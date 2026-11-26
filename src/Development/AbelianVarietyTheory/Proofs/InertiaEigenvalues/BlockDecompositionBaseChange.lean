module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsExactAdm
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltInvariantMemReductionOfFrobeniusEquation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDecompositionBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDecompositionBaseChange
namespace GlobalTheory


open Matrix in
theorem blockDecomposition_baseChange {K L : Type} [Field K] [Field L] (φ : K →+* L) {n r t : ℕ}
    (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K))) :
    ∃ e' : (Fin n → L) ≃ₗ[L] ((Fin r → L) × (Fin t → L)),
      ∀ (M : Matrix (Fin n) (Fin n) K) (P : Matrix (Fin r) (Fin r) K) (d : Fin t → K),
        (∀ u, e (M.mulVec u) = (P.mulVec (e u).1, fun c => d c * (e u).2 c)) →
        ∀ u, e' ((M.map φ).mulVec u) =
          ((P.map φ).mulVec (e' u).1, fun c => φ (d c) * (e' u).2 c) := by
  classical

  have hext : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) K), (∀ v, X *ᵥ v = Y *ᵥ v) → X = Y :=
    fun X Y h => Matrix.toLin'.injective (LinearMap.ext fun v => by
      simpa only [Matrix.toLin'_apply] using h v)

  obtain ⟨A₁, hA₁⟩ : ∃ A : Matrix (Fin r) (Fin n) K, ∀ v, A *ᵥ v = (e v).1 :=
    ⟨LinearMap.toMatrix' (LinearMap.fst K _ _ ∘ₗ e.toLinearMap), fun v => by
      rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl⟩
  obtain ⟨A₂, hA₂⟩ : ∃ A : Matrix (Fin t) (Fin n) K, ∀ v, A *ᵥ v = (e v).2 :=
    ⟨LinearMap.toMatrix' (LinearMap.snd K _ _ ∘ₗ e.toLinearMap), fun v => by
      rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl⟩
  obtain ⟨B₁, hB₁⟩ : ∃ B : Matrix (Fin n) (Fin r) K, ∀ p, B *ᵥ p = e.symm (p, 0) :=
    ⟨LinearMap.toMatrix' (e.symm.toLinearMap ∘ₗ LinearMap.inl K _ _), fun p => by
      rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl⟩
  obtain ⟨B₂, hB₂⟩ : ∃ B : Matrix (Fin n) (Fin t) K, ∀ q, B *ᵥ q = e.symm (0, q) :=
    ⟨LinearMap.toMatrix' (e.symm.toLinearMap ∘ₗ LinearMap.inr K _ _), fun q => by
      rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl⟩

  have h11 : A₁ * B₁ = 1 := hext _ _ fun p => by
    rw [← Matrix.mulVec_mulVec, hB₁, hA₁, LinearEquiv.apply_symm_apply, Matrix.one_mulVec]
  have h12 : A₁ * B₂ = 0 := hext _ _ fun q => by
    rw [← Matrix.mulVec_mulVec, hB₂, hA₁, LinearEquiv.apply_symm_apply, Matrix.zero_mulVec]
  have h21 : A₂ * B₁ = 0 := hext _ _ fun p => by
    rw [← Matrix.mulVec_mulVec, hB₁, hA₂, LinearEquiv.apply_symm_apply, Matrix.zero_mulVec]
  have h22 : A₂ * B₂ = 1 := hext _ _ fun q => by
    rw [← Matrix.mulVec_mulVec, hB₂, hA₂, LinearEquiv.apply_symm_apply, Matrix.one_mulVec]
  have hBA : B₁ * A₁ + B₂ * A₂ = 1 := hext _ _ fun u => by
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA₁, hA₂, hB₁, hB₂,
      ← map_add, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta, LinearEquiv.symm_apply_apply,
      Matrix.one_mulVec]

  have h11' : A₁.map φ * B₁.map φ = 1 := by
    rw [← Matrix.map_mul, h11, Matrix.map_one _ φ.map_zero φ.map_one]
  have h12' : A₁.map φ * B₂.map φ = 0 := by
    rw [← Matrix.map_mul, h12, Matrix.map_zero _ φ.map_zero]
  have h21' : A₂.map φ * B₁.map φ = 0 := by
    rw [← Matrix.map_mul, h21, Matrix.map_zero _ φ.map_zero]
  have h22' : A₂.map φ * B₂.map φ = 1 := by
    rw [← Matrix.map_mul, h22, Matrix.map_one _ φ.map_zero φ.map_one]
  have hBA' : B₁.map φ * A₁.map φ + B₂.map φ * A₂.map φ = 1 := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add φ φ.map_add, hBA,
      Matrix.map_one _ φ.map_zero φ.map_one]

  refine ⟨LinearEquiv.ofLinearMap ((Matrix.toLin' (A₁.map φ)).prod (Matrix.toLin' (A₂.map φ)))
    ((Matrix.toLin' (B₁.map φ)).coprod (Matrix.toLin' (B₂.map φ))) ?_ ?_, ?_⟩
  · refine LinearMap.ext fun x => ?_
    obtain ⟨p, q⟩ := x
    refine Prod.ext ?_ ?_ <;>
      simp [Matrix.mulVec_add, Matrix.mulVec_mulVec, h11', h12', h21', h22']
  · refine LinearMap.ext fun u => ?_
    have key : (B₁.map φ * A₁.map φ) *ᵥ u + (B₂.map φ * A₂.map φ) *ᵥ u = u := by
      rw [← Matrix.add_mulVec, hBA', Matrix.one_mulVec]
    simpa [Matrix.mulVec_mulVec] using key
  · intro M P d h u

    have hM₁ : A₁ * M = P * A₁ := hext _ _ fun v => by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA₁, hA₁, h v]
    have hM₂ : A₂ * M = Matrix.diagonal d * A₂ := hext _ _ fun v => by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA₂, hA₂, h v]
      funext c
      rw [Matrix.mulVec_diagonal]
    have hM₁' : A₁.map φ * M.map φ = P.map φ * A₁.map φ := by
      rw [← Matrix.map_mul, hM₁, Matrix.map_mul]
    have hM₂' : A₂.map φ * M.map φ = Matrix.diagonal (fun c => φ (d c)) * A₂.map φ := by
      rw [← Matrix.map_mul, hM₂, Matrix.map_mul, Matrix.diagonal_map φ.map_zero]
    refine Prod.ext ?_ (funext fun c => ?_)
    · change A₁.map φ *ᵥ (M.map φ *ᵥ u) = P.map φ *ᵥ (A₁.map φ *ᵥ u)
      rw [Matrix.mulVec_mulVec, hM₁', ← Matrix.mulVec_mulVec]
    · change (A₂.map φ *ᵥ (M.map φ *ᵥ u)) c = φ (d c) * (A₂.map φ *ᵥ u) c
      rw [Matrix.mulVec_mulVec, hM₂', ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDecompositionBaseChangeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_mulVec_decomposition_map_of_decomposition : ∀ {K L : Type} [Field K] [Field L] (φ : K →+* L) {n r t : ℕ} (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K))), ∃ e' : (Fin n → L) ≃ₗ[L] ((Fin r → L) × (Fin t → L)), ∀ (M : Matrix (Fin n) (Fin n) K) (P : Matrix (Fin r) (Fin r) K) (d : Fin t → K), (∀ u, e (M.mulVec u) = (P.mulVec (e u).1, fun c => d c * (e u).2 c)) → ∀ u, e' ((M.map φ).mulVec u) = ((P.map φ).mulVec (e' u).1, fun c => φ (d c) * (e' u).2 c) := by
  first | exact @GlobalTheory.blockDecomposition_baseChange | exact GlobalTheory.blockDecomposition_baseChange | (intros; apply GlobalTheory.blockDecomposition_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinApproxRootImageIndep
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem scaleRoots_derivative_eval₂_mul {W R : Type} [CommRing W] [CommRing R] (c : W →+* R) (P : Polynomial W)
    (s : W) (t : R) :
    c s * Polynomial.eval₂ c (c s * t) (Polynomial.derivative (P.scaleRoots s)) =
      c s ^ P.natDegree * Polynomial.eval₂ c t (Polynomial.derivative P) := by
  have h : (P.scaleRoots s).comp (Polynomial.C s * Polynomial.X) = Polynomial.C s ^ P.natDegree * P := by
    have h0 := Polynomial.scaleRoots_eval₂_mul (p := P) (Polynomial.C : W →+* Polynomial W) Polynomial.X s
    rw [Polynomial.eval₂_C_X] at h0
    exact h0
  have h1 := congrArg (fun r => Polynomial.eval₂ c t (Polynomial.derivative r)) h
  simp only [Polynomial.derivative_comp, ← Polynomial.C_pow, Polynomial.derivative_C_mul, Polynomial.derivative_X,
    mul_one, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_comp, Polynomial.eval₂_X] at h1
  rw [h1, map_pow]

theorem exists_mul_derivative_scaleRoots_sub_mem {W R : Type} [CommRing W] [CommRing R] (c : W →+* R) (I : Ideal R)
    (P a b : Polynomial W) (s z : W) (hab : a * P + b * Polynomial.derivative P = Polynomial.C z) (t x : R)
    (ht : Polynomial.eval₂ c t P ∈ I) (hx : x - c s * t ∈ I) :
    ∃ b' : R, b' * (Polynomial.derivative ((P.scaleRoots s).map c)).eval x - c s ^ P.natDegree * c z ∈ I := by
  refine ⟨Polynomial.eval₂ c t b * c s, ?_⟩
  obtain ⟨w, hw⟩ := Polynomial.sub_dvd_eval_sub x (c s * t) (Polynomial.derivative ((P.scaleRoots s).map c))
  have h1 := scaleRoots_derivative_eval₂_mul c P s t
  have h2 := congrArg (Polynomial.eval₂ c t) hab
  rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_C] at h2
  have h3 : (Polynomial.derivative ((P.scaleRoots s).map c)).eval (c s * t) =
      Polynomial.eval₂ c (c s * t) (Polynomial.derivative (P.scaleRoots s)) := by
    rw [Polynomial.derivative_map, Polynomial.eval_map]
  rw [h3] at hw
  have h4 : Polynomial.eval₂ c t b * c s * (Polynomial.derivative ((P.scaleRoots s).map c)).eval x -
      c s ^ P.natDegree * c z = (Polynomial.eval₂ c t b * c s * w) * (x - c s * t) -
        (c s ^ P.natDegree * Polynomial.eval₂ c t a) * Polynomial.eval₂ c t P := by
    linear_combination (Polynomial.eval₂ c t b * c s) * hw + Polynomial.eval₂ c t b * h1 +
      c s ^ P.natDegree * h2
  rw [h4]
  exact I.sub_mem (I.mul_mem_left _ hx) (I.mul_mem_left _ ht)

theorem eval₂_C_X_powerSeries {W : Type} [CommRing W] (P : Polynomial W) :
    Polynomial.eval₂ (PowerSeries.C : W →+* W⟦X⟧) X P = (P : W⟦X⟧) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval₂_add, hp, hq, Polynomial.coe_add]
  | monomial n a =>
    rw [Polynomial.eval₂_monomial, ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_pow,
      Polynomial.coe_C, Polynomial.coe_X]

theorem approxRoot_image_indep_general_rings {W R : Type} [CommRing W] [CommRing R] (l n m c : ℕ) (P a b : Polynomial W)
    (hab : a * P + b * Polynomial.derivative P = Polynomial.C ((l : W) ^ c)) (q : W⟦X⟧)
    (h1 : (P : W⟦X⟧) ∣ q - (l : W⟦X⟧) ^ m * X)
    (h2 : (P : W⟦X⟧) ^ n ∣ Polynomial.eval₂ PowerSeries.C q (P.scaleRoots ((l : W) ^ m)))
    (I : Ideal R) (f g : W⟦X⟧ →+* R) (hC : ∀ w, f (PowerSeries.C w) = g (PowerSeries.C w)) (hX : f X - g X ∈ I)
    (hI : I = Ideal.span {f P}) (hI' : I = Ideal.span {g P}) :
    ∃ k : ℕ, f P ^ n ∣ (l : R) ^ k * (f q - g q) := by
  have hfE : f P ∈ I := by rw [hI]; exact Ideal.mem_span_singleton_self _
  have hgE : g P ∈ I := by rw [hI']; exact Ideal.mem_span_singleton_self _
  have hcomp : f.comp PowerSeries.C = g.comp PowerSeries.C := RingHom.ext hC
  have hroot : ∀ h : W⟦X⟧ →+* R, h P ∈ I →
      ((P.scaleRoots ((l : W) ^ m)).map (h.comp PowerSeries.C)).eval (h q) ∈ I ^ n := by
    intro h hE
    obtain ⟨y, hy⟩ := h2
    rw [Polynomial.eval_map, ← Polynomial.hom_eval₂, hy, map_mul, map_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hE n)
  have hcong : ∀ h : W⟦X⟧ →+* R, h P ∈ I → h q - (l : R) ^ m * h X ∈ I := by
    intro h hE
    obtain ⟨y, hy⟩ := h1
    have := congrArg h hy
    rw [map_sub, map_mul, map_mul, map_pow, map_natCast] at this
    rw [this]
    exact Ideal.mul_mem_right _ _ hE
  have hxy : f q - g q ∈ I := by
    have : f q - g q = (f q - (l : R) ^ m * f X) - (g q - (l : R) ^ m * g X) + (l : R) ^ m * (f X - g X) := by ring
    rw [this]
    exact I.add_mem (I.sub_mem (hcong f hfE) (hcong g hgE)) (I.mul_mem_left _ hX)
  obtain ⟨b', hb'⟩ := exists_mul_derivative_scaleRoots_sub_mem (f.comp PowerSeries.C) I P a b
    ((l : W) ^ m) _ hab (f X) (f q)
    (by rw [← Polynomial.hom_eval₂, eval₂_C_X_powerSeries]; exact hfE)
    (by rw [map_pow, map_natCast]; exact hcong f hfE)
  have hg := hroot g hgE
  rw [← hcomp] at hg
  have key := GlobalTheory.T.pow_mul_sub_mem_pow_of_eval_mem_pow R I _ _ _ _ _ n (hroot f hfE) hg hxy hb'
  rw [hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton, map_pow, map_pow, map_natCast, ← pow_mul, ← pow_add,
    ← pow_mul] at key
  exact ⟨_, key⟩

theorem approx_root_indep : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n m : ℕ) (q : bk.S), bk.E ∣ q - (l : bk.S) ^ m * X → bk.E ^ n ∣ Polynomial.eval₂ PowerSeries.C q (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ m)) → (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, BK.hf f bk.E ^ n ∣ (l : B.A) ^ k * (BK.hf f q - BK.hf g q)) := by
  intro l _ K bk n m q h1 h2 B f g
  obtain ⟨hC, hX, hI⟩ := GlobalTheory.BSP.IdealSubMembership.main l K bk B f g
  obtain ⟨-, -, hI'⟩ := GlobalTheory.BSP.IdealSubMembership.main l K bk B g f
  obtain ⟨c, a, b, hab⟩ := GlobalTheory.T.bezout_eisenstein_derivative_prime_pow l K bk
  exact approxRoot_image_indep_general_rings l n m c bk.Ep a b hab q h1 h2 B.I (BK.hf f) (BK.hf g) hC hX hI hI'

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentRankConstOfCharpolyInLocalFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentRankConstOfCharpolyInLocalFunctions
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing Polynomial

namespace GlobalTheory.IdemConstRank

theorem charpoly_of_idem {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (h : M * M = M) :
    ∃ b : ℕ, M.charpoly = (X - 1) ^ M.rank * X ^ b := by
  classical
  have hf : IsIdempotentElem (Matrix.toLin' M) := by
    have h2 : Matrix.toLin' (M * M) = Matrix.toLin' M := by rw [h]
    rw [Matrix.toLin'_mul] at h2
    exact h2
  have hc := LinearMap.IsIdempotentElem.isCompl hf
  let e := Submodule.prodEquivOfIsCompl _ _ hc
  have key : e.conj ((1 : Module.End K (LinearMap.range (Matrix.toLin' M))).prodMap
      (0 : Module.End K (LinearMap.ker (Matrix.toLin' M)))) = Matrix.toLin' M := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.prodMap_apply, Module.End.one_apply, LinearMap.zero_apply]
    rw [Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl', map_add (f := _),
      LinearMap.mem_ker.mp y.2.2, (LinearMap.IsIdempotentElem.mem_range_iff hf).mp y.1.2]
    simp
  refine ⟨Module.finrank K (LinearMap.ker (Matrix.toLin' M)), ?_⟩
  have hcp : M.charpoly = (e.conj ((1 : Module.End K (LinearMap.range (Matrix.toLin' M))).prodMap
      (0 : Module.End K (LinearMap.ker (Matrix.toLin' M))))).charpoly := by
    rw [key, Matrix.charpoly_toLin']
  rw [hcp, LinearEquiv.charpoly_conj, LinearMap.charpoly_prodMap,
    LinearMap.charpoly_one, LinearMap.charpoly_zero, Matrix.rank, ← Matrix.toLin'_apply']

theorem residue_eq {X O : Type} [CommRing O] [IsLocalRing O] (T : Subalgebra O (X → O))
    [IsLocalRing T] (f : X → O) (hf : f ∈ T) (x y : X) :
    IsLocalRing.residue O (f x) = IsLocalRing.residue O (f y) := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  by_contra hne
  have hu : IsUnit (f x - f y) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hne
    exact hne
  have ev : ∀ z : X, ∀ t : T, IsUnit t → IsUnit ((t : X → O) z) := fun z t ht =>
    ht.map ((Pi.evalRingHom (fun _ : X => O) z).comp T.val.toRingHom)
  let g : T := ⟨f - algebraMap O (X → O) (f y), T.sub_mem hf (T.algebraMap_mem _)⟩
  let g' : T := algebraMap O T (f x - f y) - g
  have hg : g ∈ nonunits T := fun hg => by
    have := ev y g hg
    simp [g] at this
  have hg' : g' ∈ nonunits T := fun hg => by
    have := ev x g' hg
    simp [g', g] at this
  have hsum : g + g' = algebraMap O T (f x - f y) := by
    simp [g']
  exact IsLocalRing.nonunits_add hg hg' (hsum ▸ hu.map (algebraMap O T))

theorem rootMultiplicity_one {k : Type} [Field k] (a b : ℕ) :
    rootMultiplicity (1 : k) ((X - 1) ^ a * X ^ b) = a := by
  have h1 : ((Polynomial.X : k[X]) - 1) ^ a = (Polynomial.X - Polynomial.C 1) ^ a := by
    rw [map_one]
  have hne : ((Polynomial.X : k[X]) - Polynomial.C 1) ^ a * Polynomial.X ^ b ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero 1)) (pow_ne_zero _ X_ne_zero)
  rw [h1, rootMultiplicity_mul hne, rootMultiplicity_X_sub_C_pow, rootMultiplicity_eq_zero, add_zero]
  simp [IsRoot]

theorem rank_eq_rootMultiplicity {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) O) (h : M * M = M) :
    (M.map (toFr O)).rank = rootMultiplicity 1 (M.charpoly.map (IsLocalRing.residue O)) := by
  obtain ⟨b, hb⟩ := charpoly_of_idem (M.map (toFr O)) (by rw [← Matrix.map_mul, h])
  rw [Matrix.charpoly_map] at hb
  have hinj : Function.Injective (toFr O) := IsFractionRing.injective O (FractionRing O)
  have hM : M.charpoly = ((Polynomial.X : O[X]) - 1) ^ (M.map (toFr O)).rank * Polynomial.X ^ b := by
    apply Polynomial.map_injective _ hinj
    rw [hb]
    simp
  rw [hM]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_one]
  exact (rootMultiplicity_one _ _).symm

theorem rank_const : ∀ {X O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {n : ℕ} (T : Subalgebra O (X → O)) (e : X → Matrix (Fin n) (Fin n) O), IsLocalRing T → e * e = e → (∀ j : ℕ, (fun x => (e x).charpoly.coeff j) ∈ T) → ∀ x y, ((e x).map (toFr O)).rank = ((e y).map (toFr O)).rank := by
  intro X O _ _ _ n T e hT he hc x y
  have hx := rank_eq_rootMultiplicity (e x) (congrFun he x)
  have hy := rank_eq_rootMultiplicity (e y) (congrFun he y)
  have hp : (e x).charpoly.map (IsLocalRing.residue O) = (e y).charpoly.map (IsLocalRing.residue O) := by
    ext j
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    exact residue_eq T (fun z => (e z).charpoly.coeff j) (hc j) x y
  rw [hx, hy, hp]

end GlobalTheory.IdemConstRank
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentRankConstOfCharpolyInLocalFunctionsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_rank_const_of_charpoly_in_local_functions : ∀ {X O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {n : ℕ} (T : Subalgebra O (X → O)) (e : X → Matrix (Fin n) (Fin n) O), IsLocalRing T → e * e = e → (∀ j : ℕ, (fun x => (e x).charpoly.coeff j) ∈ T) → ∀ x y, ((e x).map (toFr O)).rank = ((e y).map (toFr O)).rank := by
  first | exact @GlobalTheory.IdemConstRank.rank_const | exact GlobalTheory.IdemConstRank.rank_const | (intros; apply GlobalTheory.IdemConstRank.rank_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToBcrisPhi
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToBcrisPhi
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.FrobCoord

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]

theorem frob_mem_invL_S {f : K⟦X⟧} (hf : f ∈ invL l (S O K e)) : frob K l f ∈ invL l (S O K e) :=
  frob_mem_invL l (fun _ h => frob_mem_S l h) hf

theorem iSl_frob (ϖ : PiSys l e) (f : invL l (S O K e)) :
    ϖ.iSl O K ⟨frob K l f, frob_mem_invL_S f.2⟩ = frobOB l O (ϖ.iSl O K f) := by
  let F : invL l (S O K e) →+* invL l (S O K e) :=
    (frob K l).toRingHom.restrict _ _ fun _ h => frob_mem_invL_S h
  have key : (ϖ.iSl O K).toRingHom.comp F = (frobOB l O).toRingHom.comp (ϖ.iSl O K).toRingHom := by
    have hS : ∀ (x : S O K e) (h : frob K l (x : K⟦X⟧) ∈ invL l (S O K e)) (h' : (x : K⟦X⟧) ∈ invL l (S O K e)),
        ϖ.iSl O K ⟨frob K l x, h⟩ = frobOB l O (ϖ.iSl O K ⟨x, h'⟩) := fun x h h' => by
      rw [ϖ.iSl_of_mem O K (frob_mem_S l x.2) h, ϖ.iSl_of_mem O K x.2 h', ϖ.iS_frob O K x, frobOB_toOB]
    refine IsLocalization.ringHom_ext (Submonoid.powers (l : S O K e)) ?_
    ext x
    exact hS x _ _
  exact RingHom.congr_fun key f

theorem frobOB_idem (t : Wq l a →ₐ[ℤ_[l]] O) (τ : ZMod a) :
    frobOB l O (idem (constB t) τ) = idem (constB t) (τ + 1) := by
  change frobOB l O (toOB l O (toOCr l O (idem (constA t) τ))) = toOB l O (toOCr l O (idem (constA t) (τ + 1)))
  rw [frobOB_toOB, frobOCr_toOCr, frobOA_idem]

theorem iB_frob (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : ZMod a → invL l (S O K e)) :
    ϖ.iB t K (fun τ => ⟨frob K l (g (τ - 1)), frob_mem_invL_S (g (τ - 1)).2⟩) = frobOB l O (ϖ.iB t K g) :=
  (map_glue (frobOB l O).toRingHom 1 (frobOB_idem t) fun τ => (iSl_frob ϖ (g (τ - 1))).symm).symm

theorem iB_of_A (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (F : ZMod a → A O K)
    (h : ∀ τ, (F τ : K⟦X⟧) ∈ invL l (S O K e)) :
    ϖ.iB t K (fun τ => ⟨F τ, h τ⟩) = toB l O (ϖ.iTot t K F) :=
  (ϖ.iB_of_mem t K fun τ => ⟨F τ, A_le_S l e (F τ).2⟩).trans (congrArg (toOB l O) (ϖ.iC_of_mem t K F))

theorem toBcris_phi (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O)
    (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (α : ℕ)
    (Y : Matrix ι ι (OA l O)) :
    (∀ i j, ∃ f : ZMod a → A O K, (∀ τ, (f τ : K⟦X⟧) = E K l e ^ α * P.mx τ i j) ∧ Y i j = ϖ.iTot t K f) →
      ∀ m m' : P.MMl, m'.1 = P.phi m.1 →
        toB l O (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e))) ^ α • toBcris t ϖ P m' =
          (Y.map (frobOA l O)).map (toB l O) *ᵥ fun i => frobOB l O (toBcris t ϖ P m i) := by
  intro hY m m' hm
  choose f hf hYf using hY
  set c := coordL P (invL l (S O K e)) m with hc
  set c' := coordL P (invL l (S O K e)) m' with hc'

  have step1 : ∀ i τ, frob K l (E K l e) ^ α * (c' i τ : K⟦X⟧) =
      ∑ j, (frobAc l (f i j) τ : K⟦X⟧) * frob K l (c j (τ - 1) : K⟦X⟧) := by
    intro i τ
    have h1 : (c' i τ : K⟦X⟧) = frob K l (m.1 (τ - 1) i) := by
      change (P.mxInv τ *ᵥ m'.1 τ) i = _
      rw [hm, PhiMod.phi_apply, Matrix.mulVec_mulVec, P.mxInv_mul_mx, Matrix.one_mulVec, frobV_apply]
    have h2 : m.1 (τ - 1) i = ∑ j, P.mx (τ - 1) i j * (c j (τ - 1) : K⟦X⟧) := by
      rw [← mx_mulVec_coordL P _ m (τ - 1)]
      simp only [Matrix.mulVec, dotProduct, hc]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, h2, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coe_frobAc, frobTot_apply, hf i j (τ - 1), map_mul, map_mul, map_pow, mul_assoc]

  let liftA : (ZMod a → A O K) → ZMod a → invL l (S O K e) :=
    fun F τ => ⟨F τ, le_away _ _ (A_le_S l e (F τ).2)⟩
  let cF : ι → ZMod a → invL l (S O K e) :=
    fun j τ => ⟨frob K l (c j (τ - 1)), frob_mem_invL_S (c j (τ - 1)).2⟩
  have step2 : ∀ i, liftA (frobAc l fun _ => EIn l e (A O K)) ^ α * c' i =
      ∑ j, liftA (frobAc l (f i j)) * cF j := by
    intro i
    funext τ
    apply Subtype.ext
    simp only [liftA, cF, Pi.mul_apply, Pi.pow_apply, Finset.sum_apply, Subalgebra.coe_mul, Subalgebra.coe_pow,
      AddSubmonoidClass.coe_finsetSum]
    exact step1 i τ
  ext i
  have h3 := congrArg (ϖ.iB t K) (step2 i)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, map_pow, map_sum] at h3
  simp only [Finset.sum_congr rfl fun j _ => map_mul (ϖ.iB t K) (liftA (frobAc l (f i j))) (cF j)] at h3
  simp only [liftA, iB_of_A, cF, iB_frob, ϖ.iTot_frob t K, ϖ.iTot_E t K] at h3
  rw [Pi.smul_apply, smul_eq_mul, toBcris_apply, ← hc', h3]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hYf, toBcris_apply, ← hc]

end GlobalTheory.BKGal.FrobCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToBcrisPhiStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toBcris_phi_alt : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (α : ℕ) (Y : Matrix ι ι (OA l O)), (∀ i j, ∃ f : ZMod a → A O K, (∀ τ, (f τ : K⟦X⟧) = E K l e ^ α * P.mx τ i j) ∧ Y i j = ϖ.iTot t K f) → ∀ m m' : P.MMl, m'.1 = P.phi m.1 → toB l O (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e))) ^ α • toBcris t ϖ P m' = (Y.map (frobOA l O)).map (toB l O) *ᵥ fun i => frobOB l O (toBcris t ϖ P m i) := by
  first | exact @GlobalTheory.BKGal.FrobCoord.toBcris_phi | exact GlobalTheory.BKGal.FrobCoord.toBcris_phi | (intros; apply GlobalTheory.BKGal.FrobCoord.toBcris_phi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LadicDescentStepToOE
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LadicDescentStepToOE
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DescentStep

variable {l : ℕ} [Fact l.Prime]

theorem perfectRing_Cb : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ _ fun x => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  obtain ⟨a, rfl⟩ := (bijective_frobenius (OCb l) l).2 a
  obtain ⟨b, rfl⟩ := (bijective_frobenius (OCb l) l).2 b
  exact ⟨algebraMap _ _ a / algebraMap _ _ b, by simp [frobenius_def]⟩

theorem constantCoeff_frobW (w : WCb l) :
    WittVector.constantCoeff (p := l) (R := Cb l) (frobW l w) =
      WittVector.constantCoeff (p := l) (R := Cb l) w ^ l := by
  rw [WittVector.constantCoeff_apply, WittVector.constantCoeff_apply]
  change (WittVector.map (frobenius (Cb l) l) w).coeff 0 = _
  rw [WittVector.map_coeff, frobenius_def]

theorem constantCoeff_galW (g : GQ l) (w : WCb l) :
    WittVector.constantCoeff (p := l) (R := Cb l) (galW l g w) =
      autCb l (galTilt l g) (WittVector.constantCoeff (p := l) (R := Cb l) w) := by
  rw [WittVector.constantCoeff_apply, WittVector.constantCoeff_apply]
  change (WittVector.map (autCb l (galTilt l g)).toRingHom w).coeff 0 = _
  rw [WittVector.map_coeff]
  rfl

end GlobalTheory.BSP.DescentStep


open GlobalTheory.BSP.DescentStep in
theorem GlobalTheory.BSP.BK.descent_step : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (κ : Type) [Fintype κ] (x b : κ → WCb l) (c : κ → κ → WCb l), (∀ i j, c i j ∈ bk.OE) → (∀ j, b j ∈ bk.OE) → (∀ j, x j = ∑ i, frobW l (x i) * c i j + b j) → (∀ g : ↥(GK K), bk.FixFlat g → ∀ j, galW l (g : GQ l) (x j) = x j) → ∃ v x' b' : κ → WCb l, (∀ j, v j ∈ bk.OE) ∧ (∀ j, b' j ∈ bk.OE) ∧ (∀ j, x j = v j + ((l : ℕ) : WCb l) * x' j) ∧ (∀ j, x' j = ∑ i, frobW l (x' i) * c i j + b' j) ∧ ∀ g : ↥(GK K), bk.FixFlat g → ∀ j, galW l (g : GQ l) (x' j) = x' j := by
  intro l _ K bk κ _ x b c hc hb hx hg
  haveI : PerfectRing (Cb l) l := perfectRing_Cb
  obtain ⟨sat, -, hφ, hfix, -⟩ := GlobalTheory.T.breuilKisin_OE_stability_properties l K bk
  set cc := WittVector.constantCoeff (p := l) (R := Cb l) with hcc
  have hmemc : ∀ w ∈ bk.OE, cc w ∈ bk.OE.map cc := fun w hw => Subring.mem_map.2 ⟨w, hw, rfl⟩
  have key : ∀ j, cc (x j) ∈ bk.OE.map cc := by
    refine GlobalTheory.T.tilt_invariant_mem_reduction_of_frobenius_equation l K bk κ (fun j => cc (x j)) ?_ ?_
    · intro g hgf j
      have h1 := congrArg cc (hg g hgf j)
      rw [constantCoeff_galW] at h1
      exact h1
    · intro T _ i₁ i₂ h12
      refine ⟨fun i j => i₁ (cc (c i j)), fun j => ?_⟩
      have e1 : ∀ i' : Cb l →+* T,
          i' (cc (x j)) = ∑ i, i' (cc (x i)) ^ l * i' (cc (c i j)) + i' (cc (b j)) := by
        intro i'
        conv_lhs => rw [hx j]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [RingHom.map_add cc, map_sum cc, RingHom.map_add i', map_sum i']
        refine congrArg (· + _) (Finset.sum_congr rfl fun i _ => ?_)
        rw [RingHom.map_mul cc, RingHom.map_mul i', constantCoeff_frobW, RingHom.map_pow i']
      have e2 : ∀ i, i₂ (cc (c i j)) = i₁ (cc (c i j)) := fun i => (h12 _ (hmemc _ (hc i j))).symm
      rw [e1 i₁, e1 i₂, ← h12 _ (hmemc _ (hb j))]
      simp_rw [e2]
      rcases subsingleton_or_nontrivial T with hT | hT
      · exact Subsingleton.elim _ _
      · haveI : CharP T l := charP_of_injective_ringHom i₁.injective l
        simp_rw [sub_pow_char, sub_mul, Finset.sum_sub_distrib]
        ring
  choose v hv hvx using fun j => Subring.mem_map.1 (key j)
  have hker : ∀ j, x j - v j ∈ RingHom.ker cc := fun j => by
    rw [RingHom.mem_ker, map_sub, hvx j, sub_self]
  rw [hcc, WittVector.ker_constantCoeff] at hker
  choose x' hx' using fun j => Ideal.mem_span_singleton'.1 (hker j)

  set b' : κ → WCb l := fun j => x' j - ∑ i, frobW l (x' i) * c i j with hb'
  have hlb : ∀ j, ((l : ℕ) : WCb l) * b' j = b j - v j + ∑ i, frobW l (v i) * c i j := by
    intro j
    have h3 : ∀ i, ((l : ℕ) : WCb l) * (frobW l (x' i) * c i j) = (frobW l (x i) - frobW l (v i)) * c i j := by
      intro i
      rw [← map_sub, ← hx' i, map_mul, map_natCast]
      ring
    simp only [hb', mul_sub, Finset.mul_sum, h3]
    rw [mul_comm, hx' j]
    conv_lhs => rw [hx j]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have hb'mem : ∀ j, b' j ∈ bk.OE := fun j => sat _ (by
    rw [hlb j]
    refine bk.OE.add_mem (bk.OE.sub_mem (hb j) (hv j)) (bk.OE.sum_mem fun i _ => bk.OE.mul_mem (hφ _ (hv i)) (hc i j)))
  refine ⟨v, x', b', hv, hb'mem, fun j => ?_, fun j => ?_, fun g hgf j => ?_⟩
  · linear_combination (hx' j).symm
  · simp only [hb']
    ring
  · have h5 : galW l (g : GQ l) (x' j * ((l : ℕ) : WCb l)) = x' j * ((l : ℕ) : WCb l) := by
      rw [hx' j, map_sub, hg g hgf j, hfix g hgf _ (hv j)]
    rw [map_mul, map_natCast] at h5
    have h4 : (galW l (g : GQ l) (x' j) - x' j) * ((l : ℕ) : WCb l) = 0 := by
      linear_combination h5
    exact sub_eq_zero.1 (WittVector.eq_zero_of_p_mul_eq_zero _ h4)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LadicDescentStepToOEStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ladic_descent_step_to_OE : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (κ : Type) [Fintype κ] (x b : κ → WCb l) (c : κ → κ → WCb l), (∀ i j, c i j ∈ bk.OE) → (∀ j, b j ∈ bk.OE) → (∀ j, x j = ∑ i, frobW l (x i) * c i j + b j) → (∀ g : ↥(GK K), bk.FixFlat g → ∀ j, galW l (g : GQ l) (x j) = x j) → ∃ v x' b' : κ → WCb l, (∀ j, v j ∈ bk.OE) ∧ (∀ j, b' j ∈ bk.OE) ∧ (∀ j, x j = v j + ((l : ℕ) : WCb l) * x' j) ∧ (∀ j, x' j = ∑ i, frobW l (x' i) * c i j + b' j) ∧ ∀ g : ↥(GK K), bk.FixFlat g → ∀ j, galW l (g : GQ l) (x' j) = x' j := by
  first | exact @GlobalTheory.BSP.BK.descent_step | exact GlobalTheory.BSP.BK.descent_step | (intros; apply GlobalTheory.BSP.BK.descent_step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvAtTypePrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvAtTypePrimes
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.NoLocalInvariants

section General

variable {R : Type} [CommRing R] [IsDomain R] {n : Type} [Fintype n] [DecidableEq n]

theorem eq_zero_of_fixed {M : Matrix n n R} (h : (M - 1).det ≠ 0)
    {x : n → FractionRing R} (hx : (M.map (algebraMap R (FractionRing R))).mulVec x = x) : x = 0 := by
  have h1 : ((M - 1).map (algebraMap R (FractionRing R))).mulVec x = 0 := by
    have e : (M - 1).map (algebraMap R (FractionRing R)) =
        M.map (algebraMap R (FractionRing R)) - 1 := by
      ext a b
      simp [Matrix.sub_apply, Matrix.one_apply, apply_ite (algebraMap R (FractionRing R))]
    rw [e, Matrix.sub_mulVec, hx, Matrix.one_mulVec, sub_self]
  have h2 : ((M - 1).map (algebraMap R (FractionRing R))).det ≠ 0 := by
    have e : ((M - 1).map (algebraMap R (FractionRing R))).det =
        algebraMap R (FractionRing R) (M - 1).det := by
      simpa using ((algebraMap R (FractionRing R)).map_det (M - 1)).symm
    rw [e]
    exact fun h0 => h ((IsFractionRing.injective R (FractionRing R)) (by simpa using h0))
  exact Matrix.eq_zero_of_mulVec_eq_zero h2 h1

theorem det_inv_transpose_sub_one_ne_zero {M : Matrix n n R} (hu : IsUnit M.det)
    (h : (M - 1).det ≠ 0) : ((M⁻¹).transpose - 1).det ≠ 0 := by
  have e : (M⁻¹).transpose - 1 = (M⁻¹ - 1).transpose := by simp
  rw [e, Matrix.det_transpose]
  intro h0
  have h1 : (M⁻¹ - 1) * M = -(M - 1) := by
    rw [sub_mul, Matrix.nonsing_inv_mul _ hu, one_mul]
    abel
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_neg] at h2
  have h3 : ((-1 : R) ^ Fintype.card n) ≠ 0 := pow_ne_zero _ (by simp)
  exact h (by simpa [h3] using h2.symm)


omit [IsDomain R] in
theorem det_scaled_sub_one_ne_zero [IsLocalRing R] (P : Matrix n n R) (c : Rˣ)
    (h : (P.map (IsLocalRing.residue R) - (IsLocalRing.residue R (c : R)) • (1 : Matrix n n _)).det ≠ 0) :
    ((((c⁻¹ : Rˣ) : R) • P) - 1).det ≠ 0 := by
  intro h0
  have e1 : P - (c : R) • (1 : Matrix n n R) = (c : R) • ((((c⁻¹ : Rˣ) : R) • P) - 1) := by
    rw [smul_sub, smul_smul, Units.mul_inv, one_smul]
  have e2 : (P - (c : R) • (1 : Matrix n n R)).det = 0 := by
    rw [e1, Matrix.det_smul, h0, mul_zero]
  apply h
  have e3 : P.map (IsLocalRing.residue R) - (IsLocalRing.residue R (c : R)) • (1 : Matrix n n _) =
      (P - (c : R) • (1 : Matrix n n R)).map (IsLocalRing.residue R) := by
    ext a b
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, apply_ite (IsLocalRing.residue R)]
  rw [e3]
  have := (IsLocalRing.residue R).map_det (P - (c : R) • (1 : Matrix n n R))
  rw [e2, map_zero] at this
  simpa using this.symm

end General

theorem noInv_of_adm2At : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), ValuationStabilityAtRing D.ntw i s → ∀ k, D.host.g k ≠ D.ntw.l i → ∀ v ∈ placesOver D.host.E (D.host.g k), NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v := by
  intro D i s h k hk v hv
  have hvl : v ∉ placesOver D.host.E (D.ntw.l i) := by
    intro hl
    have hlp : (D.ntw.l i).Prime := Fact.out
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2
      ((Nat.coprime_primes (D.host.g_prime k) hlp).2 hk)
    have h1 : (1 : 𝓞 D.host.E) ∈ v.asIdeal := by
      have e : (1 : 𝓞 D.host.E) = (a : 𝓞 D.host.E) * ((D.host.g k : ℕ) : 𝓞 D.host.E) +
          (b : 𝓞 D.host.E) * ((D.ntw.l i : ℕ) : 𝓞 D.host.E) := by
        have h2 := congrArg (Int.cast : ℤ → 𝓞 D.host.E) hab
        push_cast at h2
        exact h2.symm
      rw [e]
      exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hv) (v.asIdeal.mul_mem_left _ hl)
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have key : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) A v →
      ∃ σ ∈ Ine (F := D.host.E) A, (Tmat i s σ - 1).det ≠ 0 := by
    intro A hA
    obtain ⟨-, σ, hσ, hdet⟩ := h.2 k hk v hv A hA
    exact ⟨σ, hσ, det_scaled_sub_one_ne_zero _ _ hdet⟩
  constructor
  · intro A hA x hx
    obtain ⟨σ, hσ, hd⟩ := key A hA
    exact eq_zero_of_fixed hd (hx σ (Ine_le_Dec A hσ))
  · intro A hA x hx
    obtain ⟨σ, hσ, hd⟩ := key A hA
    have he := (GlobalTheory.TripleGal.eps0_unram_frob D i v hvl A hA).1 σ hσ
    have hu : IsUnit (Tmat i s σ).det := by
      rw [← Tgl_coe]
      exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
    have hT : Tdual i s σ = ((Tmat i s σ)⁻¹).transpose := by
      simp [Tdual, he]
    have := hx σ (Ine_le_Dec A hσ)
    rw [hT] at this
    exact eq_zero_of_fixed (det_inv_transpose_sub_one_ne_zero hu hd) this

end GlobalTheory.NoLocalInvariants
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvAtTypePrimesStatement
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noInv_at_type_primes : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), ValuationStabilityAtRing D.ntw i s → ∀ k, D.host.g k ≠ D.ntw.l i → ∀ v ∈ placesOver D.host.E (D.host.g k), NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v := by
  first | exact @GlobalTheory.NoLocalInvariants.noInv_of_adm2At | exact GlobalTheory.NoLocalInvariants.noInv_of_adm2At | (intros; apply GlobalTheory.NoLocalInvariants.noInv_of_adm2At <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCyclic
noncomputable section
namespace GlobalTheory.TameInertiaCyclic
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc GlobalTheory.MemLoc.FrobLaws

variable {l : ℕ} [hl : Fact l.Prime]

theorem exists_pow_norm (K : FinExt l) :
    ∃ d : ℕ, 0 < d ∧ ∀ x ∈ K.1, x ≠ 0 → ∃ a : ℤ, ‖x‖ ^ d = (l : ℝ) ^ a := by
  haveI := K.2
  refine ⟨Module.finrank ℚ_[l] ↥K.1, Module.finrank_pos, fun x hxK hx => ?_⟩
  have e := spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[l] (PadicAlgCl l) x
  rw [PadicAlgCl.spectralNorm_eq] at e
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : (minpoly ℚ_[l] x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hi hx
  have hn := minpoly.natDegree_pos hi
  have hd : (minpoly ℚ_[l] x).natDegree ∣ Module.finrank ℚ_[l] ↥K.1 := by
    have := minpoly.degree_dvd (K := ℚ_[l]) (x := (⟨x, hxK⟩ : ↥K.1)) (Algebra.IsIntegral.isIntegral _)
    rwa [IntermediateField.minpoly_eq] at this
  obtain ⟨c, hc⟩ := hd
  refine ⟨-((minpoly ℚ_[l] x).coeff 0).valuation * c, ?_⟩
  rw [hc, pow_mul, e, one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) hn.ne',
    Padic.norm_eq_zpow_neg_valuation h0, zpow_mul, zpow_natCast]

theorem exists_gen (K : FinExt l) :
    ∃ π ∈ K.1, π ≠ 0 ∧ ∀ x ∈ K.1, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π ^ k‖ := by
  obtain ⟨d, hd, H⟩ := exists_pow_norm K
  have hl0 : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  let S : AddSubgroup ℤ :=
    { carrier := {n | ∃ x ∈ K.1, x ≠ 0 ∧ ‖x‖ ^ d = (l : ℝ) ^ n}
      add_mem' := by
        rintro a b ⟨x, hx, hx0, ex⟩ ⟨y, hy, hy0, ey⟩
        exact ⟨x * y, mul_mem hx hy, mul_ne_zero hx0 hy0, by
          rw [norm_mul, mul_pow, ex, ey, zpow_add₀ hl0]⟩
      zero_mem' := ⟨1, one_mem _, one_ne_zero, by simp⟩
      neg_mem' := by
        rintro a ⟨x, hx, hx0, ex⟩
        exact ⟨x⁻¹, inv_mem hx, inv_ne_zero hx0, by rw [norm_inv, inv_pow, ex, zpow_neg]⟩ }
  haveI : IsAddCyclic S := AddSubgroup.isAddCyclic S
  obtain ⟨f, hf⟩ := IsAddCyclic.exists_zsmul_surjective (G := S)
  have hfS : (f : ℤ) ∈ S := f.property
  obtain ⟨π, hπ, hπ0, eπ⟩ := hfS
  refine ⟨π, hπ, hπ0, fun x hx hx0 => ?_⟩
  obtain ⟨a, ha⟩ := H x hx hx0
  have haS : a ∈ S := ⟨x, hx, hx0, ha⟩
  obtain ⟨k, hk⟩ := hf ⟨a, haS⟩
  have hk' : k • (f : ℤ) = a := congrArg Subtype.val hk
  subst a
  refine ⟨k, (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hd.ne').1 ?_⟩
  rw [ha, norm_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, eπ, ← zpow_mul,
    smul_eq_mul, mul_comm]

theorem fix_of_near (K : FinExt l) (g : GQ l) (hst : ∀ x ∈ K.1, g x ∈ K.1)
    (hnear : ∀ x ∈ K.1, x ≠ 0 → ‖g x - x‖ < ‖x‖) {N : ℕ} (hN : ¬ l ∣ N)
    (hgN : ∀ x ∈ K.1, (g ^ N) x = x) (y : Om l) (hy : y ∈ K.1) : g y = y := by
  by_contra hne
  have hx0 : g y - y ≠ 0 := sub_ne_zero.2 hne
  have hxK : g y - y ∈ K.1 := sub_mem (hst y hy) hy
  set x := g y - y with hx
  have h1 : ∀ i : ℕ, ‖(g ^ i) x - x‖ < ‖x‖ := by
    intro i
    induction i with
    | zero => simpa using hx0
    | succ i ih =>
      have e : (g ^ (i + 1)) x - x = (g ^ i) (g x - x) + ((g ^ i) x - x) := by
        rw [pow_succ, AlgEquiv.mul_apply, map_sub (g ^ i)]; ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ih)
      rw [norm_gal]; exact hnear x hxK hx0
  have h2 : ∀ k : ℕ, ‖((g ^ k) y - y) - (k : Om l) * x‖ < ‖x‖ := by
    intro k
    induction k with
    | zero => simpa using hx0
    | succ k ih =>
      have e : ((g ^ (k + 1)) y - y) - ((k + 1 : ℕ) : Om l) * x =
          (((g ^ k) y - y) - (k : Om l) * x) + ((g ^ k) x - x) := by
        rw [pow_succ, AlgEquiv.mul_apply, hx, map_sub]; push_cast; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih (h1 k))
  have hmn : ‖(N : Om l)‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
    exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hN)
  have := h2 N
  rw [hgN y hy, sub_self, zero_sub, norm_neg, norm_mul, hmn, one_mul] at this
  exact lt_irrefl _ this

def ratio (g : GQ l) (x : Om l) : OO l :=
  ⟨g x / x, by
    show ‖g x / x‖ ≤ 1
    rw [norm_div, norm_gal]; exact div_self_le_one _⟩

theorem ratio_mul (g : GQ l) (x y : Om l) : ratio g (x * y) = ratio g x * ratio g y :=
  Subtype.ext (by
    show g (x * y) / (x * y) = g x / x * (g y / y)
    rw [map_mul, mul_div_mul_comm])

theorem res_ratio_iff (g : GQ l) {x : Om l} (hx : x ≠ 0) :
    res (ratio g x) = 1 ↔ ‖g x - x‖ < ‖x‖ := by
  rw [← map_one (res (l := l)), res_eq_iff]
  show ‖g x / x - 1‖ < 1 ↔ _
  have : g x / x - 1 = (g x - x) / x := by field_simp
  rw [this, norm_div, div_lt_one (norm_pos_iff.2 hx)]

theorem res_ratio_zpow (g : GQ l) {x : Om l} (hx : x ≠ 0) (h : res (ratio g x) = 1) (k : ℤ) :
    res (ratio g (x ^ k)) = 1 := by
  induction k using Int.induction_on with
  | zero => rw [res_ratio_iff g (by simp)]; simp
  | succ k ih => rw [zpow_add_one₀ hx, ratio_mul, map_mul, ih, h, one_mul]
  | pred k ih =>
    have e : x ^ (-(k : ℤ)) = x ^ (-(k : ℤ) - 1) * x := by
      rw [← zpow_add_one₀ hx, sub_add_cancel]
    rwa [e, ratio_mul, map_mul, h, mul_one] at ih

theorem map_mem_Kur (g : GQ l) {c : Om l} (hc : c ∈ MaximalUnramifiedExtension l) : g c ∈ MaximalUnramifiedExtension l := by
  unfold MaximalUnramifiedExtension at hc
  induction hc using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, hm, hlm, hx⟩ := hx
    exact IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, by rw [← map_pow, hx, map_one]⟩
  | algebraMap x => rw [g.commutes]; exact (MaximalUnramifiedExtension l).algebraMap_mem x
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact (MaximalUnramifiedExtension l).add_mem hx hy
  | inv x _ hx => rw [map_inv₀]; exact (MaximalUnramifiedExtension l).inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact (MaximalUnramifiedExtension l).mul_mem hx hy

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

end GlobalTheory.TameInertiaCyclic
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfResidueSpanEqTop
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSmulTopOfEntries
namespace GlobalTheory.SpanOfResidue

theorem mem_smul_top_of_entries {A : Type} [CommRing A] {r : ℕ} (I : Ideal A)
    (d : Matrix (Fin r) (Fin r) A) (hd : ∀ i j, d i j ∈ I) :
    d ∈ I • (⊤ : Submodule A (Matrix (Fin r) (Fin r) A)) := by
  rw [Matrix.matrix_eq_sum_single d]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have h : Matrix.single i j (d i j) = d i j • Matrix.single i j (1 : A) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [h]
  exact Submodule.smul_mem_smul (hd i j) Submodule.mem_top

theorem span_eq_top_of_residue {ι A : Type} [CommRing A] [IsLocalRing A] {r : ℕ}
    (f : ι → Matrix (Fin r) (Fin r) A)
    (h : Submodule.span (IsLocalRing.ResidueField A)
      (Set.range fun (i : ι) ↦ Matrix.map (f i)
        (⇑(IsLocalRing.residue A) : A → IsLocalRing.ResidueField A)) = ⊤) :
    Submodule.span A (Set.range f) = ⊤ := by
  have key : ∀ y ∈ Submodule.span (IsLocalRing.ResidueField A)
      (Set.range fun (i : ι) ↦ Matrix.map (f i)
        (⇑(IsLocalRing.residue A) : A → IsLocalRing.ResidueField A)),
      ∃ n ∈ Submodule.span A (Set.range f),
        Matrix.map n (⇑(IsLocalRing.residue A) : A → IsLocalRing.ResidueField A) = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨f i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
    | zero =>
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      ext i j
      simp
    | add x y _ _ hx hy =>
      obtain ⟨n, hn, rfl⟩ := hx
      obtain ⟨m, hm, rfl⟩ := hy
      refine ⟨n + m, Submodule.add_mem _ hn hm, ?_⟩
      ext i j
      simp
    | smul c x _ hx =>
      obtain ⟨n, hn, rfl⟩ := hx
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
      refine ⟨a • n, Submodule.smul_mem _ a hn, ?_⟩
      ext i j
      simp
  rw [eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal A)
    Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) ?_
  intro x _
  obtain ⟨n, hn, hnx⟩ := key (Matrix.map x (IsLocalRing.residue A)) (h ▸ Submodule.mem_top)
  have hx : x = n + (x - n) := by abel
  rw [hx]
  refine Submodule.add_mem_sup hn (mem_smul_top_of_entries _ _ fun i j => ?_)
  rw [← IsLocalRing.residue_eq_zero_iff, Matrix.sub_apply, map_sub, sub_eq_zero]
  exact (congrFun (congrFun hnx i) j).symm

end GlobalTheory.SpanOfResidue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfResidueSpanEqTop
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory

theorem span_matrix_eq_top_of_residue_span {ι A : Type} [CommRing A] [IsLocalRing A] {r : ℕ}
    (f : ι → Matrix (Fin r) (Fin r) A)
    (h : Submodule.span (IsLocalRing.ResidueField A)
      (Set.range (fun i => (f i).map (IsLocalRing.residue A))) = ⊤) :
    Submodule.span A (Set.range f) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue
  | exact _root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue
  | (apply _root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue ..)

theorem span_mat_eq_top_of_residue {Γ A : Type} [Group Γ] [CommRing A] [IsLocalRing A] {r : ℕ}
    (ρ : Γ →* GL (Fin r) A)
    (h : Submodule.span (IsLocalRing.ResidueField A)
      (Set.range (mat (mapRep (IsLocalRing.residue A) ρ))) = ⊤) :
    Submodule.span A (Set.range (mat ρ)) = ⊤ :=
  span_matrix_eq_top_of_residue_span (mat ρ) h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfResidueSpanEqTopStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_repMatrix_eq_top_of_residue_span_eq_top : ∀ {Γ A : Type} [Group Γ] [CommRing A] [IsLocalRing A] {r : ℕ} (ρ : Γ →* GL (Fin r) A), Submodule.span (IsLocalRing.ResidueField A) (Set.range (mat (mapRep (IsLocalRing.residue A) ρ))) = ⊤ → Submodule.span A (Set.range (mat ρ)) = ⊤ := by
  first | exact @GlobalTheory.span_mat_eq_top_of_residue | exact GlobalTheory.span_mat_eq_top_of_residue | (intros; apply GlobalTheory.span_mat_eq_top_of_residue <;> assumption)
end
end
