module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleSelfAdjointPartTensorBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleSelfAdjointPartTensorBijective
open GlobalTheory.RegSS GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem productMap_bijective_of_involution {F E L : Type} [Field F] [CharZero F] [CommRing E]
    [Algebra F E] [CommRing L] [Algebra F L] (f : E →ₐ[F] L) (τ : L ≃ₐ[F] L)
    (hτ : ∀ l, τ (τ l) = l) (P : Subalgebra F L) (hP : ∀ l, l ∈ P ↔ τ l = l)
    (b : Module.Basis (Fin 2) F E) (d : F) (h0 : b 0 = 1) (h1 : τ (f (b 1)) = - f (b 1))
    (hd : d ≠ 0) (hsq : b 1 * b 1 = algebraMap F E d) :
    Function.Bijective (Algebra.TensorProduct.productMap P.val f) := by
  have hδ : f (b 1) * f (b 1) = algebraMap F L d := by rw [← map_mul, hsq, AlgHom.commutes]
  have hinv : algebraMap F L d⁻¹ * (f (b 1) * f (b 1)) = 1 := by
    rw [hδ, ← map_mul, inv_mul_cancel₀ hd, map_one]
  have h2 : algebraMap F L 2⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap F L) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  have hval : ∀ a c : P, Algebra.TensorProduct.productMap P.val f (a ⊗ₜ[F] 1 + c ⊗ₜ[F] b 1) =
      (a : L) + (c : L) * f (b 1) := fun a c => by
    simp [Algebra.TensorProduct.productMap_apply_tmul]
  constructor
  · have hrep : ∀ x : P ⊗[F] E, ∃ a c : P, x = a ⊗ₜ[F] 1 + c ⊗ₜ[F] b 1 := by
      intro x
      induction x with
      | tmul p e =>
        refine ⟨b.repr e 0 • p, b.repr e 1 • p, ?_⟩
        conv_lhs => rw [← b.sum_repr e, Fin.sum_univ_two, h0]
        rw [TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.smul_tmul]
      | add x y hx hy =>
        obtain ⟨a, c, rfl⟩ := hx
        obtain ⟨a', c', rfl⟩ := hy
        exact ⟨a + a', c + c', by rw [TensorProduct.add_tmul, TensorProduct.add_tmul]; abel⟩
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, c, rfl⟩ := hrep x
    rw [hval] at hx
    have hx' := congrArg τ hx
    rw [map_add (f := _), map_mul, map_zero, (hP _).1 a.2, (hP _).1 c.2, h1] at hx'
    have ha : (a : L) = 0 := by
      linear_combination (algebraMap F L 2⁻¹) * (hx + hx') - (a : L) * h2
    have hc : (c : L) = 0 := by
      linear_combination (algebraMap F L d⁻¹ * f (b 1)) * (hx - ha) - (c : L) * hinv
    rw [show a = 0 from Subtype.ext ha, show c = 0 from Subtype.ext hc]
    simp
  · intro l
    refine ⟨(⟨algebraMap F L 2⁻¹ * (l + τ l), (hP _).2 ?_⟩ : P) ⊗ₜ[F] 1 +
      (⟨algebraMap F L 2⁻¹ * algebraMap F L d⁻¹ * f (b 1) * (l - τ l), (hP _).2 ?_⟩ : P) ⊗ₜ[F] b 1,
      ?_⟩
    · rw [map_mul, map_add (f := _), hτ, AlgEquiv.commutes, add_comm]
    · rw [map_mul, map_mul, map_mul, map_sub, hτ, AlgEquiv.commutes, AlgEquiv.commutes, h1]
      ring
    · rw [hval]
      dsimp only
      linear_combination l * h2 + algebraMap F L 2⁻¹ * (l - τ l) * hinv

theorem plusTensorBijective : PlusTensorBijective := by
  intro F E _ _ _ _ n _ _ σ J γ h hA
  obtain ⟨τ, -, hτ, hE, hP⟩ := exists_adjEquiv h hA
  obtain ⟨b, d, h0, h1, hd, hsq⟩ := quad_exists_basis h.quad
  refine productMap_bijective_of_involution _ τ hτ _ hP b d h0 ?_ hd hsq
  rw [IsScalarTower.toAlgHom_apply, hE, h1, map_neg]

end GlobalTheory.RegSS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleSelfAdjointPartTensorBijectiveStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularSemisimple_selfAdjointPart_tensor_bijective : GlobalTheory.RegSS.PlusTensorBijective := by
  first | exact @GlobalTheory.RegSS.plusTensorBijective | exact GlobalTheory.RegSS.plusTensorBijective | (intros; apply GlobalTheory.RegSS.plusTensorBijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EtaleTensorQuadraticSplitAlgClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EtaleTensorQuadraticSplitAlgClosed
noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem splitClosed_etale (F P Ω n : Type) [Field F] [CommRing P] [Algebra F P] [Fintype n]
    [Algebra.Etale F P] [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]
    (h : Module.finrank F P = Fintype.card n) :
    Nonempty (Ω ⊗[F] P ≃ₐ[Ω] (n → Ω)) := by
  classical
  haveI : Module.Finite F P := Algebra.FormallyUnramified.finite_of_free F P
  haveI : IsArtinianRing (Ω ⊗[F] P) := isArtinian_of_tower Ω inferInstance
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed Ω (Ω ⊗[F] P)
  letI : Fintype (PrimeSpectrum (Ω ⊗[F] P)) := Fintype.ofFinite _
  have hc : Fintype.card (PrimeSpectrum (Ω ⊗[F] P)) = Fintype.card n := by
    have := e.toLinearEquiv.finrank_eq
    rw [Module.finrank_baseChange, h, Module.finrank_fintype_fun_eq_card] at this
    exact this.symm
  exact ⟨e.trans (AlgEquiv.piCongrLeft' Ω (fun _ => Ω) (Fintype.equivOfCardEq hc))⟩

theorem splitClosed_quad {F E : Type} [Field F] [CharZero F] [CommRing E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsQuadInvol F E σ) (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] :
    ∃ φ : E ⊗[F] Ω ≃ₐ[F] Ω × Ω, (∀ ω : Ω, φ (1 ⊗ₜ ω) = (ω, ω)) ∧
      ∀ u, φ (Algebra.TensorProduct.map σ (AlgHom.id F Ω) u) = (φ u).swap := by
  haveI := h.etale
  haveI := quad_finite h
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨e⟩ := splitClosed_etale F E Ω (Fin 2) (by simp [h.finrank_eq])
  let θ : E →ₐ[F] Ω := (((Pi.evalAlgHom Ω (fun _ : Fin 2 => Ω) 0).comp e.toAlgHom).restrictScalars F).comp
    Algebra.TensorProduct.includeRight
  obtain ⟨b, d, -, hb1, hd, hbb⟩ := quad_exists_basis h
  have hc : θ (b 1) ≠ 0 := by
    intro h0
    have := congrArg θ hbb
    rw [map_mul, h0, mul_zero, AlgHom.commutes] at this
    exact hd ((map_eq_zero _).1 this.symm)
  let f : Ω ⊗[F] E →ₐ[Ω] Ω × Ω :=
    Algebra.TensorProduct.lift (Algebra.ofId Ω (Ω × Ω)) (θ.prod (θ.comp σ)) (fun _ _ => Commute.all _ _)
  have hf : ∀ ω x, f (ω ⊗ₜ x) = (ω * θ x, ω * θ (σ x)) := by
    intro ω x; simp [f, Algebra.ofId_apply]
  have hs : Function.Surjective f := by
    rintro ⟨x, y⟩
    refine ⟨((x + y) / 2) ⊗ₜ 1 + ((x - y) / (2 * θ (b 1))) ⊗ₜ b 1, ?_⟩
    rw [map_add (f := _), hf, hf, hb1, map_neg, map_one, map_one]
    ext <;> simp <;> field_simp <;> ring
  have hi : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap)
      (by simp [h.finrank_eq])).2 hs
  refine ⟨(Algebra.TensorProduct.comm F E Ω).trans
    ((AlgEquiv.ofBijective f ⟨hi, hs⟩).restrictScalars F), fun ω => (hf ω 1).trans (by simp), fun u => ?_⟩
  induction u with
  | tmul a w =>
    change f (w ⊗ₜ σ a) = (f (w ⊗ₜ a)).swap
    rw [hf, hf, h.invol]; rfl
  | add a w ha hw => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hw, Prod.swap_add]

def splitClosedPair (F Ω n : Type) [Field F] [Field Ω] [Algebra F Ω] :
    ((n → Ω) × (n → Ω)) ≃ₐ[F] (n → Ω × Ω) where
  toFun x i := (x.1 i, x.2 i)
  invFun y := (fun i => (y i).1, fun i => (y i).2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem splitClosed : SplitClosed := by
  intro F E _ _ _ _ σ h P _ _ n _ hP ⟨b⟩ Ω _ _ _
  obtain ⟨e⟩ := splitClosed_etale F P Ω n (Module.finrank_eq_card_basis b)
  obtain ⟨g, hg1, hg⟩ := splitClosed_quad h Ω
  let e' : P ⊗[F] Ω ≃ₐ[F] (n → Ω) := (Algebra.TensorProduct.comm F P Ω).trans (e.restrictScalars F)
  have he' : ∀ ω : Ω, e' (1 ⊗ₜ ω) = fun _ => ω := fun ω => e.commutes ω
  let φ : P ⊗[F] (E ⊗[F] Ω) ≃ₐ[F] (n → Ω × Ω) :=
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : P ≃ₐ[F] P) g).trans
      (Algebra.TensorProduct.prodRight F F P Ω Ω)).trans
      ((AlgEquiv.prodCongr e' e').trans (splitClosedPair F Ω n))
  have hφ : ∀ p x i, φ (p ⊗ₜ x) i = (e' (p ⊗ₜ (g x).1) i, e' (p ⊗ₜ (g x).2) i) := by
    intro p x i; rfl
  refine ⟨φ, fun ω => funext fun i => by rw [hφ, hg1, he'], fun u i => ?_⟩
  induction u with
  | tmul p x => rw [tConj3, Algebra.TensorProduct.map_tmul, hφ, hφ, hg]; rfl
  | add a w ha hw => rw [map_add (f := _), map_add (f := _), map_add (f := _), Pi.add_apply, Pi.add_apply, ha, hw, Prod.swap_add]

end GlobalTheory.RegSS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EtaleTensorQuadraticSplitAlgClosedStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_tensor_quadratic_split_algClosed : GlobalTheory.RegSS.SplitClosed := by
  first | exact @GlobalTheory.RegSS.splitClosed | exact GlobalTheory.RegSS.splitClosed | (intros; apply GlobalTheory.RegSS.splitClosed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitSubtorusLaurentPolynomialPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitSubtorusLaurentPolynomialPoints
noncomputable section

open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS.Laurent

variable {F : Type} [Field F] {s : ℕ}

def chi (t : Fin s → Fˣ) : Multiplicative (Fin s → ℤ) →* F where
  toFun a := ((∏ j, t j ^ (Multiplicative.toAdd a) j : Fˣ) : F)
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, Pi.add_apply, _root_.zpow_add, Finset.prod_mul_distrib, Units.val_mul]

def ev (t : Fin s → Fˣ) : AddMonoidAlgebra F (Fin s → ℤ) →ₐ[F] F :=
  AddMonoidAlgebra.lift F F (Fin s → ℤ) (chi t)

theorem ev_single (t : Fin s → Fˣ) (a : Fin s → ℤ) (c : F) :
    ev t (AddMonoidAlgebra.single a c) = c * ((∏ j, t j ^ a j : Fˣ) : F) := by
  rw [ev, AddMonoidAlgebra.lift_single]; rfl

def univ (F : Type) [Field F] (s : ℕ) (j : Fin s) : (AddMonoidAlgebra F (Fin s → ℤ))ˣ where
  val := AddMonoidAlgebra.single (Pi.single j 1) 1
  inv := AddMonoidAlgebra.single (-Pi.single j 1) 1
  val_inv := by rw [AddMonoidAlgebra.single_mul_single]; simp [AddMonoidAlgebra.one_def]
  inv_val := by rw [AddMonoidAlgebra.single_mul_single]; simp [AddMonoidAlgebra.one_def]

theorem map_univ (t : Fin s → Fˣ) (j : Fin s) :
    Units.map (ev t : AddMonoidAlgebra F (Fin s → ℤ) →* F) (univ F s j) = t j := by
  refine Units.ext ?_
  change ev t (AddMonoidAlgebra.single (Pi.single j 1) 1) = _
  rw [ev_single, one_mul, Finset.prod_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem exists_coeff {E : Type} [CommRing E] [Algebra F E]
    (x : E ⊗[F] AddMonoidAlgebra F (Fin s → ℤ)) :
    ∃ c : (Fin s → ℤ) →₀ E ⊗[F] F, ∀ t : Fin s → Fˣ,
      Algebra.TensorProduct.map (AlgHom.id F E) (ev t) x =
        c.sum fun a y => ((∏ j, t j ^ a j : Fˣ) : F) • y := by
  have hadd : ∀ x y : E ⊗[F] AddMonoidAlgebra F (Fin s → ℤ),
      (∃ c : (Fin s → ℤ) →₀ E ⊗[F] F, ∀ t : Fin s → Fˣ,
        Algebra.TensorProduct.map (AlgHom.id F E) (ev t) x =
          c.sum fun a y => ((∏ j, t j ^ a j : Fˣ) : F) • y) →
      (∃ c : (Fin s → ℤ) →₀ E ⊗[F] F, ∀ t : Fin s → Fˣ,
        Algebra.TensorProduct.map (AlgHom.id F E) (ev t) y =
          c.sum fun a y => ((∏ j, t j ^ a j : Fˣ) : F) • y) →
      (∃ c : (Fin s → ℤ) →₀ E ⊗[F] F, ∀ t : Fin s → Fˣ,
        Algebra.TensorProduct.map (AlgHom.id F E) (ev t) (x + y) =
          c.sum fun a y => ((∏ j, t j ^ a j : Fˣ) : F) • y) := by
    rintro x y ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c + d, fun t => ?_⟩
    rw [map_add (f := _), hc, hd, Finsupp.sum_add_index' (by simp) (by simp [smul_add])]
  induction x with
  | add x y hx hy => exact hadd x y hx hy
  | tmul e p =>
    induction p using AddMonoidAlgebra.induction_linear with
    | zero => exact ⟨0, fun t => by simp⟩
    | add p q hp hq => rw [TensorProduct.tmul_add]; exact hadd _ _ hp hq
    | single a c =>
      refine ⟨Finsupp.single a (e ⊗ₜ c), fun t => ?_⟩
      rw [Finsupp.sum_single_index (by simp), Algebra.TensorProduct.map_tmul, ev_single,
        AlgHom.id_apply, mul_comm, ← smul_eq_mul, TensorProduct.tmul_smul]

end GlobalTheory.RegSS.Laurent

namespace GlobalTheory.RegSS

open Laurent

theorem subtorusLaurent : SubtorusLaurent := by
  intro F E _ _ _ n _ _ σ J γ s A
  classical
  choose c hc using fun i j : n => exists_coeff (F := F) (s := s)
    ((A.hom _ (univ F s) : Matrix n n (E ⊗[F] AddMonoidAlgebra F (Fin s → ℤ))) i j)
  refine ⟨Finset.univ.biUnion fun p : n × n => (c p.1 p.2).support,
    fun a => Matrix.of fun i j => c i j a, fun t => ?_⟩
  have h := A.natural _ F (ev t) (univ F s)
  simp only [map_univ] at h
  ext i j
  have h2 : (A.hom F t : Matrix n n (E ⊗[F] F)) i j =
      Algebra.TensorProduct.map (AlgHom.id F E) (ev t)
        ((A.hom _ (univ F s) : Matrix n n (E ⊗[F] AddMonoidAlgebra F (Fin s → ℤ))) i j) := by
    rw [h]; rfl
  rw [h2, hc, Matrix.sum_apply, Finsupp.sum_of_support_subset _
    (Finset.subset_biUnion_of_mem (fun p : n × n => (c p.1 p.2).support) (Finset.mem_univ (i, j)))
    _ (by simp)]
  rfl

end GlobalTheory.RegSS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitSubtorusLaurentPolynomialPointsStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_subtorus_laurentPolynomial_points : GlobalTheory.RegSS.SubtorusLaurent := by
  first | exact @GlobalTheory.RegSS.subtorusLaurent | exact GlobalTheory.RegSS.subtorusLaurent | (intros; apply GlobalTheory.RegSS.subtorusLaurent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentraliserPointsBoundedOfNormOneBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentraliserPointsBoundedOfNormOneBounded
noncomputable section

open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS.MatBd

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

theorem assoc_sigR (P : Type) [CommRing P] [Algebra F P] (σ : E →ₐ[F] E) (R : Type) [CommRing R]
    [Algebra F R] (x : (P ⊗[F] E) ⊗[F] R) :
    Algebra.TensorProduct.assoc F F F P E R (sigR (tConj P σ) R x) =
      tConj3 P σ R (Algebra.TensorProduct.assoc F F F P E R x) := by
  induction x with
  | tmul a r =>
    induction a with
    | tmul p e => simp [sigR, tConj, tConj3]
    | add a b ha hb => rw [TensorProduct.add_tmul, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]

def entry (σ : E →ₐ[F] E) (J γ : Matrix n n E) (i j : n) : plusAlg σ J γ ⊗[F] E →ₗ[F] E where
  toFun x := (plusTensor σ J γ x : Matrix n n E) i j
  map_add' a b := by rw [map_add (f := _)]; rfl
  map_smul' c a := by rw [map_smul]; rfl

theorem toMat_assoc_apply (σ : E →ₐ[F] E) (J γ : Matrix n n E) (R : Type) [CommRing R]
    [Algebra F R] (x : (plusAlg σ J γ ⊗[F] E) ⊗[F] R) (i j : n) :
    toMat σ J γ R (Algebra.TensorProduct.assoc F F F (plusAlg σ J γ) E R x) i j =
      LinearMap.rTensor R (entry σ J γ i j) x := by
  induction x with
  | tmul a r =>
    induction a with
    | tmul p e =>
      have h : (plusTensor σ J γ (p ⊗ₜ e) : Matrix n n E) =
          e • ((p : genAlg γ) : Matrix n n E) := by
        rw [plusTensor, Algebra.TensorProduct.productMap_apply_tmul, mul_comm]
        exact (Algebra.smul_def e ((p : genAlg γ) : Matrix n n E)).symm
      rw [Algebra.TensorProduct.assoc_tmul, LinearMap.rTensor_tmul]
      change (((p : genAlg γ) : Matrix n n E).map (inclE (F := F) R) *
        algebraMap (E ⊗[F] R) (Matrix n n (E ⊗[F] R)) (e ⊗ₜ r)) i j =
        ((plusTensor σ J γ (p ⊗ₜ e) : Matrix n n E) i j) ⊗ₜ r
      rw [h, ← Algebra.commutes, ← Algebra.smul_def]
      simp [inclE]
    | add a b ha hb =>
      rw [TensorProduct.add_tmul, map_add (f := _), map_add (f := _), map_add (f := _), Matrix.add_apply, ha, hb]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), Matrix.add_apply, ha, hb]

theorem toMat_assoc_inclE (σ : E →ₐ[F] E) (J γ : Matrix n n E) (R : Type) [CommRing R]
    [Algebra F R] (β : plusAlg σ J γ ⊗[F] E) :
    toMat σ J γ R (Algebra.TensorProduct.assoc F F F (plusAlg σ J γ) E R (inclE (F := F) R β)) =
      (plusTensor σ J γ β : Matrix n n E).map (inclE (F := F) R) := by
  ext i j
  rw [toMat_assoc_apply]
  rfl

theorem exists_centRat {σ : E →ₐ[F] E} {J : Matrix n n E} {γ : GL n E} (h : IsRegular σ J γ)
    (β : plusAlg σ J (γ : Matrix n n E) ⊗[F] E) (hβ : β * tConj _ σ β = 1) :
    ∃ δ ∈ centRat σ J γ, (δ : Matrix n n E) = plusTensor σ J (γ : Matrix n n E) β := by
  have h1 : (plusTensor σ J (γ : Matrix n n E) β : Matrix n n E) *
      adj (σ : E →+* E) J (plusTensor σ J (γ : Matrix n n E) β : Matrix n n E) = 1 := by
    rw [← plusTensor_tConj h, ← Subalgebra.coe_mul, ← map_mul, hβ, map_one]
    rfl
  refine ⟨⟨_, _, h1, mul_eq_one_comm.1 h1⟩, ⟨(mem_UJ_iff_mul_adj _ h.nondeg _).2 h1, ?_⟩, rfl⟩
  refine Subgroup.mem_centralizer_singleton_iff.2 (Units.ext ?_)
  exact (commute_of_mem_genAlg rfl (plusTensor σ J (γ : Matrix n n E) β).2).symm

theorem matOfNormBounded : MatOfNormBounded := by
  intro F E _ _ _ _ n _ _ σ J γ h _ _ hP hN
  obtain ⟨D, hD, hu⟩ := hN
  letI : TopologicalSpace (E ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := E) (AdeleRing (𝓞 F) F)
  letI : TopologicalSpace ((plusAlg σ J (γ : Matrix n n E) ⊗[F] E) ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := plusAlg σ J (γ : Matrix n n E) ⊗[F] E) (AdeleRing (𝓞 F) F)
  let a := Algebra.TensorProduct.assoc F F F (plusAlg σ J (γ : Matrix n n E)) E (AdeleRing (𝓞 F) F)
  have hc : Continuous fun x => toMat σ J (γ : Matrix n n E) (AdeleRing (𝓞 F) F) (a x) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [a, toMat_assoc_apply]
    exact continuous_rTensor _ _
  refine ⟨_, hD.image hc, fun g hg => ?_⟩
  obtain ⟨u, hu1, hug⟩ := ((hP (AdeleRing (𝓞 F) F)).2.2 g).1 hg
  obtain ⟨x, hx⟩ := a.surjective u
  obtain ⟨β, hβ, hxβ⟩ := hu x (a.injective (by
    rw [map_mul, map_one, assoc_sigR]
    change a x * tConj3 _ σ _ (a x) = 1
    rw [hx]
    exact hu1))
  obtain ⟨δ, hδ, hδβ⟩ := exists_centRat h β hβ
  refine ⟨δ, hδ, _, hxβ, ?_⟩
  beta_reduce
  rw [map_mul, map_mul, hx, hug, toMat_assoc_inclE, hδβ]

end GlobalTheory.RegSS.MatBd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentraliserPointsBoundedOfNormOneBoundedStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centraliser_points_bounded_of_normOne_bounded : GlobalTheory.RegSS.MatOfNormBounded := by
  first | exact @GlobalTheory.RegSS.MatBd.matOfNormBounded | exact GlobalTheory.RegSS.MatBd.matOfNormBounded | (intros; apply GlobalTheory.RegSS.MatBd.matOfNormBounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicQuotientNotCompactOfSplitIdempotent
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicQuotientNotCompactOfSplitIdempotent
noncomputable section

open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem bddAbove_of_compact_quotient {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G)
    [CompactSpace (G ⧸ H)] (f : G →* ℝ) (hf : Continuous f) (hH : ∀ h ∈ H, f h = 1) :
    ∃ C : ℝ, ∀ g, f g ≤ C := by
  let φ : G ⧸ H → ℝ := Quotient.lift f fun a b hab => by
    have h := hH _ (QuotientGroup.leftRel_apply.1 hab)
    rw [← mul_one (f a), ← h, ← map_mul, mul_inv_cancel_left]
  have hφ : Continuous φ := hf.quotient_lift _
  obtain ⟨C, hC⟩ := (isCompact_range hφ).bddAbove
  exact ⟨C, fun g => hC ⟨(g : G ⧸ H), rfl⟩⟩

theorem exists_one_lt_ideleNorm (F : Type) [Field F] [NumberField F] :
    ∃ t : Idele F, 1 < ideleNorm t := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
  let P : HeightOneSpectrum (𝓞 F) :=
    ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField F)⟩
  obtain ⟨ϖ, hϖ⟩ := exists_isUniformiser P
  have h1 : ‖(ϖ : P.adicCompletion F)‖ = (Ideal.absNorm P.asIdeal : ℝ)⁻¹ := by
    rw [FinitePlace.norm_def, hϖ, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    simp
  refine ⟨(localIdele P ϖ)⁻¹, ?_⟩
  rw [map_inv, UnitaryHeckeChar.ideleNorm_localIdele, h1, inv_inv]
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm P

theorem commute_map_of_mem_centPts {F E : Type} [Field F] [CommRing E] [Algebra F E]
    {n : Type} [Fintype n] [DecidableEq n] {σ : E →ₐ[F] E} {J : Matrix n n E} {γ : GL n E}
    (R : Type) [CommRing R] [Algebra F R] {ε : Matrix n n E} (hε : ε ∈ genAlg (γ : Matrix n n E))
    {g : GL n (E ⊗[F] R)} (hg : g ∈ centPts σ J γ R) :
    (g : Matrix n n (E ⊗[F] R)) * ε.map (inclE (F := F) R) = ε.map (inclE (F := F) R) * g := by
  have h : (g : Matrix n n (E ⊗[F] R)) * (γ : Matrix n n E).map (inclE (F := F) R) =
      (γ : Matrix n n E).map (inclE (F := F) R) * g :=
    congrArg Units.val (Subgroup.mem_centralizer_singleton_iff.1 hg.2)
  refine commute_of_mem_genAlg h ?_
  induction hε using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.1 hx]; exact Algebra.self_mem_adjoin_singleton _ _
  | algebraMap r =>
    have : (algebraMap E (Matrix n n E) r).map (inclE (F := F) R) =
        algebraMap (E ⊗[F] R) _ (inclE (F := F) R r) := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]
    rw [this]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy =>
    rw [Matrix.map_add _ (map_add _)]; exact add_mem hx hy
  | mul x y _ _ hx hy =>
    rw [Matrix.map_mul]; exact mul_mem hx hy

theorem notCompactOfIdempotent_of (hD : IdempotentDet) : NotCompactOfIdempotent := by
  intro F E _ _ _ _ n _ _ σ J γ hreg ε hε hε0 hεε ht hc
  haveI := quad_finite hreg.quad
  letI : TopologicalSpace (E ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := E) (AdeleRing (𝓞 F) F)
  obtain ⟨d, χ, hd, hχ, h1, hmul, hrat, hval⟩ := hD F E n ε hε0 hεε (AdeleRing (𝓞 F) F)
  let χ₀ : centPts σ J γ (AdeleRing (𝓞 F) F) →* AdeleRing (𝓞 F) F :=
    { toFun := fun g => χ (g.1 : Matrix n n _)
      map_one' := h1
      map_mul' := fun g h => hmul _ _ (commute_map_of_mem_centPts _ hε h.2) }
  have hχ₀ : Continuous χ₀ := hχ.comp (Units.continuous_val.comp continuous_subtype_val)
  have hχi : Continuous fun g => χ₀ g⁻¹ :=
    hχ.comp (Units.continuous_coe_inv.comp continuous_subtype_val)
  have hχ₁ : Continuous χ₀.toHomUnits := Units.continuous_iff.2 ⟨hχ₀, hχi⟩
  haveI : CompactSpace (centPts σ J γ (AdeleRing (𝓞 F) F) ⧸
    ((centRat σ J γ).map (bc (inclE (F := F) (AdeleRing (𝓞 F) F)))).subgroupOf
      (centPts σ J γ (AdeleRing (𝓞 F) F))) := hc
  obtain ⟨C, hC⟩ := bddAbove_of_compact_quotient
    (((centRat σ J γ).map (bc (inclE (F := F) (AdeleRing (𝓞 F) F)))).subgroupOf
      (centPts σ J γ (AdeleRing (𝓞 F) F))) (ideleNorm.comp χ₀.toHomUnits)
    (continuous_ideleNorm.comp hχ₁) (by
      rintro g ⟨δ, -, hδ⟩
      obtain ⟨c, hc⟩ := hrat δ
      have e : ((χ₀.toHomUnits g : Idele F) : AdeleRing (𝓞 F) F) = algebraMap F _ c := by
        rw [← hc]
        change χ (g.1 : Matrix n n _) = _
        rw [show g.1 = _ from hδ.symm]
        rfl
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [map_zero] at e
        haveI : Nontrivial (AdeleRing (𝓞 F) F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
        exact Units.ne_zero _ e
      have e' : χ₀.toHomUnits g = principalIdele F (Units.mk0 c hc0) := Units.ext e
      rw [MonoidHom.comp_apply, e', ideleNorm_principalIdele])
  obtain ⟨t, ht1⟩ := exists_one_lt_ideleNorm F
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C (one_lt_pow₀ ht1 hd.ne')
  obtain ⟨g, hg, hgt⟩ := ht (t ^ m)
  have e : χ₀.toHomUnits ⟨g, hg⟩ = (t ^ m) ^ d := Units.ext (hval _ _ hgt)
  have := hC ⟨g, hg⟩
  rw [MonoidHom.comp_apply, e, map_pow, map_pow, ← pow_mul, mul_comm, pow_mul] at this
  exact absurd hm (not_lt.2 this)

end GlobalTheory.RegSS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicQuotientNotCompactOfSplitIdempotentStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_quotient_not_compact_of_split_idempotent : GlobalTheory.RegSS.IdempotentDet → GlobalTheory.RegSS.NotCompactOfIdempotent := by
  first | exact @GlobalTheory.RegSS.notCompactOfIdempotent_of | exact GlobalTheory.RegSS.notCompactOfIdempotent_of | (intros; apply GlobalTheory.RegSS.notCompactOfIdempotent_of <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitFactorIdempotentsExist
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitFactorIdempotentsExist
open GlobalTheory.RegSS GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem exists_sq_of_not_isField_tensor {F E K : Type} [Field F] [CommRing E] [Algebra F E]
    [Field K] [Algebra F K] (b : Module.Basis (Fin 2) F E) (d : F) (h0 : b 0 = 1)
    (h1 : b 1 * b 1 = algebraMap F E d) (h : ¬ IsField (K ⊗[F] E)) :
    ∃ c : K, c * c = algebraMap F K d := by
  by_contra hc
  push_neg at hc
  apply h
  let B := Algebra.TensorProduct.basis K b
  have hB0 : B 0 = 1 := by simp [B, h0, Algebra.TensorProduct.one_def]
  have hB1 : B 1 * B 1 = algebraMap F K d • (1 : K ⊗[F] E) := by
    simp only [B, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, h1,
      mul_one, algebraMap_smul]
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, Algebra.TensorProduct.one_def]
  refine ⟨⟨0, 1, ?_⟩, mul_comm, fun {x} hx => ?_⟩
  · rw [← hB0]; exact (B.ne_zero 0).symm
  · have hs := B.sum_repr x
    rw [Fin.sum_univ_two, hB0] at hs
    set s := B.repr x 0
    set t := B.repr x 1
    have hn : s * s - algebraMap F K d * (t * t) ≠ 0 := by
      intro hn
      by_cases ht : t = 0
      · have hs0 : s = 0 := by simpa [ht] using hn
        exact hx (by rw [← hs, hs0, ht]; simp)
      · refine hc (s / t) ?_
        field_simp
        linear_combination hn
    refine ⟨(s * s - algebraMap F K d * (t * t))⁻¹ • (s • (1 : K ⊗[F] E) - t • B 1), ?_⟩
    have : x * (s • (1 : K ⊗[F] E) - t • B 1) =
        (s * s - algebraMap F K d * (t * t)) • (1 : K ⊗[F] E) := by
      rw [← hs]
      simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hB1, one_mul, mul_one]
      module
    rw [mul_smul_comm, this, smul_smul, inv_mul_cancel₀ hn, one_smul]

theorem splitIdempotents : SplitIdempotents := by
  intro F E _ _ _ _ σ hσ P _ _ k K _ _ ⟨e⟩
  classical
  obtain ⟨b, d, h0, hb, hd, h1⟩ := quad_exists_basis hσ
  have hc : ∀ i : {i : Fin k // ¬ IsField (K i ⊗[F] E)}, ∃ c : K i, c * c * algebraMap F _ d = 1 := by
    intro i
    obtain ⟨c, hc⟩ := exists_sq_of_not_isField_tensor b d h0 h1 i.2
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hd ((algebraMap F (K i)).injective (by simpa using hc.symm))
    exact ⟨c⁻¹, by rw [← hc]; field_simp⟩
  choose c hc using hc
  let u : {i : Fin k // ¬ IsField (K i ⊗[F] E)} → P := fun i => e.symm (Pi.single i.1 1)
  let v : {i : Fin k // ¬ IsField (K i ⊗[F] E)} → P := fun i => e.symm (Pi.single i.1 (c i))
  have same : ∀ (i : Fin k) (x y : K i), e.symm (Pi.single i x) * e.symm (Pi.single i y) =
      e.symm (Pi.single i (x * y)) := fun i x y => by rw [← map_mul, Pi.single_mul]
  have diff : ∀ (i j : Fin k) (x : K i) (y : K j), i ≠ j →
      e.symm (Pi.single i x) * e.symm (Pi.single j y) = 0 := fun i j x y hij => by
    rw [← map_mul, ← map_zero e.symm]
    congr 1
    ext l
    by_cases hl : l = i
    · subst hl; simp [Pi.single_eq_of_ne hij]
    · simp [Pi.single_eq_of_ne hl]
  have hUU : ∀ i, (u i ⊗ₜ[F] (1 : E)) * (u i ⊗ₜ[F] (1 : E)) = u i ⊗ₜ[F] (1 : E) := fun i => by
    simp [u, same]
  have hUV : ∀ i, (u i ⊗ₜ[F] (1 : E)) * (v i ⊗ₜ[F] b 1) = v i ⊗ₜ[F] b 1 := fun i => by
    simp [u, v, same]
  have hVV : ∀ i, (v i ⊗ₜ[F] b 1) * (v i ⊗ₜ[F] b 1) = u i ⊗ₜ[F] (1 : E) := fun i => by
    rw [Algebra.TensorProduct.tmul_mul_tmul, h1, Algebra.algebraMap_eq_smul_one,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    simp only [u, v, same]
    rw [← map_smul, ← Pi.single_smul, Algebra.smul_def, mul_comm, hc]
  have hconj : ∀ j, tConj P σ ((2⁻¹ : F) • (u j ⊗ₜ[F] (1 : E) + v j ⊗ₜ[F] b 1)) =
      (2⁻¹ : F) • (u j ⊗ₜ[F] (1 : E) - v j ⊗ₜ[F] b 1) := fun j => by
    simp [tConj, hb, TensorProduct.tmul_neg, sub_eq_add_neg]
  refine ⟨fun i => (2⁻¹ : F) • (u i ⊗ₜ[F] (1 : E) + v i ⊗ₜ[F] b 1), fun i hi => ?_, fun i => ?_,
    fun i j hij => ?_, fun i j => ?_⟩
  · have hi' : u i ⊗ₜ[F] (b 0) + v i ⊗ₜ[F] b 1 = 0 := by
      rw [h0]; exact (smul_eq_zero.1 hi).resolve_left (inv_ne_zero two_ne_zero)
    have h2 := congrArg (fun x => (Algebra.TensorProduct.basis P b).repr x 0) hi'
    simp only [map_add (f := _), Finsupp.add_apply, Algebra.TensorProduct.basis_repr_tmul] at h2
    have h3 : u i = 0 := by simpa using h2
    have h4 := congrFun (e.symm.injective (h3.trans (map_zero e.symm).symm)) i.1
    simp at h4
  · simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, hUU, hVV, hUV,
      mul_comm (v i ⊗ₜ[F] b 1) (u i ⊗ₜ[F] (1 : E))]
    module
  · have hij' : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    simp [add_mul, mul_add, u, v, diff _ _ _ _ hij']
  · rw [hconj]
    by_cases hij : i = j
    · subst hij
      simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_sub, hUU, hVV, hUV,
        mul_comm (v i ⊗ₜ[F] b 1) (u i ⊗ₜ[F] (1 : E))]
      module
    · have hij' : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      simp [add_mul, mul_sub, u, v, diff _ _ _ _ hij']

end GlobalTheory.RegSS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitFactorIdempotentsExistStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_factor_idempotents_exist : GlobalTheory.RegSS.SplitIdempotents := by
  first | exact @GlobalTheory.RegSS.splitIdempotents | exact GlobalTheory.RegSS.splitIdempotents | (intros; apply GlobalTheory.RegSS.splitIdempotents <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitTranslateBoundedOfFactors
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitTranslateBoundedOfFactors
noncomputable section

open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem unitBounded_of_split (hL : TensorLattice) {F B : Type} [Field F] [NumberField F]
    [CommRing B] [Algebra F B] [Module.Finite F B] (τ : B →ₐ[F] B) {k : ℕ} (C : Fin k → Type)
    [∀ i, CommRing (C i)] [∀ i, Algebra F (C i)] (ρ : ∀ i, C i →ₐ[F] C i)
    (π : ∀ i, B →ₐ[F] C i) (s : ∀ i, C i →ₗ[F] B)
    (hsum : ∀ x, ∑ i, s i (π i x) = x)
    (hmul : ∀ i x y, s i (π i x * y) = x * s i y)
    (hps : ∀ (b : ∀ i, C i) j, π j (∑ i, s i (b i)) = b j)
    (hcomm : ∀ i x, π i (τ x) = ρ i (π i x))
    (h : ∀ i, UnitBounded F (C i) (ρ i)) : UnitBounded F B τ := by
  classical
  letI : TopologicalSpace (B ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := B) (AdeleRing (𝓞 F) F)
  letI (i : Fin k) : TopologicalSpace (C i ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := C i) (AdeleRing (𝓞 F) F)
  haveI := (hL F B).1
  choose D hD hDu using h
  let p (i : Fin k) : B ⊗[F] AdeleRing (𝓞 F) F →ₐ[F] C i ⊗[F] AdeleRing (𝓞 F) F :=
    Algebra.TensorProduct.map (π i) (AlgHom.id F _)
  let Φ : (∀ i, C i ⊗[F] AdeleRing (𝓞 F) F) → B ⊗[F] AdeleRing (𝓞 F) F :=
    fun x => ∑ i, LinearMap.rTensor (AdeleRing (𝓞 F) F) (s i) (x i)
  have hΦ : Continuous Φ :=
    continuous_finsetSum _ fun i _ =>
      (continuous_rTensor (AdeleRing (𝓞 F) F) (s i)).comp (continuous_apply i)
  have hp : ∀ i u, p i (sigR τ _ u) = sigR (ρ i) _ (p i u) := by
    intro i u
    induction u with
    | tmul a b => simp [p, sigR, hcomm]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
  have hm : ∀ i u (y : C i), LinearMap.rTensor (AdeleRing (𝓞 F) F) (s i)
      (p i u * inclE (F := F) _ y) = u * inclE (F := F) _ (s i y) := by
    intro i u y
    induction u with
    | tmul a b => simp [p, inclE, hmul]
    | add a b ha hb => rw [map_add (f := _), add_mul, map_add (f := _), add_mul, ha, hb]
  refine ⟨Φ '' Set.pi Set.univ D, (isCompact_univ_pi hD).image hΦ, fun u hu => ?_⟩
  have hpu : ∀ i, p i u * sigR (ρ i) _ (p i u) = 1 := fun i => by
    rw [← hp, ← map_mul, hu, map_one]
  choose β hβ hβD using fun i => hDu i (p i u) (hpu i)
  choose γ hγ using fun i => (hβ i).exists_right_inv
  refine ⟨∑ i, s i (β i), IsUnit.of_mul_eq_one (∑ i, s i (γ i)) ?_,
    fun i => p i u * inclE (F := F) _ (β i), fun i _ => hβD i, ?_⟩
  · rw [Finset.mul_sum]
    simp only [← hmul, hps, hγ]
    simpa using hsum 1
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [Φ, hm, map_sum, Finset.mul_sum]

theorem productUnitBounded (hL : TensorLattice) : ProductUnitBounded := by
  classical
  intro F E _ _ _ _ _ σ P _ _ _ k K _ _ ⟨e⟩ h
  let q (i : Fin k) : P →ₐ[F] K i := (Pi.evalAlgHom F K i).comp (e : P →ₐ[F] ∀ i, K i)
  let t (i : Fin k) : K i →ₗ[F] P := e.symm.toLinearMap ∘ₗ LinearMap.single F K i
  have hq : ∀ i x, q i x = e x i := fun _ _ => rfl
  have ht : ∀ i x, t i x = e.symm (Pi.single i x) := fun _ _ => rfl
  have h1 : ∀ x, ∑ i, t i (q i x) = x := fun x => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hq, ht, ← map_sum, Finset.univ_sum_single, AlgEquiv.symm_apply_apply]
  have h2 : ∀ i x y, t i (q i x * y) = x * t i y := fun i x y => by
    apply e.injective
    simp only [hq, ht, map_mul, AlgEquiv.apply_symm_apply]
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  refine unitBounded_of_split hL (tConj P σ) (fun i => K i ⊗[F] E) (fun i => tConj (K i) σ)
    (fun i => Algebra.TensorProduct.map (q i) (AlgHom.id F E))
    (fun i => LinearMap.rTensor E (t i)) ?_ ?_ ?_ ?_ h
  · intro x
    induction x with
    | tmul a b => simp [← TensorProduct.sum_tmul, h1]
    | add a b ha hb => simp only [map_add (f := _), Finset.sum_add_distrib, ha, hb]
  · intro i x y
    induction x with
    | add a b ha hb => simp only [map_add (f := _), add_mul, ha, hb]
    | tmul a b =>
      induction y with
      | add c d hc hd => simp only [map_add (f := _), mul_add, hc, hd]
      | tmul c d => simp [h2]
  · intro b j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single j]
    · generalize b j = y
      induction y with
      | add c d hc hd => simp only [map_add (f := _), hc, hd]
      | tmul c d => simp [hq, ht]
    · intro i _ hi
      generalize b i = y
      induction y with
      | add c d hc hd => simp only [map_add (f := _), hc, hd, add_zero]
      | tmul c d => simp [hq, ht, hi.symm]
    · simp
  · intro i x
    induction x with
    | tmul a b => simp [tConj]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]

end GlobalTheory.RegSS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitTranslateBoundedOfFactorsStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_unit_translate_bounded_of_factors : GlobalTheory.RegSS.TensorLattice → GlobalTheory.RegSS.ProductUnitBounded := by
  first | exact @GlobalTheory.RegSS.productUnitBounded | exact GlobalTheory.RegSS.productUnitBounded | (intros; apply GlobalTheory.RegSS.productUnitBounded <;> assumption)
end
end
