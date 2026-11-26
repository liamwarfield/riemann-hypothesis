module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStandardTypeVectorOfParabolicTypeVector
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameCharacterParahoricInvariant
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameGenAtTransport

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantMapOfLevelTypeVector
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantMapOfLevelTypeVector
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LevelType

theorem exists_map_of_typeVec (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] (n : Type) [Fintype n] [DecidableEq n] (W : Type) [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL n F) W) (ρ : FDRep ℂ (GL n (ZMod p))) (y : W) :
    resCard F = p → TypeVec π (Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) y → ∃ φ : ρ →ₗ[ℂ] W, φ ≠ 0 ∧
      ∀ (g : GL n (ZMod p)) (h : GL n F), IsLift g h → ∀ w, π h (φ w) = φ (ρ.ρ g w) := by
  intro hp hy
  obtain ⟨h1, ℓ, hℓ, h0⟩ := hy
  let Φ : Module.Dual ℂ ρ → (ρ →ₗ[ℂ] W) := fun μ =>
    ∑ g : GL n (ZMod p), LinearMap.smulRight (μ ∘ₗ ρ.ρ g⁻¹) (π (ℓ g) y)
  have hΦ : ∀ μ w, Φ μ w = ∑ g, μ (ρ.ρ g⁻¹ w) • π (ℓ g) y := by
    intro μ w
    simp [Φ, LinearMap.sum_apply]
  have heq : ∀ μ (g₀ : GL n (ZMod p)) (h : GL n F), IsLift g₀ h → ∀ w, π h (Φ μ w) = Φ μ (ρ.ρ g₀ w) := by
    intro μ g₀ h H w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hΦ, hΦ, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft g₀) _ _ fun g => ?_
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, IsLift.apply_eq hp h1 (H.mul hp (hℓ g)) (hℓ _)]
    simp [mul_inv_rev, map_mul, Module.End.mul_apply]
  by_contra hne
  have hz : ∀ μ, Φ μ = 0 := fun μ => by
    by_contra e
    exact hne ⟨_, e, heq μ⟩
  apply h0
  let b := Module.finBasis ℂ ρ
  have key : ∑ g, LinearMap.trace ℂ ρ (ρ.ρ g⁻¹) • π (ℓ g) y = 0 := by
    have : ∑ i, Φ (b.coord i) (b i) = 0 := by simp [hz]
    rw [← this]
    simp_rw [hΦ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.sum_smul, LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    rfl
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp_rw [Formalism.IrreducibleCountingLemmas.TYPES.zIdem_coeff, mul_smul]
  rw [← Finset.smul_sum, key, smul_zero]

end GlobalTheory.LevelType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantMapOfLevelTypeVectorStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariantMap_of_levelTypeVector : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] (n : Type) [Fintype n] [DecidableEq n] (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL n F) W) (ρ : FDRep ℂ (GL n (ZMod p))) (y : W), resCard F = p → TypeVec π (Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) y → ∃ φ : ρ →ₗ[ℂ] W, φ ≠ 0 ∧ ∀ (g : GL n (ZMod p)) (h : GL n F), IsLift g h → ∀ w, π h (φ w) = φ (ρ.ρ g w) := by
  first | exact @GlobalTheory.LevelType.exists_map_of_typeVec | exact GlobalTheory.LevelType.exists_map_of_typeVec | (intros; apply GlobalTheory.LevelType.exists_map_of_typeVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParabolicTypeVectorOfEquivariantMap
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParabolicTypeVectorOfEquivariantMap
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType GlobalTheory.StepData GlobalTheory.ProdSupport Matrix ValuativeRel
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LevelType

theorem exists_parVec_of_map : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] (α n : Type) [Fintype α] [LinearOrder α] [Fintype n] [DecidableEq n] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ n) (X : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (s : ∀ a, Representation ℂ (GL (m a) F) (X a)) (a : α) (θ : (ZMod p)ˣ →* ℂˣ) (χ : Fˣ →* ℂˣ) (U : Type) [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL n (ZMod p)) U) (φ : U →ₗ[ℂ] IndSp e (piTensor s)), resCard F = p → CharLift θ χ → (∀ g ∈ KO F (m a), ∀ v, s a g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v) → φ ≠ 0 → (∀ (g : GL n (ZMod p)) (h : GL n F), IsLift g h → ∀ w, multiProd e s h (φ w) = φ (ρ g w)) → ∃ v : U, v ≠ 0 ∧ ParVec ρ e a θ v := by
  intro F _ _ _ _ p _ α n _ _ _ _ m _ _ e X _ _ s a θ χ U _ _ ρ φ hp hθ hs hφ hint
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  let Λ : U →ₗ[ℂ] (⨂[ℂ] b, X b) :=
    { toFun := fun w => (φ w).1.1 1
      map_add' := fun x y => by rw [map_add (f := _)]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  have hΛ : ∀ w, Λ w = (φ w).1.1 1 := fun _ => rfl
  have hΛ0 : Λ ≠ 0 := by
    obtain ⟨w, hw⟩ : ∃ w, φ w ≠ 0 := by
      by_contra! h
      exact hφ (LinearMap.ext h)
    obtain ⟨x, hx⟩ : ∃ x, (φ w).1.1 x ≠ 0 := by
      by_contra! h
      exact hw (Subtype.ext (Subtype.ext (funext h)))
    obtain ⟨q, κ, hκ, rfl⟩ := MultiIrr.exists_parab_mul e x
    obtain ⟨g, hg⟩ := exists_isLift_of_mem_KO hp hκ
    intro h0
    apply hx
    have h1 : (φ w).1.1 κ = 0 := by
      have h2 : Λ (ρ g w) = 0 := by rw [h0]; rfl
      rw [hΛ, ← hint g κ hg w] at h2
      have h3 : (multiProd e s κ (φ w)).1.1 1 = (φ w).1.1 (1 * κ) := rfl
      rwa [h3, one_mul] at h2
    rw [parInd_law, h1, map_zero, smul_zero]
  let H : Subgroup (GL n (ZMod p)) := Subgroup.map (parab (ZMod p) e).subtype
    (⨅ b : {b // b ≠ a}, ((Pi.evalMonoidHom (fun c => GL (m c) (ZMod p)) b.1).comp (leviProj (ZMod p) e)).ker)
  have hH : ∀ x : parab (ZMod p) e, (∀ b, b ≠ a → leviProj (ZMod p) e x b = 1) → (x : GL n (ZMod p)) ∈ H := by
    intro x hx
    refine ⟨x, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_iInf]
    intro b
    exact MonoidHom.mem_ker.2 (hx b.1 b.2)
  have hH' : ∀ y ∈ H, ∃ x : parab (ZMod p) e, (x : GL n (ZMod p)) = y ∧
      ∀ b, b ≠ a → leviProj (ZMod p) e x b = 1 := by
    rintro y ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_iInf] at hx
    exact ⟨x, rfl, fun b hb => MonoidHom.mem_ker.1 (hx ⟨b, hb⟩)⟩
  have key : ∀ y ∈ H, ∀ w, Λ (ρ y w) = ((θ.comp GeneralLinearGroup.det y : ℂˣ) : ℂ) • Λ w := by
    intro y hy w
    obtain ⟨x, rfl, hx⟩ := hH' y hy
    obtain ⟨h, hh, hl⟩ := exists_canon_lift hp (x : GL n (ZMod p))
    have hP : h ∈ parab F e := mem_parab.2 fun i j hij => by
      have h0 := mem_parab.1 x.2 i j hij
      change h.val i j = 0
      rw [hh]
      change ((((x : GL n (ZMod p)) : Matrix n n (ZMod p)) i j).val : F) = 0
      rw [h0]
      simp
    let q : parab F e := ⟨h, hP⟩
    have hq : ∀ b, b ≠ a → leviProj F e q b = 1 := by
      intro b hb
      have h2 := hx b hb
      refine Units.ext (Matrix.ext fun i j => ?_)
      have h3 := congrArg (fun g : GL (m b) (ZMod p) => (g : Matrix (m b) (m b) (ZMod p)) i j) h2
      simp only [leviProj_apply] at h3
      rw [leviProj_apply]
      change h.val _ _ = _
      rw [hh]
      change ((((x : GL n (ZMod p)) : Matrix n n (ZMod p)) _ _).val : F) = _
      rw [h3]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij, ZMod.val_one]
    have hqa : leviProj F e q = Pi.mulSingle a (leviProj F e q a) := by
      funext b
      by_cases hb : b = a
      · subst hb; simp
      · rw [Pi.mulSingle_eq_of_ne hb, hq b hb]
    have hKa : leviProj F e q a ∈ KO F (m a) := by
      refine IsLift.mem_KO hp (g := leviProj (ZMod p) e x a) fun i j => ?_
      change valuation F (h.val _ _ - _) < 1
      rw [hh]
      simp
    have hδ : deltaHalf F m (leviProj F e q) = 1 := by
      rw [deltaHalf_apply]
      refine Finset.prod_eq_one fun b _ => isUnram_absPow F _ _ ?_
      by_cases hb : b = a
      · subst hb; exact valuation_det_of_mem_KO hKa
      · rw [hq b hb, map_one]; simp
    have hdet : χ (GeneralLinearGroup.det (leviProj F e q a)) = θ (GeneralLinearGroup.det (x : GL n (ZMod p))) := by
      rw [← CharLift.det hp hθ hl]
      congr 1
      change _ = GeneralLinearGroup.det (q : GL n F)
      rw [det_parab F e q, Finset.prod_eq_single a]
      · intro b _ hb; rw [hq b hb, map_one]
      · simp
    have hv := hint _ h hl w
    rw [hΛ, hΛ, ← hv]
    change (φ w).1.1 (1 * h) = _
    rw [one_mul]
    have hlaw := parInd_law e (piTensor s) (φ w) q 1
    rw [mul_one] at hlaw
    change (φ w).1.1 (q : GL n F) = _
    rw [hlaw, hδ, Units.val_one, one_smul, hqa, piTensor_mulSingle s a _ _ (hs _ hKa), MonoidHom.comp_apply, hdet]
  obtain ⟨v, hv0, hv⟩ := exists_eigen_of_map ρ H (θ.comp GeneralLinearGroup.det) Λ hΛ0 key
  exact ⟨v, hv0, fun x hx => hv _ (hH x hx)⟩

end GlobalTheory.LevelType

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParabolicTypeVectorOfEquivariantMapStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_parabolicTypeVector_of_equivariantMap : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] (α n : Type) [Fintype α] [LinearOrder α] [Fintype n] [DecidableEq n] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ n) (X : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (s : ∀ a, Representation ℂ (GL (m a) F) (X a)) (a : α) (θ : (ZMod p)ˣ →* ℂˣ) (χ : Fˣ →* ℂˣ) (U : Type) [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL n (ZMod p)) U) (φ : U →ₗ[ℂ] IndSp e (piTensor s)), resCard F = p → CharLift θ χ → (∀ g ∈ KO F (m a), ∀ v, s a g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v) → φ ≠ 0 → (∀ (g : GL n (ZMod p)) (h : GL n F), IsLift g h → ∀ w, multiProd e s h (φ w) = φ (ρ g w)) → ∃ v : U, v ≠ 0 ∧ ParVec ρ e a θ v := by
  first | exact @GlobalTheory.LevelType.exists_parVec_of_map | exact GlobalTheory.LevelType.exists_parVec_of_map | (intros; apply GlobalTheory.LevelType.exists_parVec_of_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionEmptySecondIsSubquotientFirst
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionEmptySecondIsSubquotientFirst
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EmptySecondBlockProd

variable {c : Bool → ℕ} {r : ℕ}

def falseEquiv (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0) : Fin (c false) ≃ Fin r :=
  Equiv.ofBijective (fun i => f ⟨false, i⟩) ⟨fun i j h => by
    have := f.injective h
    simpa using this, fun x => by
    obtain ⟨⟨b, i⟩, rfl⟩ := f.surjective x
    cases b with
    | false => exact ⟨i, rfl⟩
    | true => exact absurd i.2 (by omega)⟩

theorem mem_parab_all {R : Type} [CommRing R] (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (g : GL (Fin r) R) : g ∈ parab R f := by
  refine mem_parab_iff.2 fun a b i j hab => ?_
  cases a with
  | false => exact absurd hab (by cases b <;> decide)
  | true => exact absurd i.2 (by omega)

theorem eq_one_true {R : Type} [CommRing R] (hc : c true = 0) (h : GL (Fin (c true)) R) : h = 1 :=
  Units.ext (Matrix.ext fun i _ => (Fin.cast hc i).elim0)

def levi {R : Type} [CommRing R] (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0) :
    GL (Fin r) R →* Levi R (fun j => Fin (c j)) :=
  (leviProj R f).comp ((MonoidHom.id _).codRestrict (parab R f) (mem_parab_all f hc))

theorem levi_false {R : Type} [CommRing R] (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (g : GL (Fin r) R) : levi f hc g false = reix R (falseEquiv f hc).symm g :=
  Units.ext (Matrix.ext fun _ _ => rfl)

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem deltaHalf_eq_one (hc : c true = 0) (g : Levi F (fun j => Fin (c j))) :
    deltaHalf F (fun j => Fin (c j)) g = 1 := by
  rw [deltaHalf_apply, Fintype.prod_bool]
  have h1 : modExp (fun j => Fin (c j)) false = 0 := by
    simp only [modExp, Finset.sum_filter, Fintype.sum_bool]
    simp [hc]
  have h2 : Matrix.GeneralLinearGroup.det (g true) = 1 := by
    rw [eq_one_true hc (g true), map_one]
  rw [h1, h2]
  simp

end GlobalTheory.EmptySecondBlockProd

namespace GlobalTheory.EmptySecondBlockProd

variable {c : Bool → ℕ} {r : ℕ}
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def evOne (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (ρ : Representation ℂ (Levi F (fun j => Fin (c j))) W) :
    (parInd f ρ).IntertwiningMap (ρ.comp (levi f hc)) where
  toLinearMap :=
    { toFun := fun x => x.1.1 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  isIntertwining' g := by
    refine LinearMap.ext fun x => ?_
    show x.1.1 (1 * g) = ρ (levi f hc g) (x.1.1 1)
    have := parInd_law f ρ x ⟨g, mem_parab_all f hc g⟩ 1
    rw [mul_one] at this
    rw [one_mul, this, deltaHalf_eq_one hc, Units.val_one, one_smul]
    rfl

theorem evOne_apply (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (ρ : Representation ℂ (Levi F (fun j => Fin (c j))) W) (x : IndSp f ρ) :
    evOne f hc ρ x = x.1.1 1 := rfl

theorem evOne_injective (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (ρ : Representation ℂ (Levi F (fun j => Fin (c j))) W) : Function.Injective (evOne f hc ρ) := by
  refine (injective_iff_map_eq_zero (evOne f hc ρ)).2 fun x hx => ?_
  rw [evOne_apply] at hx
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  have := parInd_law f ρ x ⟨g, mem_parab_all f hc g⟩ 1
  rw [mul_one] at this
  show x.1.1 g = 0
  rw [this, hx, map_zero, smul_zero]

end GlobalTheory.EmptySecondBlockProd

namespace GlobalTheory.EmptySecondBlockProd

variable {c : Bool → ℕ} {r : ℕ}
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_smul_eq (hc : c true = 0) (σ : IrrRep (GL (Fin (c true)) F)) {z : σ.V} (hz : z ≠ 0)
    (y : σ.V) : ∃ a : ℂ, a • z = y := by
  let S : Subrepresentation σ.ρ := ⟨ℂ ∙ z, fun g v hv => by
    rw [eq_one_true hc g, map_one]
    exact hv⟩
  haveI := σ.irr
  rcases eq_bot_or_eq_top S with h | h
  · exfalso
    have : z ∈ S.toSubmodule := Submodule.mem_span_singleton_self z
    rw [h] at this
    exact hz this
  · have : y ∈ S.toSubmodule := by rw [h]; trivial
    exact Submodule.mem_span_singleton.1 this

def tensorMap (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (s : ∀ j, IrrRep (GL (Fin (c j)) F)) (x₀ : ∀ j, (s j).V) :
    Representation.IntertwiningMap
      ((s false).ρ.comp (reix F (falseEquiv f hc).symm) : Representation ℂ (GL (Fin r) F) (s false).V)
      ((piTensor fun j => (s j).ρ).comp (levi f hc)) where
  toLinearMap := (PiTensorProduct.tprod ℂ).toLinearMap x₀ false
  isIntertwining' g := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, MonoidHom.coe_comp, Function.comp_apply,
      MultilinearMap.toLinearMap_apply, piTensor_tprod]
    congr 1
    funext j
    cases j with
    | false => simp [levi_false]
    | true => simp [eq_one_true hc (levi f hc g true)]

theorem tensorMap_surjective (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (s : ∀ j, IrrRep (GL (Fin (c j)) F)) (x₀ : ∀ j, (s j).V) (hx : x₀ true ≠ 0) :
    Function.Surjective (tensorMap f hc s x₀) := by
  show Function.Surjective (tensorMap f hc s x₀).toLinearMap
  rw [← LinearMap.range_eq_top]
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  obtain ⟨a, ha⟩ := exists_smul_eq hc (s true) hx (y true)
  refine ⟨a • y false, ?_⟩
  have e1 : y = Function.update (Function.update x₀ false (y false)) true (a • x₀ true) := by
    funext j
    cases j <;> simp [ha]
  show (PiTensorProduct.tprod ℂ).toLinearMap x₀ false (a • y false) = PiTensorProduct.tprod ℂ y
  rw [map_smul, MultilinearMap.toLinearMap_apply]
  conv_rhs => rw [e1, MultilinearMap.map_update_smul]
  congr 2
  funext j
  cases j <;> simp

theorem isSubquotient_multiProd : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (r : ℕ) (c : Bool → ℕ) (f : (Σ j, Fin (c j)) ≃ Fin r)
    (s : ∀ j, IrrRep (GL (Fin (c j)) F)), c true = 0 → ∃ φ : Fin r ≃ Fin (c false),
      IsSubquotient (multiProd f fun j => (s j).ρ)
        ((s false).ρ.comp (reix F φ) : Representation ℂ (GL (Fin r) F) (s false).V) := by
  intro F _ _ _ _ r c f s hc
  haveI := nontrivial_of_irreducible (s true).irr
  obtain ⟨z, hz⟩ := exists_ne (0 : (s true).V)
  let x₀ : ∀ j, (s j).V := fun j => Bool.rec (motive := fun j => (s j).V) 0 z j
  refine ⟨(falseEquiv f hc).symm, ?_⟩
  exact (IsSubquotient.of_injective (evOne f hc _) (evOne_injective f hc _)).trans
    (IsSubquotient.of_surjective (tensorMap f hc s x₀) (tensorMap_surjective f hc s x₀ hz))

end GlobalTheory.EmptySecondBlockProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionEmptySecondIsSubquotientFirstStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicInduction_emptySecond_isSubquotient_first : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (r : ℕ) (c : Bool → ℕ) (f : (Σ j, Fin (c j)) ≃ Fin r) (s : ∀ j, IrrRep (GL (Fin (c j)) F)), c true = 0 → ∃ φ : Fin r ≃ Fin (c false), IsSubquotient (multiProd f fun j => (s j).ρ) ((s false).ρ.comp (reix F φ) : Representation ℂ (GL (Fin r) F) (s false).V) := by
  first | exact @GlobalTheory.EmptySecondBlockProd.isSubquotient_multiProd | exact GlobalTheory.EmptySecondBlockProd.isSubquotient_multiProd | (intros; apply GlobalTheory.EmptySecondBlockProd.isSubquotient_multiProd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientRepresentationTwoReindexings
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientRepresentationTwoReindexings
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LevelType

theorem reix_eq_conj (R : Type) [CommRing R] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (φ φ' : m ≃ n) : ∃ w : GL n R, ∀ g : GL m R, reix R φ g * w = w * reix R φ' g := by
  let e : n ≃ n := φ'.symm.trans φ
  have h1 : ((e.symm.toPEquiv.toMatrix : Matrix n n R) * e.toPEquiv.toMatrix) = 1 := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
  have h2 : ((e.toPEquiv.toMatrix : Matrix n n R) * e.symm.toPEquiv.toMatrix) = 1 := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
  let w : GL n R := ⟨e.symm.toPEquiv.toMatrix, e.toPEquiv.toMatrix, h1, h2⟩
  refine ⟨w, fun g => ?_⟩
  have key : (reix R φ g).val = w.val * (reix R φ' g).val * w⁻¹.val := by
    change _ = e.symm.toPEquiv.toMatrix * _ * e.toPEquiv.toMatrix
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext i j
    simp [val_reix, e]
  apply Units.ext
  rw [Units.val_mul, key, mul_assoc, Units.inv_mul, mul_one, Units.val_mul]

theorem subquotient_reix (R : Type) [CommRing R] (m n : Type) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (φ φ' : m ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL n R) V) :
    IsSubquotient (σ.comp (reix R φ) : Representation ℂ (GL m R) V) (σ.comp (reix R φ') : Representation ℂ (GL m R) V) := by
  obtain ⟨w, hw⟩ := reix_eq_conj R φ φ'
  refine IsSubquotient.of_surjective ⟨σ w, fun g => ?_⟩ fun v => ⟨σ w⁻¹ v, ?_⟩
  · change σ w * σ (reix R φ' g) = σ (reix R φ g) * σ w
    rw [← map_mul, ← map_mul, hw]
  · change σ w (σ w⁻¹ v) = v
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

end GlobalTheory.LevelType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientRepresentationTwoReindexingsStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSubquotientRepresentation_two_reindexings : ∀ (R : Type) [CommRing R] (m n : Type) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (φ φ' : m ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL n R) V), IsSubquotient (σ.comp (reix R φ) : Representation ℂ (GL m R) V) (σ.comp (reix R φ') : Representation ℂ (GL m R) V) := by
  first | exact @GlobalTheory.LevelType.subquotient_reix | exact GlobalTheory.LevelType.subquotient_reix | (intros; apply GlobalTheory.LevelType.subquotient_reix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetSubquotientFirstFactorOfEmptySecondBlock
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetSubquotientFirstFactorOfEmptySecondBlock
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EmptySecondBlock

section Reindex

variable {R : Type} [CommRing R] {t : ℕ} {c : Bool → ℕ}

def falseEquiv (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c true = 0) : Fin (c false) ≃ Fin t :=
  Equiv.ofBijective (fun i => f ⟨false, i⟩) ⟨fun i j h => by
    have := f.injective h
    simpa using this, fun x => by
    obtain ⟨⟨b, i⟩, rfl⟩ := f.surjective x
    cases b with
    | false => exact ⟨i, rfl⟩
    | true => exact absurd i.2 (by omega)⟩

theorem leviEmb_mulSingle (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c true = 0) (h : GL (Fin t) R) :
    leviEmb R f (Pi.mulSingle (M := fun j => GL (Fin (c j)) R) false (reix R (falseEquiv f hc).symm h)) = h := by
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := f.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := f.surjective y
  cases a with
  | true => exact absurd i.2 (by omega)
  | false =>
    cases b with
    | true => exact absurd j.2 (by omega)
    | false =>
      rw [leviEmb_apply_same]
      simp [val_reix, falseEquiv, Equiv.ofBijective]

end Reindex

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {c : Bool → ℕ}

theorem deltaHalf_eq_one (hc : c true = 0) (g : Levi k (fun j => Fin (c j))) :
    deltaHalf k (fun j => Fin (c j)) g = 1 := by
  haveI : IsEmpty (Fin (c true)) := by rw [hc]; infer_instance
  rw [deltaHalf_apply, Fintype.prod_bool]
  have h1 : modExp (fun j => Fin (c j)) false = 0 := by
    simp only [modExp, Finset.sum_filter, Fintype.sum_bool]
    simp [hc]
  have h2 : Matrix.GeneralLinearGroup.det (g true) = 1 := by
    ext; simp [Matrix.det_isEmpty]
  have h0 : absPow k 0 = 1 := by
    ext x; simp [val_absPow]
  rw [h1, h2]
  simp [h0]

end GlobalTheory.EmptySecondBlock

end

namespace GlobalTheory.EmptySecondBlock

open GlobalTheory.SmGL.DepthZero

theorem isSubquotient_comp' {G G' V W : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {π : Representation ℂ G V} (h : IsSubquotient σ π) (ψ : G' →* G) :
    IsSubquotient (σ.comp ψ : Representation ℂ G' W) (π.comp ψ : Representation ℂ G' V) := by
  obtain ⟨S, f, hf⟩ := h
  exact ⟨⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (ψ g) hv⟩,
    ⟨f.toLinearMap, fun g => f.isIntertwining' (ψ g)⟩, hf⟩

theorem isSubquotient_of_empty_second_block : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (r : ℕ) (c : Bool → ℕ) (f : (Σ j, Fin (c j)) ≃ Fin r) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin r) F) V) (s : ∀ j, IrrRep (GL (Fin (c j)) F)), c true = 0 → IsSubquotient (piTensor fun j => (s j).ρ) (GlobalTheory.SmGL.jac f π) → ∃ φ : Fin r ≃ Fin (c false), IsSubquotient ((s false).ρ.comp (reix F φ) : Representation ℂ (GL (Fin r) F) (s false).V) π := by
  intro F _ _ _ _ r c f V _ _ π s hc hsub
  refine ⟨(falseEquiv f hc).symm, ?_⟩
  let ι : GL (Fin r) F →* Levi F (fun j => Fin (c j)) :=
    (MonoidHom.mulSingle (fun j => GL (Fin (c j)) F) false).comp (reix F (falseEquiv f hc).symm)
  have hι : ∀ h, leviEmb F f (ι h) = h := fun h => leviEmb_mulSingle f hc h

  let q : π.IntertwiningMap ((GlobalTheory.SmGL.jac f π).comp ι) :=
    ⟨(twKer π (unipRad F f) 1).mkQ, fun h => by
      ext w
      show Submodule.Quotient.mk (π h w) = GlobalTheory.SmGL.jac f π (ι h) (Submodule.Quotient.mk w)
      rw [jac_mk, deltaHalf_eq_one hc, inv_one, Units.val_one, one_smul, hι]⟩
  have h3 : IsSubquotient ((GlobalTheory.SmGL.jac f π).comp ι) π :=
    IsSubquotient.of_surjective q (Submodule.mkQ_surjective _)
  have h2 := isSubquotient_comp' hsub ι

  haveI := nontrivial_of_irreducible (s true).irr
  obtain ⟨w0, hw0⟩ := exists_ne (0 : (s true).V)
  obtain ⟨ψ0, hψ0⟩ : ∃ ψ0 : Module.Dual ℂ (s true).V, ψ0 w0 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw0 ((Module.forall_dual_apply_eq_zero_iff ℂ w0).1 h)
  let ψ : ∀ j, (s j).V →ₗ[ℂ] ℂ := fun j => Bool.rec (motive := fun j => (s j).V →ₗ[ℂ] ℂ) 0 ((ψ0 w0)⁻¹ • ψ0) j
  let K : Representation.IntertwiningMap ((piTensor fun j => (s j).ρ).comp ι : Representation ℂ (GL (Fin r) F) _)
      ((s false).ρ.comp (reix F (falseEquiv f hc).symm) : Representation ℂ (GL (Fin r) F) _) :=
    ⟨contract ψ false, fun h => by
      refine LinearMap.ext fun t => ?_
      exact contract_piTensor (fun j => (s j).ρ) ψ false (reix F (falseEquiv f hc).symm h) t⟩
  have hK : Function.Surjective K := fun y => by
    let x : ∀ j, (s j).V := fun j => Bool.rec (motive := fun j => (s j).V) y w0 j
    refine ⟨PiTensorProduct.tprod ℂ x, ?_⟩
    show contract ψ false (PiTensorProduct.tprod ℂ x) = y
    rw [contract_tprod]
    have : Finset.univ.erase false = {true} := by decide
    rw [this, Finset.prod_singleton]
    show ((ψ0 w0)⁻¹ • ψ0) w0 • y = y
    rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hψ0, one_smul]
  exact (IsSubquotient.of_surjective K hK).trans (h2.trans h3)

end GlobalTheory.EmptySecondBlock
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetSubquotientFirstFactorOfEmptySecondBlockStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetSubquotient_firstFactor_of_emptySecondBlock : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (r : ℕ) (c : Bool → ℕ) (f : (Σ j, Fin (c j)) ≃ Fin r) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin r) F) V) (s : ∀ j, IrrRep (GL (Fin (c j)) F)), c true = 0 → IsSubquotient (piTensor fun j => (s j).ρ) (jac f π) → ∃ φ : Fin r ≃ Fin (c false), IsSubquotient ((s false).ρ.comp (reix F φ) : Representation ℂ (GL (Fin r) F) (s false).V) π := by
  first | exact @GlobalTheory.EmptySecondBlock.isSubquotient_of_empty_second_block | exact GlobalTheory.EmptySecondBlock.isSubquotient_of_empty_second_block | (intros; apply GlobalTheory.EmptySecondBlock.isSubquotient_of_empty_second_block <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleHarishChandraOfStdTraceNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleHarishChandraOfStdTraceNeZero
noncomputable section

namespace GlobalTheory.GLq.StdRes

open GlobalTheory.GLq GlobalTheory.LevelType Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

variable {p : ℕ} [Fact p.Prime]

theorem stdBlock_iff (a c : ℕ) (x : Gn p (a + 1 + c)) :
    StdBlock a x ↔ InPar (a + 1) (x : Mt p (a + 1 + c)) ∧ br (a + 1) c (x : Mt p (a + 1 + c)) = 1 ∧
      ∀ i j : Fin (a + 1), (j : ℕ) < a → tl (a + 1) (x : Mt p (a + 1 + c)) i j = if i = j then 1 else 0 := by
  constructor
  · intro h
    refine ⟨fun i j hj hi => ?_, ?_, fun i j hj => ?_⟩
    · rw [h i j (by omega), if_neg]
      intro e; subst e; omega
    · ext i j
      simp only [br, entN]
      rw [dite_eq_left (by omega), h _ _ (by simp; omega)]
      simp [Matrix.one_apply, Fin.ext_iff]
    · simp only [tl, entN]
      rw [dite_eq_left (by omega), h _ _ (by simp; omega)]
      simp [Fin.ext_iff]
  · rintro ⟨h1, h2, h3⟩ i j hij
    by_cases hi : (i : ℕ) ≤ a
    · have hj : (j : ℕ) < a := by omega
      have := h3 ⟨i, by omega⟩ ⟨j, by omega⟩ hj
      simp only [tl, entN] at this
      rw [dite_eq_left (by omega)] at this
      simpa [Fin.ext_iff] using this
    · by_cases hj : (j : ℕ) < a + 1
      · rw [h1 i j hj (by omega), if_neg]
        intro e; subst e; omega
      · have := congrFun (congrFun h2 ⟨(i : ℕ) - (a + 1), by omega⟩) ⟨(j : ℕ) - (a + 1), by omega⟩
        simp only [br, entN] at this
        rw [dite_eq_left (by omega)] at this
        have ei : (⟨a + 1 + ((i : ℕ) - (a + 1)), by omega⟩ : Fin (a + 1 + c)) = i := Fin.ext (by simp; omega)
        have ej : (⟨a + 1 + ((j : ℕ) - (a + 1)), by omega⟩ : Fin (a + 1 + c)) = j := Fin.ext (by simp; omega)
        rw [ei, ej, Matrix.one_apply] at this
        rw [this]
        simp only [Fin.ext_iff]
        congr 1
        apply propext
        omega

theorem isUnit_tl (a c : ℕ) (x : Gn p (a + 1 + c)) (h1 : InPar (a + 1) (x : Mt p (a + 1 + c)))
    (h2 : br (a + 1) c (x : Mt p (a + 1 + c)) = 1) : IsUnit (tl (a + 1) (x : Mt p (a + 1 + c))) := by
  have := LabelDet.det_inPar (a + 1) c (x : Mt p (a + 1 + c)) h1
  rw [h2, Matrix.det_one, mul_one] at this
  exact (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit (this ▸ x.det_ne_zero))

theorem val_toG {n : ℕ} (M : Mt p n) (h : IsUnit M) : ((toG M : Gn p n) : Mt p n) = M := by
  unfold toG
  rw [dite_eq_left h]
  rfl

end GlobalTheory.GLq.StdRes

namespace GlobalTheory.GLq.StdRes

open GlobalTheory.GLq GlobalTheory.LevelType Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

variable {p : ℕ} [Fact p.Prime]

theorem stdTrace_eq (a c : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (ψ : Gn p (a + 1 + c) → ℂ) :
    stdTrace a θ ψ = (p : ℂ) ^ ((a + 1) * c) * ∑ y : Gn p (a + 1),
      if StdBlock a y then (((θ (Matrix.GeneralLinearGroup.det y))⁻¹ : ℂˣ) : ℂ) * res (a + 1) c ψ y 1 else 0 := by
  have hp0 : (p : ℂ) ^ ((a + 1) * c) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have e1 : (p : ℂ) ^ ((a + 1) * c) * (∑ y : Gn p (a + 1),
      if StdBlock a y then (((θ (Matrix.GeneralLinearGroup.det y))⁻¹ : ℂˣ) : ℂ) * res (a + 1) c ψ y 1 else 0) =
      ∑ y : Gn p (a + 1), ∑ x : Gn p (a + 1 + c),
        if StdBlock a y ∧ (InPar (a + 1) (x : Mt p (a + 1 + c)) ∧ tl (a + 1) (x : Mt p (a + 1 + c)) = (y : Mt p (a + 1)) ∧
          br (a + 1) c (x : Mt p (a + 1 + c)) = ((1 : Gn p c) : Mt p c)) then
          (((θ (Matrix.GeneralLinearGroup.det y))⁻¹ : ℂˣ) : ℂ) * ψ x else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    unfold res
    by_cases hy : StdBlock a y
    · rw [if_pos hy, mul_left_comm, mul_inv_cancel_left₀ hp0, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [hy, true_and, mul_ite, mul_zero]
    · simp [hy]
  rw [e1, Finset.sum_comm]
  unfold stdTrace
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : InPar (a + 1) (x : Mt p (a + 1 + c)) ∧ br (a + 1) c (x : Mt p (a + 1 + c)) = 1
  · have hu := isUnit_tl a c x hx.1 hx.2
    have hy0 := val_toG _ hu
    rw [Finset.sum_eq_single (toG (tl (a + 1) (x : Mt p (a + 1 + c))))]
    · have hs : StdBlock a x ↔ StdBlock a (toG (tl (a + 1) (x : Mt p (a + 1 + c)))) := by
        rw [stdBlock_iff]
        unfold StdBlock
        rw [hy0]
        constructor
        · rintro ⟨-, -, h⟩ i j hij
          exact h i j (by have := i.isLt; omega)
        · intro h
          exact ⟨hx.1, hx.2, fun i j hj => h i j (by omega)⟩
      have hd : Matrix.GeneralLinearGroup.det x =
          Matrix.GeneralLinearGroup.det (toG (tl (a + 1) (x : Mt p (a + 1 + c)))) := by
        rw [LabelDet.det_par (a + 1) c x hx.1, hx.2, LabelDet.toG_one, map_one, mul_one]
      by_cases h : StdBlock a x
      · rw [if_pos h, if_pos ⟨hs.1 h, hx.1, hy0.symm, by simpa using hx.2⟩, hd]
      · rw [if_neg h, if_neg (fun e => h (hs.2 e.1))]
    · intro y _ hne
      rw [if_neg]
      rintro ⟨-, -, h, -⟩
      exact hne (Units.ext (h.symm.trans hy0.symm))
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg (fun h => hx ⟨((stdBlock_iff a c x).1 h).1, ((stdBlock_iff a c x).1 h).2.1⟩), eq_comm]
    refine Finset.sum_eq_zero fun y _ => if_neg ?_
    rintro ⟨-, h1, -, h3⟩
    exact hx ⟨h1, by simpa using h3⟩

end GlobalTheory.GLq.StdRes

namespace GlobalTheory.GLq.StdRes

open GlobalTheory.GLq GlobalTheory.LevelType Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

theorem sum_list_comm {ι X : Type} [Fintype ι] (L : List X) (f : ι → X → ℂ) :
    ∑ i, (L.map (f i)).sum = (L.map fun q => ∑ i, f i q).sum := by
  induction L with
  | nil => simp
  | cons q L ih => simp [Finset.sum_add_distrib, ih]

theorem list_sum_nat (l : List ℂ) (h : ∀ z ∈ l, ∃ n : ℕ, z = n) :
    (∃ n : ℕ, l.sum = n) ∧ ∀ z ∈ l, z ≠ 0 → ∃ n : ℕ, l.sum = n + 1 := by
  induction l with
  | nil => exact ⟨⟨0, by simp⟩, by simp⟩
  | cons z l ih =>
    obtain ⟨⟨k, hk⟩, H⟩ := ih fun w hw => h w (List.mem_cons_of_mem _ hw)
    obtain ⟨m, hm⟩ := h z List.mem_cons_self
    refine ⟨⟨m + k, by rw [List.sum_cons, hk, hm]; push_cast; ring⟩, fun w hw hw0 => ?_⟩
    rcases List.mem_cons.1 hw with rfl | hw
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by
        have : m ≠ 0 := by rintro rfl; exact hw0 (by simpa using hm)
        omega⟩
      exact ⟨m' + k, by rw [List.sum_cons, hk, hm]; push_cast; ring⟩
    · obtain ⟨k', hk'⟩ := H w hw hw0
      exact ⟨m + k', by rw [List.sum_cons, hk', hm]; push_cast; ring⟩

theorem isClass_of_isChar {G : Type} [Group G] {χ : G → ℂ} (h : IsChar χ) : IsClass χ := by
  obtain ⟨V, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

theorem ip_nat {G : Type} [Group G] [Fintype G] {α β : G → ℂ} (hα : IsChar α) (hβ : IsChar β) :
    ∃ n : ℕ, ip α β = n := by
  obtain ⟨W, hW⟩ := hα
  obtain ⟨V, hV⟩ := hβ
  refine ⟨Module.finrank ℂ (V ⟶ W), ?_⟩
  rw [← FDRep.scalar_product_char_eq_finrank_equivariant]
  unfold ip
  rw [Fintype.card_eq_nat_card]
  simp [hW, hV]

theorem ip_self {G : Type} [Group G] [Fintype G] {α : G → ℂ} (hα : IsIrr α) : ip α α = 1 := by
  obtain ⟨V, hs, hV⟩ := hα
  haveI := hs
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  have := FDRep.char_orthonormal V V
  rw [if_pos ⟨CategoryTheory.Iso.refl _⟩] at this
  unfold ip
  rw [Fintype.card_eq_nat_card]
  simpa [hV] using this

theorem isChar_of_isIrr {G : Type} [Group G] {α : G → ℂ} (h : IsIrr α) : IsChar α := by
  obtain ⟨V, -, hV⟩ := h
  exact ⟨V, hV⟩

end GlobalTheory.GLq.StdRes

namespace GlobalTheory.LevelType

open GlobalTheory.GLq GlobalTheory.GLq.StdRes Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

theorem exists_irr_hc_of_stdTrace_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (r a c : ℕ) (θ : (ZMod p)ˣ →* ℂˣ)
    (ψ : GlobalTheory.GLq.Gn p r → ℂ), r = a + 1 + c → GlobalTheory.GLq.IsChar ψ → stdTrace a θ ψ ≠ 0 →
    ∃ (α : GlobalTheory.GLq.Gn p (a + 1) → ℂ) (β : GlobalTheory.GLq.Gn p c → ℂ), GlobalTheory.GLq.IsIrr α ∧ GlobalTheory.GLq.IsIrr β ∧
      GlobalTheory.GLq.ip ψ (GlobalTheory.GLq.hc (a + 1) c α β r) ≠ 0 ∧ stdTrace a θ α ≠ 0 := by
  intro p _ r a c θ ψ hr hψ hne
  subst hr
  obtain ⟨L, hLirr, hL⟩ := (HCChar.hc_isChar_and_res_decomp p (a + 1) c (a + 1 + c) rfl).2 ψ hψ
  obtain ⟨q, hq, hqt⟩ : ∃ q ∈ L, stdTrace a θ q.1 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hne
    rw [stdTrace_eq]
    have e1 : (∑ y : Gn p (a + 1), if StdBlock a y then
        (((θ (Matrix.GeneralLinearGroup.det y))⁻¹ : ℂˣ) : ℂ) * res (a + 1) c ψ y 1 else 0) =
        ∑ y : Gn p (a + 1), (L.map fun q => if StdBlock a y then
          (((θ (Matrix.GeneralLinearGroup.det y))⁻¹ : ℂˣ) : ℂ) * (q.1 y * q.2 1) else 0).sum := by
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [hL]
      by_cases hy : StdBlock a y
      · simp only [hy, if_true]
        rw [List.sum_map_mul_left]
      · simp [hy]
    rw [e1, sum_list_comm, List.sum_eq_zero, mul_zero]
    intro z hz
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hz
    have := hcon q hq
    unfold stdTrace at this
    calc (∑ y : Gn p (a + 1), if StdBlock a y then
          (((θ (Matrix.GeneralLinearGroup.det y))⁻¹ : ℂˣ) : ℂ) * (q.1 y * q.2 1) else 0)
        = (∑ y : Gn p (a + 1), if StdBlock a y then
          (((θ (Matrix.GeneralLinearGroup.det y))⁻¹ : ℂˣ) : ℂ) * q.1 y else 0) * q.2 1 := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun y _ => ?_
          split_ifs
          · ring
          · simp
      _ = 0 := by rw [this, zero_mul]
  refine ⟨q.1, q.2, (hLirr q hq).1, (hLirr q hq).2, ?_, hqt⟩
  rw [hc, FrobRecHC.hcT_adjoint p (a + 1) c (a + 1 + c) rfl ψ _ (isClass_of_isChar hψ)]
  have e : ip (fun pr : Gn p (a + 1) × Gn p c => res (a + 1) c ψ pr.1 pr.2) (fun pr => q.1 pr.1 * q.2 pr.2) =
      (L.map fun q' => ip q'.1 q.1 * ip q'.2 q.2).sum := by
    unfold ip
    rw [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type]
    simp only [hL, Prod.fst_inv, Prod.snd_inv]
    have hs : ∀ (x : Gn p (a + 1)) (y : Gn p c), (L.map fun q' => q'.1 x * q'.2 y).sum * (q.1 x⁻¹ * q.2 y⁻¹) =
        (L.map fun q' => q'.1 x * q'.2 y * (q.1 x⁻¹ * q.2 y⁻¹)).sum := fun x y => by rw [List.sum_map_mul_right]
    simp only [hs]
    rw [Finset.sum_congr rfl fun x _ => sum_list_comm L fun y q' => q'.1 x * q'.2 y * (q.1 x⁻¹ * q.2 y⁻¹),
      sum_list_comm, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro q' _
    rw [mul_inv, mul_mul_mul_comm, Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [e]
  have hnat : ∀ z ∈ L.map (fun q' => ip q'.1 q.1 * ip q'.2 q.2), ∃ n : ℕ, z = n := by
    intro z hz
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hz
    obtain ⟨m, hm⟩ := ip_nat (isChar_of_isIrr (hLirr q' hq').1) (isChar_of_isIrr (hLirr q hq).1)
    obtain ⟨k, hk⟩ := ip_nat (isChar_of_isIrr (hLirr q' hq').2) (isChar_of_isIrr (hLirr q hq).2)
    exact ⟨m * k, by rw [hm, hk]; push_cast; ring⟩
  obtain ⟨n, hn⟩ := (list_sum_nat _ hnat).2 _ (List.mem_map_of_mem hq)
    (by show ip q.1 q.1 * ip q.2 q.2 ≠ 0; rw [ip_self (hLirr q hq).1, ip_self (hLirr q hq).2]; norm_num)
  rw [hn]
  exact_mod_cast Nat.succ_ne_zero n

end GlobalTheory.LevelType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleHarishChandraOfStdTraceNeZeroStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irreducible_harishChandra_of_stdTrace_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (r a c : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (ψ : GlobalTheory.GLq.Gn p r → ℂ), r = a + 1 + c → GlobalTheory.GLq.IsChar ψ → stdTrace a θ ψ ≠ 0 → ∃ (α : GlobalTheory.GLq.Gn p (a + 1) → ℂ) (β : GlobalTheory.GLq.Gn p c → ℂ), GlobalTheory.GLq.IsIrr α ∧ GlobalTheory.GLq.IsIrr β ∧ GlobalTheory.GLq.ip ψ (GlobalTheory.GLq.hc (a + 1) c α β r) ≠ 0 ∧ stdTrace a θ α ≠ 0 := by
  first | exact @GlobalTheory.LevelType.exists_irr_hc_of_stdTrace_ne_zero | exact GlobalTheory.LevelType.exists_irr_hc_of_stdTrace_ne_zero | (intros; apply GlobalTheory.LevelType.exists_irr_hc_of_stdTrace_ne_zero <;> assumption)
end
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BlockTypeSplit

open ValuativeRel Polynomial

section Finite

theorem isRoot_of_parVec {p : ℕ} [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) {r : ℕ} {α : Type} [Fintype α] [LinearOrder α]
    {m : α → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ Fin r) (a : α)
    {θ : (ZMod p)ˣ →* ℂˣ} {u : ZMod p} {f : (ZMod p)[X]} (ρ : FDRep ℂ (GL (Fin r) (ZMod p))) (hρ : CategoryTheory.Simple ρ)
    (hf : GlobalTheory.GLq.HasLabel L (fun x => ρ.character x) f) (hθ : GlobalTheory.GLp.IsCharLab L θ u) (ha : Fintype.card (m a) = 1)
    {v : ρ} (hv : v ≠ 0) (h : ParVec ρ.ρ e a θ v) : f.IsRoot u := by
  obtain ⟨c, v', hc, hv', hs⟩ := GlobalTheory.T.exists_standardTypeVector_of_parabolicTypeVector p r α m e a θ _ ρ.ρ v ha hv h
  have ht := GlobalTheory.T.stdParabolicTwistedTraceSum_ne_zero_of_vector p r c θ ρ v' hv' hs
  have hr : r = c + 1 + (r - c - 1) := by omega
  obtain ⟨A, B, hA, hB, h1, h2⟩ := GlobalTheory.T.exists_irreducible_harishChandra_of_stdTrace_ne_zero p r c (r - c - 1) θ ρ.character hr ⟨ρ, fun _ => rfl⟩ ht
  obtain ⟨σ, hσ, h3⟩ := GlobalTheory.T.exists_irreducible_detTwist_of_stdTrace_twoBlock p c θ A hA h2
  exact GlobalTheory.T.thetaLabel_root_of_harishChandraConstituent p L r c _ θ u f _ A B σ hr ⟨ρ, hρ, fun _ => rfl⟩ hA hB hσ hf hθ h1 h3

end Finite

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem isSubquotient_jac_two {a b n V W : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n]
    [DecidableEq n] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : a ⊕ b ≃ n)
    {π : Representation ℂ (GL n F) V} {τ : Representation ℂ (GL n F) W} (hτ : IsSmooth τ) (h : IsSubquotient π τ) :
    IsSubquotient (GlobalTheory.SmGL.jac (two e) π) (GlobalTheory.SmGL.jac (two e) τ) := by
  obtain ⟨S, f, hf⟩ := h
  let ι : S.toRepresentation.IntertwiningMap τ := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  refine (IsSubquotient.of_surjective (jacMap (two e) f) fun y => ?_).trans (.of_injective (jacMap (two e) ι) ?_)
  · obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨v, rfl⟩ := hf w
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : ι v ∈ twKer τ (unipRad F (two e)) 1 := (Submodule.Quotient.mk_eq_zero _).1 hx
    have hN := GlobalTheory.InertSupp.unipRad_eq_unipOf F (e := two e) (c := fun i => ((blk (two e) i).toNat : ℤ))
      fun i j => by cases blk (two e) i <;> cases blk (two e) j <;> simp
    obtain ⟨T, hT, h2⟩ := GlobalTheory.JacquetExact.exists_finset_of_mem_twKer h1
    obtain ⟨H, hle, hH, hSH⟩ := GlobalTheory.UnipCompact.exists_compact_subgroup F n _ T (hN ▸ hT)
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    exact GlobalTheory.IwahoriInj.twKer_mono (hle.trans hN.ge)
      (GlobalTheory.JacquetExact.mem_twKer_of_compact hτ ι Subtype.val_injective hH (h2 H hSH))

variable {p : ℕ} [Fact p.Prime] {r t : ℕ}

theorem typeVec_first {X : Bool → Type} [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)]
    (ρ : ∀ j, Representation ℂ (GL (Two (Fin r) (Fin t) j) F) (X j)) (hρ : ∀ j, IsSmooth (ρ j))
    {Y : Type} [AddCommGroup Y] [Module ℂ Y] {τ : Representation ℂ (Levi F (Two (Fin r) (Fin t))) Y}
    (h : IsSubquotient τ (piTensor ρ)) {z : MonoidAlgebra ℂ (GL (Fin r) (ZMod p))} {w : Y}
    (hw : TypeVec (n := Fin r) (τ.comp (MonoidHom.mulSingle (fun j => GL (Two (Fin r) (Fin t) j) F) false)) z w) :
    ∃ x, TypeVec (n := Fin r) (ρ false) z x := by
  obtain ⟨y, hy⟩ := TypeVec.up (n := Fin r)
    (π := (piTensor ρ).comp (MonoidHom.mulSingle (fun j => GL (Two (Fin r) (Fin t) j) F) false))
    (isSmooth_comp (isSmooth_piTensor hρ) _ (continuous_mulSingle (A := fun j => GL (Two (Fin r) (Fin t) j) F) false))
    (GlobalTheory.CuspRep.ParLaws.isSubquotient_comp h _) hw
  exact TypeVec.factor (m := Two (Fin r) (Fin t)) ρ false hy

theorem typeVec_iff {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin r) F) W)
    (z : MonoidAlgebra ℂ (GL (Fin r) (ZMod p))) (y : W) (h : TypeVec π z y) : IsLevelOne π y ∧ NotKilled π z y := by
  obtain ⟨h1, ℓ, hℓ, h0⟩ := h
  refine ⟨fun h hh => h1 h (GlobalTheory.StepData.mem_KOne.2 fun a b => ?_), ℓ, fun g a b => ?_, h0⟩
  · simpa [Matrix.one_apply] using hh a b
  · rw [dite_eq_left ⟨a.2, b.2⟩]
    exact hℓ g a b

end Local

theorem hasLabelO_of_mul {p : ℕ} [Fact p.Prime] {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod p)}
    (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod p) C) {r : ℕ} (ρ : FDRep ℂ (GL (Fin r) (ZMod p))) (hρ : CategoryTheory.Simple ρ)
    {f : (ZMod p)[X]} (h0 : Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ ≠ 0)
    (h : Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ * Formalism.L2.NT.eSerO O r f = Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) : Formalism.IrreducibleCountingLemmas.TYPES.HasLabelO O ρ f := by
  classical
  rw [GlobalTheory.SerOSys.eSerO_eq_sum, Finset.mul_sum] at h
  obtain ⟨z, hz, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h.trans_ne h0)
  obtain ⟨τ, hτ, rfl, hl⟩ := (GlobalTheory.SerOSys.Zl_finite O r f).mem_toFinset.1 hz
  refine GlobalTheory.SerOSys.hasLabelO_of_repIso O hl (GlobalTheory.SerOSys.repIso_of_zIdem_eq ρ τ hρ hτ ?_)
  by_contra e
  exact hne (GlobalTheory.SerOSys.zIdem_mul_eq_zero ρ τ hρ hτ e)

theorem exists_hasLabel {p : ℕ} [Fact p.Prime] (t : Formalism.CyclotomicNorms.Fbar p →* ℂ)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar p, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar p) (hζ : Formalism.L2.NT.IsGenSys ζ)
    (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod p) (Formalism.L2.NT.convC t ht ζ hζ))
    (hO : ∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) (ZMod p))), 1 ≤ d → CategoryTheory.Simple τ →
      Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod p) τ → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (Formalism.L2.NT.convC t ht ζ hζ) τ (O.lab d τ))
    {r : ℕ} (ρ : FDRep ℂ (GL (Fin r) (ZMod p))) (hρ : CategoryTheory.Simple ρ) {f : (ZMod p)[X]}
    (h0 : Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ ≠ 0)
    (h : Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ * Formalism.L2.NT.eSerO O r f = Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) :
    ∃ L : GlobalTheory.GLq.LabelDatum p, L.teich = t ∧ L.gen = ζ ∧ GlobalTheory.GLq.HasLabel L (fun x => ρ.character x) f := by
  let L : GlobalTheory.GLq.LabelDatum p := ⟨t, ht, ζ, fun d hd => (hζ d hd).1,
    fun d e hd he => (hζ d hd).2 (d * e) (dvd_mul_right d e) (Nat.mul_pos hd he)⟩
  exact ⟨L, rfl, rfl, GlobalTheory.T.classFunctionLabel_of_labelMap_label p L O (fun d V hd hs hc => GlobalTheory.T.isCuspidalCharacterOfPolynomial_of_cuspidalLabel p L t ht hζ rfl d V _ hd
    ((GlobalTheory.T.isCuspidalCharacter_iff_isCuspidal_GLnFiniteField p d V hd hs).2 hc) (hO d V hd hs hc)) (GlobalTheory.T.trace_harishChandra_induced_eq_product_characters p) (GlobalTheory.T.isConstituent_harishChandraRep_iff_pairing_ne_zero p) r ρ f hρ
    (hasLabelO_of_mul O ρ hρ h0 h)⟩


end GlobalTheory.BlockTypeSplit

end
