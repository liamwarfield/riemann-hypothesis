module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.KIface
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.FiniteDimensionalTranslationCoordinates
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.NonzeroTypeTheory

def Need_CMain : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (G : Grp k n)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V), IsSmooth ρ → ρ.IsIrreducible →
    (∃ x : V, x ≠ 0 ∧ ∀ g ∈ G.JSet, ρ g x = G.lam g • x) → IsTwSphProd ρ G.d G.hd G.μ

def Need_CProps : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (G : Grp k n),
    G.JSet ⊆ KO k (Fin n) ∧ (1 : GL (Fin n) k) ∈ G.JSet ∧
    (∀ g ∈ G.JSet, ∀ g' ∈ G.JSet, g * g' ∈ G.JSet ∧ G.lam (g * g') = G.lam g * G.lam g') ∧
    (∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet) ∧ (∀ g ∈ G.JSet, G.lam g ≠ 0) ∧
    IsOpen (KC k n G.lev) ∧ (1 : GL (Fin n) k) ∈ KC k n G.lev ∧ KC k n G.lev ⊆ G.JSet ∧ (∀ g ∈ KC k n G.lev, G.lam g = 1) ∧
    (∀ φ ∈ G.V0sp, ∀ k' : ↥(KO k (Fin n)), rightReg ℂ ↥(KO k (Fin n)) ℂ k' φ ∈ G.V0sp) ∧ FiniteDimensional ℂ G.V0sp ∧
    G.v0 ∈ G.V0sp ∧ G.v0 ≠ 0 ∧
    ∀ j : ↥(KO k (Fin n)), (j : GL (Fin n) k) ∈ G.JSet → rightReg ℂ ↥(KO k (Fin n)) ℂ j G.v0 = G.lam j • G.v0

def Need_Grp : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (μ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (μ i)) →
    ∃ (G : Grp k n) (σ : Fin n ≃ Fin n), ∀ i, res (G.chi i) = res (μ (σ i))

def ArtinTransferDecompositionCharacter : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a →
    ∀ (n : ℕ) (χ : Fin n → Dec (F := E) A →* ℂˣ), (∀ i, IsOpen ((χ i).ker : Set (Dec (F := E) A))) →
      ∃ μ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ, (∀ i, IsSmoothChar (μ i)) ∧
        ∀ i (σ : Weil h), χ i (Subgroup.inclusion (Weil_le_Dec h) σ) = μ i (a σ)

def LocalArtinCharacterProduct : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a →
    ∀ (n : ℕ) (χ : Fin n → Dec (F := E) A →* ℂˣ) (ho : ∀ i, IsOpen ((χ i).ker : Set (Dec (F := E) A)))
      (μ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ), (∀ i (σ : Weil h), χ i (Subgroup.inclusion (Weil_le_Dec h) σ) = μ i (a σ)) →
      ∀ (G : Grp (w.adicCompletion E) n) (σ : Fin n ≃ Fin n), (∀ i, res (G.chi i) = res (μ (σ i))) →
        ∀ s : ↥(Ine (F := E) A), (xOf h χ ho).charPol (ineIncl h s) =
          ∏ b, (X - C (((G.μ b (a (ineIncl h s))) : ℂˣ) : ℂ)) ^ G.d b

def FiniteDimensionalTranslationCoordinates : Prop :=
  ∀ (K : Type) [Group K] [TopologicalSpace K] (W : Submodule ℂ (K → ℂ)), FiniteDimensional ℂ W →
    (∀ φ ∈ W, ∀ k : K, rightReg ℂ K ℂ k φ ∈ W) → (∀ φ ∈ W, IsOpen {k : K | rightReg ℂ K ℂ k φ = φ}) →
    ∃ (m : ℕ) (V0 : Representation ℂ K (Fin m → ℂ)) (e : (Fin m → ℂ) →ₗ[ℂ] (K → ℂ)),
      Function.Injective e ∧ LinearMap.range e = W ∧ (∀ k v, e (V0 k v) = rightReg ℂ K ℂ k (e v)) ∧ IsSmooth V0

def TwistedSphericalRepresentative : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V) (h1 : IsSmooth ρ) (h2 : ρ.IsIrreducible)
    (s : ℕ) (d : Fin s → ℕ) (hd : ∑ a, d a = n) (η : Fin s → kˣ →* ℂˣ),
    IsTwSphProd (IrrGL.of ρ h1 h2).rep d hd η ↔ IsTwSphProd ρ d hd η

def DistinctOnUnitsDistinctOnInertia : Prop :=
  ArtinInertiaProp →
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a →
    ∀ (n : ℕ) (G : Grp (w.adicCompletion E) n) (b c : Fin G.s), b ≠ c →
      ∃ t : ↥(Ine (F := E) A), G.μ b (a (ineIncl h t)) ≠ G.μ c (a (ineIncl h t))

def SmoothVectorsFixedByCongruence : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (G : Grp k n),
    IsOpen (KC k n G.lev) → (1 : GL (Fin n) k) ∈ KC k n G.lev →
    ∀ φ ∈ G.V0sp, IsOpen {k' : ↥(KO k (Fin n)) | rightReg ℂ ↥(KO k (Fin n)) ℂ k' φ = φ}

end UpperTheory.NonzeroTypeTheory
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CJDefs
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Grp

variable {n : ℕ} (G : Grp k n)

def HasEtaVec {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a : Fin G.s => Fin (G.d a)) W) :
    Prop :=
  ∃ y : W, y ≠ 0 ∧ ∀ m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a)), ρ m y = G.eta m • y

def JacquetModuleFiniteProp : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible → IsSmooth (jacU G.e π) ∧ HasFiniteLength (jacU G.e π)

def SubquotientProp : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a : Fin G.s => Fin (G.d a)) W),
    IsSmooth ρ → HasFiniteLength ρ → G.HasEtaVec ρ →
    ∃ (X : Type) (_ : AddCommGroup X) (_ : Module ℂ X) (σ : Representation ℂ (Levi k fun a : Fin G.s => Fin (G.d a)) X),
      IsSmooth σ ∧ σ.IsIrreducible ∧ IsSubquotient σ ρ ∧ G.HasEtaVec σ

def TensorProductProp : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ (Levi k fun a : Fin G.s => Fin (G.d a)) X),
    IsSmooth σ → σ.IsIrreducible → G.HasEtaVec σ →
    ∃ (Y : Fin G.s → Type) (_ : ∀ a, AddCommGroup (Y a)) (_ : ∀ a, Module ℂ (Y a))
      (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)),
      (∀ a, IsSmooth (τ a)) ∧ (∀ a, (τ a).IsIrreducible) ∧ (∀ a, HasDetVec (τ a) (G.μ a)) ∧
        Nonempty (σ.Equiv (piTensor τ))

def SupportOfProductProp : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible →
    ∀ (Y : Fin G.s → Type) [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)),
      (∀ a, IsSmooth (τ a)) → (∀ a, (τ a).IsIrreducible) → (∀ a, HasDetVec (τ a) (G.μ a)) →
      IsSubquotient (piTensor τ) (jacU G.e π) → IsTwSphProd π G.d G.hd G.μ

def ExistsGroupElementProp : Prop :=
  ∀ (n : ℕ) (χ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (χ i)) →
    ∃ (G : Grp k n) (σ : Equiv.Perm (Fin n)), ∀ i, res (χ (σ i)) = res (G.chi i)

end Grp

end UpperTheory.TNZ
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CuspidalSupport2
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.CuspidalSupport₂

variable {k : Type} [Field k]

theorem twist_detRep_one (χ η : kˣ →* ℂˣ) :
    twist (detRep (Fin 1) χ) (detChar (Fin 1) η) = detRep (Fin 1) (η * χ) := by
  have h : GlobalTheory.SmGL.detChar (Fin 1) η * GlobalTheory.SmGL.detChar (Fin 1) χ =
      GlobalTheory.SmGL.detChar (R := k) (Fin 1) (η * χ) := by
    refine MonoidHom.ext fun g => ?_
    simp only [MonoidHom.mul_apply, GlobalTheory.SmGL.detChar_apply]
  unfold GlobalTheory.SmGL.detRep GlobalTheory.SmGL.ofChar
  rw [GlobalTheory.SmGL.twist_twist, h]

theorem twist_twist_inv {d : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]
    (σ : Representation ℂ (GL (Fin d) k) X) (η : kˣ →* ℂˣ) :
    twist (twist σ (detChar (Fin d) η⁻¹)) (detChar (Fin d) η) = σ := by
  have h : GlobalTheory.SmGL.detChar (Fin d) η * GlobalTheory.SmGL.detChar (Fin d) η⁻¹ =
      (1 : GL (Fin d) k →* ℂˣ) := by
    refine MonoidHom.ext fun g => ?_
    simp only [MonoidHom.mul_apply, GlobalTheory.SmGL.detChar_apply, MonoidHom.inv_apply,
      mul_inv_cancel, MonoidHom.one_apply]
  rw [GlobalTheory.SmGL.twist_twist, h, GlobalTheory.SmGL.twist_one]

end UpperTheory.TNZ.CuspidalSupport₂

namespace UpperTheory.TNZ

open CuspidalSupport₂ in
theorem step_cuspSupp : CuspidalSupportProp := by
  intro hL k _ _ _ _ d X _ _ σ hs hi η hη hdv
  obtain ⟨v, hv0, hv⟩ := hdv
  set τ := twist σ (detChar (Fin d) η⁻¹) with hτ
  have hτs : IsSmooth τ := isSmooth_twist hs hη.inv.detChar
  have hτi : τ.IsIrreducible := isIrreducible_twist hi _
  have hadm : IsAdmissible τ := (hL.bz k).1 (Fin d) X τ hτs hτi
  have hI : fixed τ (iwahori k (Fin d)) ≠ ⊥ := by
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩
    have hg := hv h.1 (iwahori_le_KO k _ h.2)
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    show (detChar (Fin d) η⁻¹ h.1 : ℂ) • σ h.1 v = v
    rw [hg, smul_smul, detChar_apply, MonoidHom.inv_apply, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, one_smul]
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries hadm hτi hI
  let χ : Fin d → kˣ →* ℂˣ := fun i => unrChar k (α i)
  have h1 := hα.trans (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k d χ)
  have h2 := isSubquotient_twist h1 (detChar (Fin d) η)
  rw [hτ, twist_twist_inv] at h2
  have hχs : ∀ i, IsSmoothChar (χ i) := fun i => isSmoothChar_of_isUnram (isUnram_unrChar (k := k) (α i))
  let φ := multiProdTwistEquiv (Equiv.sigmaUnique (Fin d) fun _ => Fin 1)
    (fun i => detRep (Fin 1) (χ i)) hη
  have h3 := h2.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have hfam : (fun i => twist (detRep (Fin 1) (χ i)) (detChar (Fin 1) η)) =
      fun i => detRep (Fin 1) (η * χ i) := funext fun i => twist_detRep_one _ _
  rw [hfam] at h3
  refine ⟨fun j => η * χ j, fun j => ⟨hη.mul (hχs j), fun u hu => ?_⟩, hi,
    fun j => ⟨one_pos, isIrreducible_ofChar _, isCuspidal_detRep_one (hη.mul (hχs j))⟩, _, h3⟩
  show η u * unrChar k (α j) u = η u
  rw [isUnram_unrChar (k := k) (α j) u hu, mul_one]

end UpperTheory.TNZ
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ProductIrreducible2
noncomputable section

open ValuativeRel Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

namespace UpperTheory.TNZ.ProductIrreducible₂

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem exists_det_eq (u : kˣ) : ∃ g : GL (Fin 1) k, GeneralLinearGroup.det g = u := by
  refine ⟨⟨Matrix.diagonal fun _ => (u : k), Matrix.diagonal fun _ => ((u⁻¹ : kˣ) : k), ?_, ?_⟩, ?_⟩
  · simp [Matrix.diagonal_mul_diagonal]
  · simp [Matrix.diagonal_mul_diagonal]
  · ext
    simp [Matrix.GeneralLinearGroup.val_det_apply]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem char_eq_of_equiv {μ μ' χ : kˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ (GL (Fin 1) k) W} (ψ : (detRep (Fin 1) μ').Equiv τ)
    (φ : (detRep (Fin 1) μ).Equiv (twist τ (detChar (Fin 1) χ))) (g : GL (Fin 1) k) :
    (μ (GeneralLinearGroup.det g) : ℂ) =
      (χ (GeneralLinearGroup.det g) : ℂ) * (μ' (GeneralLinearGroup.det g) : ℂ) := by
  have hτ : ∀ w : W, τ g w = (μ' (GeneralLinearGroup.det g) : ℂ) • w := by
    intro w
    obtain ⟨x, rfl⟩ := ψ.toLinearEquiv.surjective w
    have key : ψ.toLinearEquiv (detRep (Fin 1) μ' g x) = τ g (ψ.toLinearEquiv x) :=
      LinearMap.congr_fun (ψ.toIntertwiningMap.isIntertwining' g) x
    rw [← key]
    simp only [detRep, ofChar_apply, detChar_apply]
    rw [← smul_eq_mul, map_smul]
  have key : φ.toLinearEquiv (detRep (Fin 1) μ g 1) = twist τ (detChar (Fin 1) χ) g (φ.toLinearEquiv 1) :=
    LinearMap.congr_fun (φ.toIntertwiningMap.isIntertwining' g) 1
  simp only [detRep, ofChar_apply, detChar_apply, twist_apply, hτ, mul_one, smul_smul] at key
  have hne : φ.toLinearEquiv 1 ≠ 0 := by
    rw [Ne, LinearEquiv.map_eq_zero_iff]
    exact one_ne_zero
  have h1 : φ.toLinearEquiv ((μ (GeneralLinearGroup.det g) : ℂ)) =
      (μ (GeneralLinearGroup.det g) : ℂ) • φ.toLinearEquiv 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [h1] at key
  exact smul_left_injective ℂ hne key

theorem eq_on_units (y : IrrGL (k := k)) (h : 1 = y.1) (μ μ' : kˣ →* ℂˣ) (hμ : IsSmoothChar μ)
    (hs' : IsSmooth (detRep (Fin 1) μ')) (hi' : (detRep (Fin 1) μ').IsIrreducible)
    (hy : IrrGL.of (detRep (Fin 1) μ') hs' hi' = y) (j : ℤ)
    (hφ : Nonempty ((h ▸ GlobalTheory.SplitRead.Irr.ofDet 1 μ hμ : GlobalTheory.SplitRead.Irr k y.1).π.Equiv
      (twist (GlobalTheory.SplitRead.Irr.ofIrrRep y.2.rep).π (detChar (Fin y.1) (absPow k (j : ℂ))))))
    (u : kˣ) (hu : valuation k (u : k) = 1) : μ u = μ' u := by
  subst hy
  obtain ⟨φ⟩ := hφ
  obtain ⟨g, hg⟩ := exists_det_eq u
  have := char_eq_of_equiv (IrrGL.equivOf (detRep (Fin 1) μ') hs' hi') φ g
  rw [hg] at this
  have habs : (absPow k (j : ℂ) u : ℂ) = 1 := by
    rw [val_absPow, nabs_eq_one (k := k) hu]
    simp
  rw [habs, one_mul] at this
  exact Units.ext this

theorem product_irreducible_of_distinct_twists (hL : GlobalTheory.Mem.LiteralAutomorphy.LitLoc) :
    ∀ (s N : ℕ) (d : Fin s → ℕ) (hd : ∑ b, d b = N) (X : Fin s → Type) [∀ b, AddCommGroup (X b)]
      [∀ b, Module ℂ (X b)] (σ : ∀ b, Representation ℂ (GL (Fin (d b)) k) (X b)),
      (∀ b, IsSmooth (σ b)) → (∀ b, (σ b).IsIrreducible) → ∀ η : Fin s → kˣ →* ℂˣ,
      (∀ b c, b ≠ c → ∃ u : kˣ, valuation k (u : k) = 1 ∧ η b u ≠ η c u) →
      ∀ μ : ∀ b, Fin (d b) → kˣ →* ℂˣ,
      (∀ b j, IsSmoothChar (μ b j) ∧ ∀ u : kˣ, valuation k (u : k) = 1 → μ b j u = η b u) →
      (∀ b, IsCuspSupport (σ b) (fun _ => 1) (fun j => detRep (Fin 1) (μ b j))) →
        (multiProd (stdBlocks d hd) σ).IsIrreducible := by
  intro s
  induction s with
  | zero =>
    intros
    exact GlobalTheory.SmGL.MultiIrr.isIrreducible_multiProd_zero _ _
  | succ s ih =>
    intro N d hd X _ _ σ hs hi η hη μ hμ hcs
    have e : N = d 0 + ∑ i : Fin s, d i.succ := hd.symm.trans (Fin.sum_univ_succ _)
    subst e
    obtain ⟨E⟩ := GlobalTheory.SmGL.MultiIrr.nonempty_prod₂_equiv_multiProd_succ d hd σ
    have hτi : (multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i => σ i.succ).IsIrreducible :=
      ih _ (fun i => d i.succ) rfl (fun i => X i.succ) (fun i => σ i.succ) (fun i => hs _) (fun i => hi _)
        (fun i => η i.succ) (fun b c hbc => hη _ _ fun h => hbc (Fin.succ_injective _ h))
        (fun i => μ i.succ) (fun i => hμ _) (fun i => hcs _)
    have hτs : IsSmooth (multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i => σ i.succ) :=
      isSmooth_parInd _ _
    obtain ⟨h', x, hx, hxc⟩ := GlobalTheory.LocGL.SupportRing.hasSupport_multiProd hL.zel (d := fun i : Fin s => d i.succ) rfl
      (fun i => σ i.succ) (fun i => hs _) (fun i => hi _) (fun i => hasSupport_of_isCuspSupport (hcs i.succ)) hτi
    have hP := hL.disj k (d 0) (∑ i : Fin s, d i.succ) (d 0) h'
      { V := X 0, π := σ 0, smooth := hs 0, irr := hi 0 }
      { V := _, π := multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i => σ i.succ, smooth := hτs,
        irr := hτi }
      (fun _ => 1) (fun b => (x b).1) (fun a => GlobalTheory.SplitRead.Irr.ofDet 1 (μ 0 a) (hμ 0 a).1)
      (fun b => GlobalTheory.SplitRead.Irr.ofIrrRep (x b).2.rep) (hcs 0) hxc ?_
    · exact GlobalTheory.Parabolic.isIrreducible_of_equiv E hP
    · intro a b hab j _ hφ
      have hxb : x b ∈ ∑ i : Fin s, Finset.univ.val.map fun a =>
          IrrGL.of (detRep (Fin 1) (μ i.succ a)) ((hcs i.succ).2.1 a).2.2.1 ((hcs i.succ).2.1 a).2.1 := by
        rw [← hx]
        exact Multiset.mem_map_of_mem x (Finset.mem_univ_val b)
      obtain ⟨c, -, hc⟩ := Multiset.mem_sum.1 hxb
      obtain ⟨j', -, hj'⟩ := Multiset.mem_map.1 hc
      obtain ⟨u, hu, hne⟩ := hη 0 c.succ (Fin.succ_ne_zero c).symm
      apply hne
      rw [← (hμ 0 a).2 u hu, ← (hμ c.succ j').2 u hu]
      exact eq_on_units (x b) hab (μ 0 a) (μ c.succ j') (hμ 0 a).1 _ _ hj' j hφ u hu

end UpperTheory.TNZ.ProductIrreducible₂

namespace UpperTheory.TNZ

theorem step_prodIrr : ProductIrreducibleProp := by
  unfold ProductIrreducibleProp
  intro hC hL k _ _ _ _ s N d hd X _ _ σ hs hi η hη hdv hne
  have H := fun b => hC hL k (d b) (X b) (σ b) (hs b) (hi b) (η b) (hη b) (hdv b)
  choose μ hμ hcs using H
  exact ProductIrreducible₂.product_irreducible_of_distinct_twists hL s N d hd X σ hs hi η hne μ hμ hcs

end UpperTheory.TNZ
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.DeterminantVector
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace DeterminantVector

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mem_fixed_iff {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin N) k) V) (K : Subgroup (GL (Fin N) k)) (v : V) :
    v ∈ fixed ρ K ↔ ∀ g ∈ K, ρ g v = v := by
  constructor
  · intro h g hg
    simpa using h ⟨g, hg⟩
  · intro h g
    simpa using h g g.2


omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem hasDetVec_twist {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin N) k) V) (η : kˣ →* ℂˣ) (h : IsSpherical ρ) :
    HasDetVec (twist ρ (detChar (Fin N) η)) η := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  refine ⟨v, hv0, fun g hg => ?_⟩
  rw [twist_apply, detChar_apply, (mem_fixed_iff ρ _ v).1 hv g hg]


omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem isSpherical_twist {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin N) k) V) (η : kˣ →* ℂˣ) (h : HasDetVec ρ η) :
    IsSpherical (twist ρ (detChar (Fin N) η⁻¹)) := by
  obtain ⟨v, hv0, hv⟩ := h
  refine (Submodule.ne_bot_iff _).2 ⟨v, ?_, hv0⟩
  refine (mem_fixed_iff _ _ v).2 fun g hg => ?_
  rw [twist_apply, detChar_apply, hv g hg, smul_smul, MonoidHom.inv_apply, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_smul]

end DeterminantVector

theorem step_detVec : DeterminantVectorProp := by
  intro k _ _ _ _ N V _ _ ρ η
  exact ⟨DeterminantVector.hasDetVec_twist ρ η, DeterminantVector.isSpherical_twist ρ η⟩

end UpperTheory.TNZ
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PUntwistRc
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TNZ

namespace P_untwistRc

theorem tw_eq_self {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : IrrGL (k := k)) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (e : χ = 1) : x.tw χ hχ = x := by
  subst e
  exact IrrGL.tw_one x hχ

theorem of_eq_tw {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {d : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ (GL (Fin d) k) X)
    (hs : IsSmooth σ) (hi : σ.IsIrreducible) (η : kˣ →* ℂˣ) (hη : IsSmoothChar η) :
    IrrGL.of σ hs hi =
      (IrrGL.of (twist σ (detChar (Fin d) η⁻¹)) (isSmooth_twist hs hη.inv.detChar) (isIrreducible_twist hi _)).tw η hη := by
  rw [← IrrGL.tw_of σ hs hi η⁻¹ hη.inv, IrrGL.tw_tw]
  exact (tw_eq_self _ _ _ (inv_mul_cancel η)).symm

end P_untwistRc

theorem step_untwistRc : UntwistRestrictionProp := by
  intro E Ω _ _ _ _ _ A w h a ha ε rc hL d X _ _ σ hs hi η hη
  refine ⟨isSmooth_twist hs hη.inv.detChar, isIrreducible_twist hi _, ?_⟩
  rw [P_untwistRc.of_eq_tw σ hs hi η hη, hL.twist, hL.one]

end UpperTheory.TNZ
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SphericalUnramified
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TNZ

namespace SphericalUnramified

theorem isSpherical_of_equiv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {d : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin d) k) V} {π : Representation ℂ (GL (Fin d) k) W} (e : ρ.Equiv π)
    (h : IsSpherical ρ) : IsSpherical π := by
  unfold IsSpherical IsSphericalFor at *
  obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨e x, ?_, ?_⟩
  · intro g
    have hg := hx g
    have hint : e (ρ (g : GL (Fin d) k) x) = π (g : GL (Fin d) k) (e x) :=
      LinearMap.congr_fun (e.isIntertwining' (g : GL (Fin d) k)) x
    rw [← hint, hg, map_smul]
  · intro h1
    apply h0
    have : e x = e 0 := by rw [h1, map_zero]
    exact EquivLike.injective e this

end SphericalUnramified

theorem step_sphUnr : SphericalUnramifiedProp := by
  intro E Ω _ _ _ _ _ A w h a ha ε rc hL d X _ _ σ hs hi hsph
  exact (hL.sph (IrrGL.of σ hs hi)).1 (SphericalUnramified.isSpherical_of_equiv (IrrGL.equivOf σ hs hi) hsph)

end UpperTheory.TNZ
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.UnramifiedTwist
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace UpperTheory.TNZ

namespace UnramifiedTwist

theorem charpoly_smul_one {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (c : ℂ) :
    (c • (1 : Module.End ℂ V)).charpoly = (X - C c) ^ Module.finrank ℂ V := by
  have h1 := LinearMap.charpoly_sub_smul (c • (1 : Module.End ℂ V)) c
  rw [sub_self, LinearMap.charpoly_zero] at h1
  calc (c • (1 : Module.End ℂ V)).charpoly
      = ((c • (1 : Module.End ℂ V)).charpoly.comp (X + C c)).comp (X - C c) := by
        rw [Polynomial.comp_assoc]; simp
    _ = (X - C c) ^ Module.finrank ℂ V := by rw [← h1, Polynomial.X_pow_comp]

theorem diagEnd_const (c : ℂ) :
    diagEnd (fun _ : Fin 1 => c) = c • (1 : Module.End ℂ (Fin 1 → ℂ)) :=
  LinearMap.ext fun v => funext fun i => by simp

end UnramifiedTwist

open UnramifiedTwist in
theorem step_unrTwist : UnramifiedTwistProp := by
  intro E Ω _ _ _ _ _ A w h u ψ hψ hu
  obtain ⟨n, a, rfl⟩ := WD.exists_rep u
  rw [WD.unr_mk] at hu
  obtain ⟨hN, hI⟩ := hu
  simp only [WD.lpOfChar, WD.lpChar_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff, WD.charPol_mk, WD.lpDim_mk]
  refine ⟨?_, fun t => ?_⟩
  · rw [WDRep.tensor_N, hN, WDRep.ofChars_N]
    simp
  · rw [WDRep.tensor_ρ, hI t, WDRep.ofChars_ρ, diagEnd_const, TensorProduct.map_smul_right,
      TensorProduct.map_one, charpoly_smul_one, Module.finrank_tensorProduct]
    simp

end UpperTheory.TNZ
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PProdRc
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TNZ.P_prodRc

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem wd_eq_lpZero {x : WD h} (hx : x.lpDim = 0) : x = WD.lpZero (h := h) := by
  obtain ⟨n, a, rfl⟩ := x.exists_rep
  obtain rfl : n = 0 := by simpa using hx
  exact WD.sound ⟨.refl _ _, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩

theorem main {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} (L : Laws a ha ε rc) :
    ∀ (s N : ℕ) (d : Fin s → ℕ) (hd : ∑ b, d b = N) (X : Fin s → Type) [∀ b, AddCommGroup (X b)]
      [∀ b, Module ℂ (X b)] (σ : ∀ b, Representation ℂ (GL (Fin (d b)) (w.adicCompletion E)) (X b))
      (hs : ∀ b, IsSmooth (σ b)) (hi : ∀ b, (σ b).IsIrreducible)
      (hI : (multiProd (stdBlocks d hd) σ).IsIrreducible),
      rc (IrrGL.of (multiProd (stdBlocks d hd) σ) (isSmooth_parInd _ _) hI) =
        sumList (List.ofFn fun b => rc (IrrGL.of (σ b) (hs b) (hi b))) := by
  intro s
  induction s with
  | zero =>
    intro N d hd X _ _ σ hs hi hI
    have h0 : N = 0 := by simpa using hd.symm
    rw [List.ofFn_zero, sumList, List.foldr_nil]
    exact wd_eq_lpZero ((L.dim (IrrGL.of (multiProd (stdBlocks d hd) σ) (isSmooth_parInd _ _) hI)).trans h0)
  | succ s ih =>
    intro N d hd X _ _ σ hs hi hI
    obtain rfl : N = d 0 + ∑ i : Fin s, d i.succ := hd.symm.trans (Fin.sum_univ_succ d)
    obtain ⟨Φ⟩ := GlobalTheory.SmGL.MultiIrr.nonempty_prod₂_equiv_multiProd_succ d hd σ
    have hts : IsSmooth (multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i : Fin s => σ i.succ) :=
      isSmooth_parInd _ _
    have hti := GlobalTheory.SmGL.ProdIrr.isIrreducible_of_prod₂ _ _ _ _ _ _ (σ 0) _ (multiProd (stdBlocks d hd) σ)
      (hs 0) (hi 0) hts hI ⟨Φ.symm⟩
    have key := L.prod (d 0) (∑ i : Fin s, d i.succ) ⟨X 0, σ 0, hs 0, hi 0⟩ ⟨_, _, hts, hti⟩
      ⟨_, multiProd (stdBlocks d hd) σ, isSmooth_parInd _ _, hI⟩ ⟨Φ.symm⟩
    refine key.trans ?_
    rw [List.ofFn_succ, sumList, List.foldr_cons]
    congr 1
    exact ih _ (fun i => d i.succ) rfl (fun i => X i.succ) (fun i => σ i.succ) (fun i => hs i.succ)
      (fun i => hi i.succ) hti

end UpperTheory.TNZ.P_prodRc

namespace UpperTheory.TNZ

theorem step_prodRc : ProductRestrictionProp := by
  intro E Ω _ _ _ _ _ A w h a ha ε rc L s N d hd X _ _ σ hs hi hI
  exact P_prodRc.main L s N d hd X σ hs hi hI

end UpperTheory.TNZ
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.JacNeZero
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Grp

variable {n : ℕ} (G : Grp k n)

theorem jac_ne_zero (hcb : CompactConductorBasicProp (k := k)) (hccB : G.CompactConductorBoundProp) (hJone : G.JacquetOneProp) (hJmul : G.JacquetMultiplicativeProp)
    (hJinv : G.JacquetInverseProp) (hKC : G.CompactOpenKernelProp) (hΔU : G.ModulusOnUnitsProp) (hΔM : G.ModulusMultiplicativeProp) (hlM : G.LambdaMultiplicativeProp)
    (hlB : G.LambdaBasicProp) (hlU : G.LambdaUnipotentProp) (hiw : G.IwahoriDecompositionProp) (hPJ : G.ParabolicJacquetProp) (hkill : G.AnnihilationProp)
    (hni : G.NonIntegralProp) (hTE : G.TorusCentreEigenProp) (hTp : G.TorusPowerProp) (hjK : G.JacquetKernelProp) (hTI : G.TorusCentreInjectiveProp)
    (hun : UniformizerProp (k := k))
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π)
    (x : V) (hx0 : x ≠ 0) (hx : x ∈ G.Eig π) :
    (Submodule.Quotient.mk x : Jacquet π (unipRad k G.e)) ≠ 0 := by
  obtain ⟨ϖ, hϖ⟩ := hun
  have hJmul' := hJmul hcb hccB
  have hJinv' := hJinv hcb hccB
  have hΔU' := hΔU hccB
  have hlM' := hlM hcb hΔU hΔM hccB
  have hiw' := hiw hcb hccB hΔU hJmul hJinv
  have hTE' := hTE hcb hccB hΔU hΔM hJmul hJinv hlM hlU hiw
  have hPJ' := hPJ hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC
  have hTI' := hTI hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hlU hiw hPJ hkill hni hTE hKC ϖ hϖ V π hs
  have hTp' := hTp hcb hccB hΔU hΔM hJmul hJinv hlM hlU hiw hTE ϖ hϖ V π
  have hE : ∀ y ∈ G.Eig π, G.Tz π ϖ 1 y ∈ G.Eig π := fun y hy => (hTE' ϖ hϖ 1).2 V π y hy
  have key : ∀ m : ℕ, ∀ y ∈ G.Eig π, (G.Tz π ϖ 1)^[m] y = 0 → y = 0 := by
    intro m
    induction m with
    | zero => intro y _ h; simpa using h
    | succ m ih =>
      intro y hy h
      rw [Function.iterate_succ_apply] at h
      exact hTI' y hy (ih _ (hE y hy) h)
  intro h0
  obtain ⟨m, hm⟩ := hjK hcb hccB hΔU hΔM hJmul hJinv hlM hiw hTE hlU ϖ hϖ V π hs x hx h0
  rw [hTp' x hx m] at hm
  exact hx0 (key m x hx hm)

theorem cMain (hcb : CompactConductorBasicProp (k := k)) (hccB : G.CompactConductorBoundProp) (hJone : G.JacquetOneProp) (hJmul : G.JacquetMultiplicativeProp)
    (hJinv : G.JacquetInverseProp) (hKC : G.CompactOpenKernelProp) (hΔU : G.ModulusOnUnitsProp) (hΔM : G.ModulusMultiplicativeProp) (hlM : G.LambdaMultiplicativeProp)
    (hlB : G.LambdaBasicProp) (hlU : G.LambdaUnipotentProp) (hiw : G.IwahoriDecompositionProp) (hPJ : G.ParabolicJacquetProp) (hkill : G.AnnihilationProp)
    (hni : G.NonIntegralProp) (hTE : G.TorusCentreEigenProp) (hTp : G.TorusPowerProp) (hjK : G.JacquetKernelProp) (hTI : G.TorusCentreInjectiveProp)
    (hun : UniformizerProp (k := k)) (hlL : LeviSubgroupRestriction) (hjI : G.JacquetImageProp) (hjP : G.JacquetProductProp) : G.CMainFor := by
  intro L V _ _ π hs hirr ⟨x, hx0, hx⟩
  refine hjP L V π hs hirr ⟨_, G.jac_ne_zero hcb hccB hJone hJmul hJinv hKC hΔU hΔM hlM hlB hlU hiw hPJ hkill hni hTE hTp
    hjK hTI hun π hs x hx0 hx, fun m hm => hjI hlL hJone V π x hx m hm⟩

end Grp

end UpperTheory.TNZ
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSumList
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace UpperTheory.TNZ

namespace P_sumList

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem monomial_sum_iff_alt (x y : WD h) : (WD.lpSum x y).mono0 ↔ x.mono0 ∧ y.mono0 := by
  induction x using WD.ind with
  | hP n a =>
    induction y using WD.ind with
    | hP m b =>
      rw [WD.lpSum_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff, WD.monodromyZero_ofWeilDeligneRepClass_iff, WD.monodromyZero_ofWeilDeligneRepClass_iff, WDRep.sum_N]
      constructor
      · intro hN
        refine ⟨LinearMap.ext fun v => ?_, LinearMap.ext fun v => ?_⟩
        · have := congrArg Prod.fst (LinearMap.congr_fun hN (v, 0))
          simpa using this
        · have := congrArg Prod.snd (LinearMap.congr_fun hN (0, v))
          simpa using this
      · rintro ⟨ha, hb⟩
        rw [ha, hb, LinearMap.prodMap_zero]

theorem charPol_lpSum (x y : WD h) (σ : Weil h) :
    (WD.lpSum x y).charPol σ = x.charPol σ * y.charPol σ := by
  induction x using WD.ind with
  | hP n a =>
    induction y using WD.ind with
    | hP m b =>
      rw [WD.lpSum_mk, WD.charPol_mk, WD.charPol_mk, WD.charPol_mk, WDRep.sum_ρ,
        LinearMap.charpoly_prodMap]

theorem monomial_zero_alt : (WD.lpZero (h := h)).mono0 := by
  rw [WD.lpZero, WD.monodromyZero_ofWeilDeligneRepClass_iff, WDRep.diag_N]

theorem charPol_lpZero (σ : Weil h) : (WD.lpZero (h := h)).charPol σ = 1 := by
  refine Polynomial.eq_one_of_monic_natDegree_zero (WD.charPol_monic _ σ) ?_
  rw [WD.charPol_natDegree, WD.lpZero, WD.lpDim_mk]
  simp

end P_sumList

open P_sumList in
theorem step_sumList : SumOverListProp := by
  intro E Ω _ _ _ _ _ A w h l
  refine ⟨?_, fun σ => ?_⟩
  · induction l with
    | nil => simp [sumList, monomial_zero_alt]
    | cons y l ih =>
      rw [sumList, List.foldr_cons, ← sumList, monomial_sum_iff_alt, ih]
      simp
  · induction l with
    | nil => simp [sumList, charPol_lpZero]
    | cons y l ih =>
      rw [sumList, List.foldr_cons, ← sumList, charPol_lpSum, ih, List.map_cons, List.prod_cons]

end UpperTheory.TNZ
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ScalarInertia
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Polynomial Module
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.WeilDeligne

namespace UpperTheory.TNZ.ScalarInertia

theorem eq_algebraMap_of_charpoly {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : End ℂ V) (hs : f.IsSemisimple) (c : ℂ) (m : ℕ) (hc : f.charpoly = (X - C c) ^ m) :
    f = algebraMap ℂ (End ℂ V) c := by
  have hg : (f - algebraMap ℂ (End ℂ V) c).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.mpr hs
  have hn : IsNilpotent (f - algebraMap ℂ (End ℂ V) c) := by
    refine ⟨m, ?_⟩
    have := LinearMap.aeval_self_charpoly f
    rw [hc] at this
    simpa [map_pow, map_sub, aeval_X, aeval_C] using this
  exact sub_eq_zero.mp (Module.End.eq_zero_of_isNilpotent_isSemisimple hn hg)

variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem isSmooth_inv {ψ : Weil h →* ℂˣ} (hψ : IsSmooth ψ) : IsSmooth ψ⁻¹ :=
  hψ.of_le fun σ hσ => by simp [hσ]

variable [IsAlgClosure E Ω]

theorem unr_twist {n : ℕ} (a : WDRep h (Fin n → ℂ)) (ψ : Weil h →* ℂˣ) (hψ : IsSmooth ψ) (hN : a.N = 0)
    (m : ℕ) (hc : ∀ t : Ine (F := E) A,
      (a.ρ (ineIncl h t)).charpoly = (X - C ((ψ (ineIncl h t) : ℂˣ) : ℂ)) ^ m) :
    (a.twist ψ⁻¹ (isSmooth_inv hψ)).Unr := by
  refine ⟨hN, fun t => ?_⟩
  rw [WDRep.twist_ρ, eq_algebraMap_of_charpoly _ (a.semisimple _) _ _ (hc t),
    Algebra.algebraMap_eq_smul_one, smul_smul, MonoidHom.inv_apply, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_smul]

theorem iso_tensor {n : ℕ} (a : WDRep h (Fin n → ℂ)) (ψ : Weil h →* ℂˣ) (hψ : IsSmooth ψ) (hN : a.N = 0) :
    ((a.twist ψ⁻¹ (isSmooth_inv hψ)).tensor
      (WDRep.ofChars h (ι := Fin 1) (fun _ => ψ) fun _ => hψ)).Iso a := by
  refine ⟨(TensorProduct.congr (LinearEquiv.refl ℂ (Fin n → ℂ)) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans
    (TensorProduct.rid ℂ (Fin n → ℂ)), fun σ x => ?_, fun x => ?_⟩
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [WDRep.tensor_ρ, TensorProduct.map_tmul, WDRep.twist_ρ, WDRep.ofChars_ρ,
        LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply, TensorProduct.rid_tmul,
        LinearEquiv.funUnique_apply, Function.eval, diagEnd_apply, LinearMap.smul_apply, map_smul, smul_smul,
        MonoidHom.inv_apply]
      congr 1
      rw [mul_comm, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · simp [WDRep.twist, hN]

end UpperTheory.TNZ.ScalarInertia

namespace UpperTheory.TNZ

open ScalarInertia in
theorem step_scalarInertia : ScalarOnInertiaProp := by
  intro E Ω _ _ _ _ _ A w h v ψ hψ hv hc
  obtain ⟨n, a, rfl⟩ := WD.exists_rep v
  rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at hv
  simp only [WD.charPol_mk, WD.lpDim_mk] at hc
  refine ⟨WD.mk (a.twist ψ⁻¹ (isSmooth_inv hψ)), (WD.unr_mk _).mpr (unr_twist a ψ hψ hv _ hc), by simp, ?_⟩
  rw [WD.lpOfChar, WD.lpChar_mk]
  exact WD.sound (iso_tensor a ψ hψ hv).symm

end UpperTheory.TNZ
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.GMain
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TNZ

theorem gMain (h1 : DeterminantVectorProp) (h2 : UnramifiedTwistProp) (h3 : SumOverListProp) (h4a : IsotypicComponentProp)
    (h4b : ScalarOnInertiaProp) (h5 : SphericalOfUnramifiedProp) (h5' : SphericalUnramifiedProp) (h6 : TwistRestrictionProp) (h6' : UntwistRestrictionProp)
    (h7 : ProductRestrictionProp) (h8a : CuspidalSupportProp) (h8b : ProductIrreducibleProp) (h9 : ArtinInertiaProp) : GMain := by
  intro E Ω _ _ _ _ _ A w h a ha ε rc hL hLit s d η hη hdist x hd
  have hψ : ∀ b, IsSmooth ((η b).comp a) := fun b => ha.smooth (hη b)
  constructor
  · rintro ⟨h0, hc⟩
    obtain ⟨v, hv, hsum⟩ := h4a E Ω A w h (rc x) s d (fun b => (η b).comp a) hψ hdist h0 hc
    have hv' : ∀ b, ∃ v' : WD h, v'.unr ∧ v'.lpDim = d b ∧
        v b = v'.lpChar (WD.lpOfChar h ((η b).comp a) (hψ b)) := by
      intro b
      obtain ⟨v', hu, hdim, he⟩ := h4b E Ω A w h (v b) ((η b).comp a) (hψ b) (hv b).1
        (fun t => by rw [(hv b).2.1]; exact (hv b).2.2 t)
      exact ⟨v', hu, hdim.trans (hv b).2.1, he⟩
    choose v' hu hdim he using hv'
    choose Xs instA instM σ hs hi hsph hrc using fun b => h5 E Ω A w h a ha ε rc hL (d b) (v' b) (hu b) (hdim b)
    letI := instA
    letI := instM
    choose hs' hi' hrc' using fun b => h6 E Ω A w h a ha ε rc hL (d b) (Xs b) (σ b) (hs b) (hi b) (η b) (hη b)
    have hdet : ∀ b, HasDetVec (twist (σ b) (detChar (Fin (d b)) (η b))) (η b) :=
      fun b => (h1 _ (d b) (Xs b) (σ b) (η b)).1 (hsph b)
    have hdistU : ∀ b c, b ≠ c → ∃ u : (w.adicCompletion E)ˣ,
        valuation (w.adicCompletion E) (u : w.adicCompletion E) = 1 ∧ η b u ≠ η c u := by
      intro b c hbc
      obtain ⟨t, ht⟩ := hdist b c hbc
      exact ⟨a (ineIncl h t), (h9 E Ω A w h a ha).1 t, ht⟩
    have hI := h8b h8a hLit _ s x.1 d hd Xs (fun b => twist (σ b) (detChar (Fin (d b)) (η b))) hs' hi' η hη hdet hdistU
    have hrcP := h7 E Ω A w h a ha ε rc hL s x.1 d hd Xs (fun b => twist (σ b) (detChar (Fin (d b)) (η b))) hs' hi' hI
    have heq : rc (IrrGL.of (multiProd (stdBlocks d hd) fun b => twist (σ b) (detChar (Fin (d b)) (η b)))
        (isSmooth_parInd _ _) hI) = rc x := by
      rw [hrcP, hsum]
      congr 1
      refine List.ofFn_inj.2 (funext fun b => ?_)
      rw [hrc' b, hrc b, he b]
    have e2 := (hL.bij.1 heq).trans (IrrGL.of_rep x).symm
    obtain ⟨e⟩ := IrrGL.of_eq_of.1 e2
    exact ⟨Xs, instA, instM, fun b => twist (σ b) (detChar (Fin (d b)) (η b)), hs', hi', hdet, ⟨e.symm⟩⟩
  · rintro ⟨Xs, instA, instM, σ, hs, hi, hdet, ⟨e⟩⟩
    letI := instA
    letI := instM
    have hI : (multiProd (stdBlocks d hd) σ).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e x.2.rep.irr
    have hx : x = IrrGL.of (multiProd (stdBlocks d hd) σ) (isSmooth_parInd _ _) hI :=
      (IrrGL.of_rep x).symm.trans (IrrGL.of_eq_of.2 ⟨e⟩)
    have hfac : ∀ b, ∃ u : WD h, u.unr ∧ u.lpDim = d b ∧
        rc (IrrGL.of (σ b) (hs b) (hi b)) = u.lpChar (WD.lpOfChar h ((η b).comp a) (hψ b)) := by
      intro b
      obtain ⟨hs', hi', hr⟩ := h6' E Ω A w h a ha ε rc hL (d b) (Xs b) (σ b) (hs b) (hi b) (η b) (hη b)
      exact ⟨_, h5' E Ω A w h a ha ε rc hL (d b) (Xs b) _ hs' hi' ((h1 _ (d b) (Xs b) (σ b) (η b)).2 (hdet b)),
        hL.dim _, hr⟩
    choose u hu hud hur using hfac
    have hl := h3 E Ω A w h (List.ofFn fun b => rc (IrrGL.of (σ b) (hs b) (hi b)))
    have hP := h7 E Ω A w h a ha ε rc hL s x.1 d hd Xs σ hs hi hI
    rw [← hx] at hP
    rw [hP]
    refine ⟨hl.1.2 fun y hy => ?_, fun t => ?_⟩
    · simp only [List.mem_ofFn, Set.mem_range] at hy
      obtain ⟨b, rfl⟩ := hy
      rw [hur b]
      exact (h2 E Ω A w h (u b) _ (hψ b) (hu b)).1
    · rw [hl.2, List.map_ofFn, List.prod_ofFn]
      refine Finset.prod_congr rfl fun b _ => ?_
      simp only [Function.comp_apply]
      rw [hur b, (h2 E Ω A w h (u b) _ (hψ b) (hu b)).2 t, hud b]
      rfl

end UpperTheory.TNZ
end
end
