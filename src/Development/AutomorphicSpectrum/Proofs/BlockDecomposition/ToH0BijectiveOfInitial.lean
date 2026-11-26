module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationCriticalComparisonMap

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensTransfer
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

universe w w' w₁ w₂ w₃ w₄ w₅ t₁ t₂ t₃ t₄ t₅

section Alg

theorem five_add {A₁ : Type w₁} {A₂ : Type w₂} {A₃ : Type w₃} {A₄ : Type w₄} {A₅ : Type w₅}
    {L₁ : Type t₁} {L₂ : Type t₂} {L₃ : Type t₃} {L₄ : Type t₄} {L₅ : Type t₅}
    [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃] [AddCommGroup A₄] [AddCommGroup A₅]
    [AddCommGroup L₁] [AddCommGroup L₂] [AddCommGroup L₃] [AddCommGroup L₄] [AddCommGroup L₅]
    (u₁ : A₁ →+ A₂) (u₂ : A₂ →+ A₃) (u₃ : A₃ →+ A₄) (u₄ : A₄ →+ A₅)
    (v₁ : L₁ →+ L₂) (v₂ : L₂ →+ L₃) (v₃ : L₃ →+ L₄) (v₄ : L₄ →+ L₅)
    (g₁ : A₁ →+ L₁) (g₂ : A₂ →+ L₂) (g₃ : A₃ →+ L₃) (g₄ : A₄ →+ L₄) (g₅ : A₅ →+ L₅)
    (c₁ : ∀ x, g₂ (u₁ x) = v₁ (g₁ x)) (c₂ : ∀ x, g₃ (u₂ x) = v₂ (g₂ x))
    (c₃ : ∀ x, g₄ (u₃ x) = v₃ (g₃ x)) (c₄ : ∀ x, g₅ (u₄ x) = v₄ (g₄ x))
    (eA₂ : Function.Exact u₁ u₂) (eA₃ : Function.Exact u₂ u₃) (eA₄ : Function.Exact u₃ u₄)
    (eL₂ : Function.Exact v₁ v₂) (eL₃ : Function.Exact v₂ v₃) (eL₄ : Function.Exact v₃ v₄)
    (s₁ : Function.Surjective g₁) (b₂ : Function.Bijective g₂) (b₄ : Function.Bijective g₄)
    (i₅ : Function.Injective g₅) : Function.Bijective g₃ := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : u₃ x = 0 := b₄.1 (by rw [c₃, hx, map_zero, map_zero])
    obtain ⟨y, rfl⟩ := (eA₃ x).1 h1
    have h2 : v₂ (g₂ y) = 0 := by rw [← c₂, hx]
    obtain ⟨z, hz⟩ := (eL₂ _).1 h2
    obtain ⟨t, rfl⟩ := s₁ z
    have h3 : u₁ t = y := b₂.1 (by rw [c₁, hz])
    exact (eA₂ _).2 ⟨t, h3⟩
  · intro t
    obtain ⟨p, hp⟩ := b₄.2 (v₃ t)
    have h1 : u₄ p = 0 := i₅ (by
      rw [c₄, hp, map_zero]
      exact (eL₄ _).2 ⟨t, rfl⟩)
    obtain ⟨q, rfl⟩ := (eA₄ p).1 h1
    have h2 : v₃ (t - g₃ q) = 0 := by rw [map_sub, ← c₃, hp, sub_self]
    obtain ⟨y', hy'⟩ := (eL₃ _).1 h2
    obtain ⟨y, rfl⟩ := b₂.2 y'
    refine ⟨q + u₂ y, ?_⟩
    rw [map_add (f := _), c₂, hy']
    abel

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ι → Type}
  [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

theorem tens_ext {M : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] {P : Type w'} [AddCommGroup P]
    (g h : (∀ i, N i ⊗[R] M i) →+ P) (H : ∀ i n x, g (Pi.single i (n ⊗ₜ x)) = h (Pi.single i (n ⊗ₜ x))) : g = h := by
  refine AddMonoidHom.functions_ext _ g h fun i t => ?_
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul n x => exact H i n x
  | add x y hx hy => rw [Pi.single_add, map_add (f := _), map_add (f := _), hx, hy]

def piT {M : ι → Type w} {M' : ι → Type w'} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)] (u : ∀ i, M i →ₗ[R] M' i) :
    (∀ i, N i ⊗[R] M i) →+ (∀ i, N i ⊗[R] M' i) where
  toFun t i := (u i).lTensor (N i) (t i)
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

theorem piT_single {M : ι → Type w} {M' : ι → Type w'} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)] (u : ∀ i, M i →ₗ[R] M' i) (i : ι) (n : N i) (x : M i) :
    piT (N := N) u (Pi.single i (n ⊗ₜ x)) = Pi.single i (n ⊗ₜ u i x) := by
  funext k
  by_cases h : k = i
  · subst h
    simp [piT]
  · simp [piT, Pi.single_eq_of_ne h]

theorem piT_exact [∀ i, Module.Flat R (N i)] {M₁ : ι → Type w₁} {M₂ : ι → Type w₂} {M₃ : ι → Type w₃}
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)] [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)]
    [∀ i, AddCommGroup (M₃ i)] [∀ i, Module R (M₃ i)] (u : ∀ i, M₁ i →ₗ[R] M₂ i) (v : ∀ i, M₂ i →ₗ[R] M₃ i)
    (h : ∀ i, Function.Exact (u i) (v i)) : Function.Exact (piT (N := N) u) (piT (N := N) v) := by
  intro t
  constructor
  · intro ht
    have h1 : ∀ i, ∃ s, (u i).lTensor (N i) s = t i := fun i =>
      (Module.Flat.lTensor_exact (N i) (h i) (t i)).1 (congrFun ht i)
    choose s hs using h1
    exact ⟨s, funext hs⟩
  · rintro ⟨s, rfl⟩
    funext i
    exact (Module.Flat.lTensor_exact (N i) (h i) _).2 ⟨s i, rfl⟩

theorem tens_zero {M : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] {M' : Type w'} [AddCommGroup M']
    (hM : ∀ i, Subsingleton (M i)) (hM' : Subsingleton M') (f : ∀ i, N i → M i → M') :
    Tens R (N := N) (M := M) (M' := M') f := by
  have h0 : ∀ i, Subsingleton (N i ⊗[R] M i) := fun i => by
    refine ⟨fun x y => ?_⟩
    have : ∀ z : N i ⊗[R] M i, z = 0 := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul n x => rw [Subsingleton.elim x 0, TensorProduct.tmul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    rw [this x, this y]
  refine ⟨⟨⟨fun _ => 0, fun _ => 0, fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩, fun _ _ => by simp⟩,
    fun i n x => Subsingleton.elim _ _⟩

theorem tens_transfer {M : ι → Type w₁} {L : ι → Type w₂} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (L i)] [∀ i, Module R (L i)] {M' : Type t₁} {L' : Type t₂} [AddCommGroup M'] [AddCommGroup L']
    (u : ∀ i, M i ≃ₗ[R] L i) (u' : M' ≃+ L') (f : ∀ i, N i → M i → M') (h : ∀ i, N i → L i → L')
    (hc : ∀ i n x, h i n (u i x) = u' (f i n x))
    (hf : Tens R (N := N) (M := M) (M' := M') f) : Tens R (N := N) (M := L) (M' := L') h := by
  obtain ⟨g, hg⟩ := hf
  let e : (∀ i, N i ⊗[R] L i) ≃+ (∀ i, N i ⊗[R] M i) :=
    { toFun := piT (N := N) fun i => ((u i).symm : L i →ₗ[R] M i)
      invFun := piT (N := N) fun i => ((u i) : M i →ₗ[R] L i)
      left_inv := fun t => by
        funext i
        change (((u i) : M i →ₗ[R] L i).lTensor (N i)) ((((u i).symm : L i →ₗ[R] M i).lTensor (N i)) (t i)) = t i
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
        simp
      right_inv := fun t => by
        funext i
        change (((u i).symm : L i →ₗ[R] M i).lTensor (N i)) ((((u i) : M i →ₗ[R] L i).lTensor (N i)) (t i)) = t i
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
        simp
      map_add' := map_add _ }
  refine ⟨(e.trans g).trans u', fun i n x => ?_⟩
  obtain ⟨y, rfl⟩ := (u i).surjective x
  have : e (Pi.single i (n ⊗ₜ u i y)) = Pi.single i (n ⊗ₜ y) := by
    change piT (N := N) (fun i => ((u i).symm : L i →ₗ[R] M i)) _ = _
    rw [piT_single]
    simp
  simp only [AddEquiv.trans_apply, this, hg, hc]

theorem tens_five [∀ i, Module.Flat R (N i)]
    {M₁ : ι → Type w₁} {M₂ : ι → Type w₂} {M₃ : ι → Type w₃} {M₄ : ι → Type w₄} {M₅ : ι → Type w₅}
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)] [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)]
    [∀ i, AddCommGroup (M₃ i)] [∀ i, Module R (M₃ i)] [∀ i, AddCommGroup (M₄ i)] [∀ i, Module R (M₄ i)]
    [∀ i, AddCommGroup (M₅ i)] [∀ i, Module R (M₅ i)]
    {L₁ : Type t₁} {L₂ : Type t₂} {L₃ : Type t₃} {L₄ : Type t₄} {L₅ : Type t₅}
    [AddCommGroup L₁] [AddCommGroup L₂] [AddCommGroup L₃] [AddCommGroup L₄] [AddCommGroup L₅]
    (u₁ : ∀ i, M₁ i →ₗ[R] M₂ i) (u₂ : ∀ i, M₂ i →ₗ[R] M₃ i) (u₃ : ∀ i, M₃ i →ₗ[R] M₄ i) (u₄ : ∀ i, M₄ i →ₗ[R] M₅ i)
    (v₁ : L₁ →+ L₂) (v₂ : L₂ →+ L₃) (v₃ : L₃ →+ L₄) (v₄ : L₄ →+ L₅)
    (f₁ : ∀ i, N i → M₁ i → L₁) (f₂ : ∀ i, N i → M₂ i → L₂) (f₃ : ∀ i, N i → M₃ i → L₃)
    (f₄ : ∀ i, N i → M₄ i → L₄) (f₅ : ∀ i, N i → M₅ i → L₅)
    (c₁ : ∀ i n x, f₂ i n (u₁ i x) = v₁ (f₁ i n x)) (c₂ : ∀ i n x, f₃ i n (u₂ i x) = v₂ (f₂ i n x))
    (c₃ : ∀ i n x, f₄ i n (u₃ i x) = v₃ (f₃ i n x)) (c₄ : ∀ i n x, f₅ i n (u₄ i x) = v₄ (f₄ i n x))
    (eM₂ : ∀ i, Function.Exact (u₁ i) (u₂ i)) (eM₃ : ∀ i, Function.Exact (u₂ i) (u₃ i))
    (eM₄ : ∀ i, Function.Exact (u₃ i) (u₄ i))
    (eL₂ : Function.Exact v₁ v₂) (eL₃ : Function.Exact v₂ v₃) (eL₄ : Function.Exact v₃ v₄)
    (h₁ : Tens R (N := N) (M := M₁) (M' := L₁) f₁) (h₂ : Tens R (N := N) (M := M₂) (M' := L₂) f₂)
    (h₄ : Tens R (N := N) (M := M₄) (M' := L₄) f₄) (h₅ : Tens R (N := N) (M := M₅) (M' := L₅) f₅)
    (hadd : ∀ i, ∃ F : N i ⊗[R] M₃ i →+ L₃, ∀ n x, F (n ⊗ₜ x) = f₃ i n x) :
    Tens R (N := N) (M := M₃) (M' := L₃) f₃ := by
  obtain ⟨g₁, hg₁⟩ := h₁
  obtain ⟨g₂, hg₂⟩ := h₂
  obtain ⟨g₄, hg₄⟩ := h₄
  obtain ⟨g₅, hg₅⟩ := h₅
  choose F hF using hadd
  let g₃ : (∀ i, N i ⊗[R] M₃ i) →+ L₃ := ∑ i, (F i).comp (Pi.evalAddMonoidHom _ i)
  have hg₃ : ∀ i n x, g₃ (Pi.single i (n ⊗ₜ x)) = f₃ i n x := by
    intro i n x
    simp only [g₃, AddMonoidHom.finsetSum_apply, AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply]
    rw [Finset.sum_eq_single i]
    · simp [hF]
    · intro k _ hk
      simp [Pi.single_eq_of_ne hk]
    · simp
  have b := five_add (piT (N := N) u₁) (piT (N := N) u₂) (piT (N := N) u₃) (piT (N := N) u₄) v₁ v₂ v₃ v₄
    g₁.toAddMonoidHom g₂.toAddMonoidHom g₃ g₄.toAddMonoidHom g₅.toAddMonoidHom
    (fun x => DFunLike.congr_fun (tens_ext (g₂.toAddMonoidHom.comp (piT (N := N) u₁)) (v₁.comp g₁.toAddMonoidHom)
      fun i n x => by simp [piT_single, hg₁, hg₂, c₁]) x)
    (fun x => DFunLike.congr_fun (tens_ext (g₃.comp (piT (N := N) u₂)) (v₂.comp g₂.toAddMonoidHom)
      fun i n x => by simp [piT_single, hg₂, hg₃, c₂]) x)
    (fun x => DFunLike.congr_fun (tens_ext (g₄.toAddMonoidHom.comp (piT (N := N) u₃)) (v₃.comp g₃)
      fun i n x => by simp [piT_single, hg₃, hg₄, c₃]) x)
    (fun x => DFunLike.congr_fun (tens_ext (g₅.toAddMonoidHom.comp (piT (N := N) u₄)) (v₄.comp g₄.toAddMonoidHom)
      fun i n x => by simp [piT_single, hg₄, hg₅, c₄]) x)
    (piT_exact u₁ u₂ eM₂) (piT_exact u₂ u₃ eM₃) (piT_exact u₃ u₄ eM₄) eL₂ eL₃ eL₄
    g₁.surjective g₂.bijective g₄.bijective g₅.injective
  exact ⟨AddEquiv.ofBijective g₃ b, hg₃⟩

end Alg

end GlobalTheory.CompanionTheory.LocBC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaNat
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'} (m : SMor Φ Φ' σ)

section Pts

variable {d : ℕ} (E : Frame Φ d) (E' : Frame Φ' d) (e : E.D ⟶ m.G.obj E'.D)

def Gp : Pt E' ⥤ Pt E where
  obj X := ⟨m.G.obj X.T, e ≫ m.G.map X.s⟩
  map {X Y} f := m.G.map (show X.T ⟶ Y.T from f)
  map_id X := m.G.map_id X.T
  map_comp {X Y Z} f g := m.G.map_comp (show X.T ⟶ Y.T from f) (show Y.T ⟶ Z.T from g)

def mPt (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') :
    CH.Mor (Pt.U E ⋙ sq a b) (Pt.U E' ⋙ sq a' b') σ where
  G := Gp m E E' e
  τ X := (m.sqC c ha hb).τ X.T
  nat {X Y} φ x := (m.sqC c ha hb).nat (show X.T ⟶ Y.T from φ) x

end Pts

section Cuts

variable {d : ℕ} (E : Frame Φ (d + 1)) (E' : Frame Φ' (d + 1)) (e : E.D ⟶ m.G.obj E'.D)
  (he : m.Fr E E' e) (hρ : ∀ T, Function.Injective (m.ρ T))

include he hρ in
theorem cut_mem {X Y : Cut E'} (φ : X ⟶ Y) :
    E.τ 0 ((e ≫ m.G.map X.s) ≫ m.G.map φ.1) (e ≫ m.G.map Y.s) = 0 := by
  apply hρ Y.T
  have h := he 0 (X.s ≫ φ.1) Y.s
  rw [map_zero, Category.assoc, ← m.G.map_comp, h]
  exact φ.2

def G1 : Cut E' ⥤ Cut E where
  obj X := ⟨m.G.obj X.T, e ≫ m.G.map X.s⟩
  map {X Y} φ := ⟨m.G.map φ.1, cut_mem m E E' e he hρ φ⟩
  map_id X := Cut.hom_ext (m.G.map_id X.T)
  map_comp {X Y Z} f g := Cut.hom_ext (m.G.map_comp f.1 g.1)

def m1 : SMor (Cut.Φ1 E) (Cut.Φ1 E') σ where
  G := G1 m E E' e he hρ
  ρ T := m.ρ T.T
  comm T r := m.comm T.T r
  nat {T T'} φ x := m.nat φ.1 x
  mem T x hx := m.mem T.T hx
  dp T k x hx := m.dp T.T k hx

def e1 : (Cut.E1 E).D ⟶ (G1 m E E' e he hρ).obj (Cut.E1 E').D :=
  ⟨e, by
    change E.τ 0 (𝟙 E.D ≫ e) (e ≫ m.G.map (𝟙 E'.D)) = 0
    rw [Category.id_comp, m.G.map_id, Category.comp_id]
    exact E.τ_self 0 e⟩

theorem fr1 : (m1 m E E' e he hρ).Fr (Cut.E1 E) (Cut.E1 E') (e1 m E E' e he hρ) :=
  fun i {T} s s' => he i.succ s.1 s'.1

variable (Q : Poly Φ) (Q' : Poly Φ')

def etaC (X : Pt E') : (Cut.P0 Q).obj ((Gp m E E' e).obj X) ⟶ (G1 m E E' e he hρ).obj ((Cut.P0 Q').obj X) :=
  Cut.adjInv Q _ _ (m.G.map (Q'.j X.T))

theorem j_eta (X : Pt E') : Q.j (m.G.obj X.T) ≫ (etaC m E E' e he hρ Q Q' X).1 = m.G.map (Q'.j X.T) :=
  Cut.adjInv_j Q ((Gp m E E' e).obj X) ((G1 m E E' e he hρ).obj ((Cut.P0 Q').obj X)) (m.G.map (Q'.j X.T))

theorem rho_eta (X : Pt E') :
    m.ρ (Q'.P X.T) ((Φ.A.map (etaC m E E' e he hρ Q Q' X).1).hom (Q.X (m.G.obj X.T))) = Q'.X X.T := by
  have h1 : (Φ.A.map (etaC m E E' e he hρ Q Q' X).1).hom (Q.X (m.G.obj X.T)) =
      E.τ 0 ((e ≫ m.G.map X.s) ≫ m.G.map (Q'.j X.T)) (e ≫ m.G.map (Cut.sec Q' X)) :=
    Q.lift_X (m.G.map (Q'.j X.T)) _ (E.mem 0 _ _)
  rw [h1, Category.assoc, ← m.G.map_comp, he 0 (X.s ≫ Q'.j X.T) (Cut.sec Q' X), Cut.sec_spec, if_pos rfl]

theorem eta_nat {X Y : Pt E'} (φ : X.T ⟶ Y.T) :
    Cut.Pmap (X := (Gp m E E' e).obj X) (Y := (Gp m E E' e).obj Y) Q (m.G.map φ) ≫ (etaC m E E' e he hρ Q Q' Y).1 =
      (etaC m E E' e he hρ Q Q' X).1 ≫ m.G.map (Cut.Pmap (X := X) (Y := Y) Q' φ) := by
  have e1 : Q.j (m.G.obj X.T) ≫ Cut.Pmap (X := (Gp m E E' e).obj X) (Y := (Gp m E E' e).obj Y) Q (m.G.map φ) =
      m.G.map φ ≫ Q.j (m.G.obj Y.T) := Cut.Pmap_j (X := (Gp m E E' e).obj X) (Y := (Gp m E E' e).obj Y) Q (m.G.map φ)
  have e2 : Q'.j X.T ≫ Cut.Pmap (X := X) (Y := Y) Q' φ = φ ≫ Q'.j Y.T := Cut.Pmap_j (X := X) (Y := Y) Q' φ
  have e3 : Q.j (m.G.obj X.T) ≫ Cut.Pmap (X := (Gp m E E' e).obj X) (Y := (Gp m E E' e).obj Y) Q (m.G.map φ) ≫
      (etaC m E E' e he hρ Q Q' Y).1 = Q.j (m.G.obj X.T) ≫ (etaC m E E' e he hρ Q Q' X).1 ≫
        m.G.map (Cut.Pmap (X := X) (Y := Y) Q' φ) := by
    rw [← Category.assoc, e1, Category.assoc, j_eta, ← Category.assoc (Q.j _), j_eta, ← m.G.map_comp, ← m.G.map_comp, e2]
  have e4 := Cut.truncation_hom_ext Q (X := (Gp m E E' e).obj X) (Y := (G1 m E E' e he hρ).obj ((Cut.P0 Q').obj Y))
    (ψ := (Cut.P0 Q).map (show (Gp m E E' e).obj X ⟶ (Gp m E E' e).obj Y from m.G.map φ) ≫ etaC m E E' e he hρ Q Q' Y)
    (ψ' := etaC m E E' e he hρ Q Q' X ≫ (G1 m E E' e he hρ).map ((Cut.P0 Q').map (show X ⟶ Y from φ))) e3
  exact congrArg Subtype.val e4

def eta : Gp m E E' e ⋙ Cut.P0 Q ⟶ Cut.P0 Q' ⋙ G1 m E E' e he hρ where
  app X := etaC m E E' e he hρ Q Q' X
  naturality {X Y} φ := Cut.hom_ext (eta_nat m E E' e he hρ Q Q' (X := X) (Y := Y) φ)

def mP (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') :
    CH.Mor (Cut.P0 Q ⋙ Cut.U E ⋙ sq a b) (Cut.P0 Q' ⋙ Cut.U E' ⋙ sq a' b') σ where
  G := Gp m E E' e
  τ X := ((m.sqC c ha hb).τ (Q'.P X.T)).comp ((sq a b).map (etaC m E E' e he hρ Q Q' X).1).hom
  nat {X Y} φ x := by
    have key : ∀ (φ : X.T ⟶ Y.T) (x : sqM a b (Q.P (m.G.obj X.T))),
        (m.sqC c ha hb).τ (Q'.P Y.T) (((sq a b).map (etaC m E E' e he hρ Q Q' Y).1).hom
          (((sq a b).map (Cut.Pmap (X := (Gp m E E' e).obj X) (Y := (Gp m E E' e).obj Y) Q (m.G.map φ))).hom x)) =
        ((sq a' b').map (Cut.Pmap (X := X) (Y := Y) Q' φ)).hom
          ((m.sqC c ha hb).τ (Q'.P X.T) (((sq a b).map (etaC m E E' e he hρ Q Q' X).1).hom x)) := by
      intro φ x
      rw [← (m.sqC c ha hb).nat]
      congr 1
      have h := eta_nat m E E' e he hρ Q Q' (X := X) (Y := Y) φ
      have h2 := congrArg (fun t => ((sq a b).map t).hom x) h
      simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h2
      exact h2
    exact key φ x

end Cuts

end GlobalTheory.CompanionTheory.LocBC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClsCongr
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

universe w w'

section LES

theorem cls_congr {R : Type} [CommRing R] {K : Cx.{w} R} {n : ℕ} {x y : K.X n} (h : x = y) (hx : K.d n x = 0)
    (hy : K.d n y = 0) : K.cls x hx = K.cls y hy := by
  subst h; rfl

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}

theorem sq_mapH {K L : Cx.{w} R} {K' L' : Cx.{w'} R'} (φ : Cx.Hom K L (RingHom.id R)) (ψ : Cx.Hom L L' σ)
    (φ' : Cx.Hom K' L' (RingHom.id R')) (ψ' : Cx.Hom K K' σ)
    (h : ∀ n x, ψ.f n (φ.f n x) = φ'.f n (ψ'.f n x)) (n : ℕ) (z : K.H n) :
    ψ.mapH n (φ.mapH n z) = φ'.mapH n (ψ'.mapH n z) := by
  obtain ⟨x, hx, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K n).1 z
  have c1 : L.d n (φ.f n x) = 0 := by rw [φ.comm, hx, map_zero]
  have c2 : L'.d n (ψ.f n (φ.f n x)) = 0 := by rw [ψ.comm, c1, map_zero]
  have c3 : K'.d n (ψ'.f n x) = 0 := by rw [ψ'.comm, hx, map_zero]
  have c4 : L'.d n (φ'.f n (ψ'.f n x)) = 0 := by rw [φ'.comm, c3, map_zero]
  rw [CrystallineSemistableComparison.P.mapH_cls φ n x hx c1, CrystallineSemistableComparison.P.mapH_cls ψ n _ c1 c2, CrystallineSemistableComparison.P.mapH_cls ψ' n x hx c3,
    CrystallineSemistableComparison.P.mapH_cls φ' n _ c3 c4]
  exact cls_congr (h n x) _ _

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

theorem tens_les [∀ i, Module.Flat R (N i)]
    {K L M : ι → Cx.{w} R} {K' L' M' : Cx.{w'} R'}
    (f : ∀ i, Cx.Hom (K i) (L i) (RingHom.id R)) (g : ∀ i, Cx.Hom (L i) (M i) (RingHom.id R))
    (hf : ∀ i n, Function.Injective ((f i).f n)) (hfg : ∀ i n, Function.Exact ((f i).f n) ((g i).f n))
    (hg : ∀ i n, Function.Surjective ((g i).f n))
    (f' : Cx.Hom K' L' (RingHom.id R')) (g' : Cx.Hom L' M' (RingHom.id R'))
    (hf' : ∀ n, Function.Injective (f'.f n)) (hfg' : ∀ n, Function.Exact (f'.f n) (g'.f n))
    (hg' : ∀ n, Function.Surjective (g'.f n))
    (a : ∀ i, N i → Cx.Hom (K i) K' σ) (b : ∀ i, N i → Cx.Hom (L i) L' σ) (c : ∀ i, N i → Cx.Hom (M i) M' σ)
    (hab : ∀ i n k x, (b i n).f k ((f i).f k x) = f'.f k ((a i n).f k x))
    (hbc : ∀ i n k x, (c i n).f k ((g i).f k x) = g'.f k ((b i n).f k x))
    (hL : ∀ j, Tens R (N := N) (M := fun i => (L i).H j) (M' := L'.H j) fun i n x => (b i n).mapH j x)
    (hM : ∀ j, Tens R (N := N) (M := fun i => (M i).H j) (M' := M'.H j) fun i n x => (c i n).mapH j x)
    (hadd : ∀ i j, ∃ F : N i ⊗[R] (K i).H j →+ K'.H j, ∀ n x, F (n ⊗ₜ x) = (a i n).mapH j x) :
    ∀ j, Tens R (N := N) (M := fun i => (K i).H j) (M' := K'.H j) fun i n x => (a i n).mapH j x := by
  intro j
  choose δ hδ h0 e1 e2 e3 using fun i => CrystallineSemistableComparison.P.les (f i) (g i) (hf i) (hfg i) (hg i)
  obtain ⟨δ', hδ', h0', e1', e2', e3'⟩ := CrystallineSemistableComparison.P.les f' g' hf' hfg' hg'
  have dcomm : ∀ i n k z, (a i n).mapH (k + 1) (δ i k z) = δ' k ((c i n).mapH k z) := by
    intro i n k z
    obtain ⟨m, hm, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (M i) k).1 z
    obtain ⟨y, rfl⟩ := hg i k m
    obtain ⟨x, hx⟩ := CrystallineSemistableComparison.CechClassBoundaries.conn_ex (f i) (g i) (hfg i) y hm
    have hxc := CrystallineSemistableComparison.CechClassBoundaries.conn_cyc (f i) (hf i) y x hx
    have c3 : K'.d (k + 1) ((a i n).f (k + 1) x) = 0 := by rw [(a i n).comm, hxc, map_zero]
    have c4 : M'.d k ((c i n).f k ((g i).f k y)) = 0 := by rw [(c i n).comm, hm, map_zero]
    have c5 : M'.d k (g'.f k ((b i n).f k y)) = 0 := by rw [← hbc]; exact c4
    rw [hδ i k y x hm hxc hx, CrystallineSemistableComparison.P.mapH_cls (a i n) _ x hxc c3, CrystallineSemistableComparison.P.mapH_cls (c i n) k _ hm c4,
      cls_congr (hbc i n k y) c4 c5, hδ' k _ _ c5 c3 (by rw [← hab, hx, (b i n).comm])]
  cases j with
  | zero =>
    refine tens_five (M₁ := fun _ => PUnit.{w + 1}) (M₂ := fun _ => PUnit.{w + 1}) (L₁ := PUnit.{w' + 1}) (L₂ := PUnit.{w' + 1})
      (fun _ => 0) (fun _ => 0) (fun i => (f i).mapH 0) (fun i => (g i).mapH 0)
      0 0 (f'.mapH 0).toAddMonoidHom (g'.mapH 0).toAddMonoidHom
      (fun _ _ _ => 0) (fun _ _ _ => 0) _ (fun i n x => (b i n).mapH 0 x) (fun i n x => (c i n).mapH 0 x)
      (fun _ _ _ => rfl) (fun i n x => ?_) (fun i n x => ?_) (fun i n x => ?_)
      (fun i y => by simp) (fun i y => ?_) (fun i => e1 i 0)
      (fun y => by simp) (fun y => ?_) (e1' 0)
      (tens_zero (fun _ => inferInstance) inferInstance _) (tens_zero (fun _ => inferInstance) inferInstance _)
      (hL 0) (hM 0) (fun i => hadd i 0)
    · have : (0 : PUnit.{w + 1} →ₗ[R] (K i).H 0) x = 0 := rfl
      simp
    · exact sq_mapH (f i) (b i n) f' (a i n) (hab i n) 0 x
    · exact sq_mapH (g i) (c i n) g' (b i n) (hbc i n) 0 x
    · constructor
      · intro h
        have : y = 0 := h0 i (h.trans (map_zero _).symm)
        exact ⟨0, by simp [this]⟩
      · rintro ⟨t, rfl⟩
        simp
    · constructor
      · intro h
        have : y = 0 := h0' (h.trans (map_zero _).symm)
        exact ⟨0, by simp [this]⟩
      · rintro ⟨t, rfl⟩
        simp
  | succ k =>
    exact tens_five (fun i => (g i).mapH k) (fun i => δ i k) (fun i => (f i).mapH (k + 1)) (fun i => (g i).mapH (k + 1))
      (g'.mapH k).toAddMonoidHom (δ' k).toAddMonoidHom (f'.mapH (k + 1)).toAddMonoidHom (g'.mapH (k + 1)).toAddMonoidHom
      (fun i n x => (b i n).mapH k x) (fun i n x => (c i n).mapH k x) _
      (fun i n x => (b i n).mapH (k + 1) x) (fun i n x => (c i n).mapH (k + 1) x)
      (fun i n x => sq_mapH (g i) (c i n) g' (b i n) (hbc i n) k x) (fun i n x => dcomm i n k x)
      (fun i n x => sq_mapH (f i) (b i n) f' (a i n) (hab i n) (k + 1) x)
      (fun i n x => sq_mapH (g i) (c i n) g' (b i n) (hbc i n) (k + 1) x)
      (fun i => e2 i k) (fun i => e3 i k) (fun i => e1 i (k + 1)) (e2' k) (e3' k) (e1' (k + 1))
      (hL k) (hM k) (hL (k + 1)) (hM (k + 1)) (fun i => hadd i (k + 1))

end LES

end GlobalTheory.CompanionTheory.LocBC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SqCSmul
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'} (m : SMor Φ Φ' σ)

theorem sqC_add {c c' c'' : R'} (hc : c'' = c + c') {a b : IdF Φ.A} {a' b' : IdF Φ'.A}
    (ha : m.LeC c a a') (hb : m.LeC c b b') (ha' : m.LeC c' a a') (hb' : m.LeC c' b b')
    (ha'' : m.LeC c'' a a') (hb'' : m.LeC c'' b b') (T : C') (x : sqM a b (m.G.obj T)) :
    (m.sqC c'' ha'' hb'').τ T x = (m.sqC c ha hb).τ T x + (m.sqC c' ha' hb').τ T x := by
  subst hc
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ (algebraMap R' _ (c + c') * m.ρ T y) =
    Ideal.Quotient.mk _ (algebraMap R' _ c * m.ρ T y) + Ideal.Quotient.mk _ (algebraMap R' _ c' * m.ρ T y)
  rw [map_add (f := _), add_mul, map_add (f := _)]

theorem sqC_smul {c c' : R'} (r : R) (hc : c' = σ r * c) {a b : IdF Φ.A} {a' b' : IdF Φ'.A}
    (ha : m.LeC c a a') (hb : m.LeC c b b') (ha' : m.LeC c' a a') (hb' : m.LeC c' b b') (T : C')
    (x : sqM a b (m.G.obj T)) :
    (m.sqC c' ha' hb').τ T x = (m.sqC c ha hb).τ T (r • x) := by
  subst hc
  rw [LinearMap.map_smulₛₗ]
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ (algebraMap R' _ (σ r * c) * m.ρ T y) =
    σ r • Ideal.Quotient.mk _ (algebraMap R' _ c * m.ρ T y)
  have h : ∀ z : Φ'.A.obj T, Ideal.Quotient.mk (b'.S T) (algebraMap R' _ (σ r) * z) = σ r • Ideal.Quotient.mk (b'.S T) z :=
    fun z => by rw [← Algebra.smul_def]; rfl
  rw [← h, ← mul_assoc, ← map_mul]

section Pts

variable {d : ℕ} (E : Frame (Φ := Φ) d) (E' : Frame (Φ := Φ') d) (e : E.D ⟶ m.G.obj E'.D)

theorem mPt_add {c c' c'' : R'} (hc : c'' = c + c') {a b : IdF Φ.A} {a' b' : IdF Φ'.A}
    (ha : m.LeC c a a') (hb : m.LeC c b b') (ha' : m.LeC c' a a') (hb' : m.LeC c' b b')
    (ha'' : m.LeC c'' a a') (hb'' : m.LeC c'' b b') (j : ℕ) (x : CH.H (Pt.U E ⋙ sq a b) j) :
    (mPt m E E' e c'' ha'' hb'').pull j x = (mPt m E E' e c ha hb).pull j x + (mPt m E E' e c' ha' hb').pull j x := by
  obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx _) j).1 x
  have h1 := CrystallineSemistableComparison.CechClassBoundaries.cyc (mPt m E E' e c'' ha'' hb'').hom f hf
  have h2 := CrystallineSemistableComparison.CechClassBoundaries.cyc (mPt m E E' e c ha hb).hom f hf
  have h3 := CrystallineSemistableComparison.CechClassBoundaries.cyc (mPt m E E' e c' ha' hb').hom f hf
  change (mPt m E E' e c'' ha'' hb'').hom.mapH j _ = (mPt m E E' e c ha hb).hom.mapH j _ + (mPt m E E' e c' ha' hb').hom.mapH j _
  rw [CrystallineSemistableComparison.P.mapH_cls _ j f hf h1, CrystallineSemistableComparison.P.mapH_cls _ j f hf h2, CrystallineSemistableComparison.P.mapH_cls _ j f hf h3,
    ← (CrystallineSemistableComparison.P.cls_surj _ j).2.2.2.1 _ _ h2 h3 (by rw [map_add (f := _), h2, h3, add_zero])]
  exact cls_congr (funext fun s => sqC_add m hc ha hb ha' hb' ha'' hb'' _ _) _ _

theorem mPt_smul {c c' : R'} (r : R) (hc : c' = σ r * c) {a b : IdF Φ.A} {a' b' : IdF Φ'.A}
    (ha : m.LeC c a a') (hb : m.LeC c b b') (ha' : m.LeC c' a a') (hb' : m.LeC c' b b')
    (j : ℕ) (x : CH.H (Pt.U E ⋙ sq a b) j) :
    (mPt m E E' e c' ha' hb').pull j x = (mPt m E E' e c ha hb).pull j (r • x) := by
  obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx _) j).1 x
  have h0 : CH.d _ j (r • f) = 0 := by rw [map_smul]; exact (show r • CH.d _ j f = 0 by rw [show CH.d _ j f = 0 from hf, smul_zero])
  have h1 := CrystallineSemistableComparison.CechClassBoundaries.cyc (mPt m E E' e c' ha' hb').hom f hf
  have h2 := CrystallineSemistableComparison.CechClassBoundaries.cyc (mPt m E E' e c ha hb).hom (r • f) h0
  rw [← (CrystallineSemistableComparison.P.cls_surj _ j).2.2.2.2 r f hf h0]
  change (mPt m E E' e c' ha' hb').hom.mapH j _ = (mPt m E E' e c ha hb).hom.mapH j _
  rw [CrystallineSemistableComparison.P.mapH_cls _ j f hf h1, CrystallineSemistableComparison.P.mapH_cls _ j _ h0 h2]
  exact cls_congr (funext fun s => sqC_smul m r hc ha hb ha' hb' _ _) _ _

theorem pull_U (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') (j : ℕ)
    (x : CH.H (sq a b) j) :
    (mPt m E E' e c ha hb).pull j ((CH.Mor.restrict (sq a b) (Pt.U E)).pull j x) =
      (CH.Mor.restrict (sq a' b') (Pt.U E')).pull j ((m.sqC c ha hb).pull j x) := by
  obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx _) j).1 x
  rfl

end Pts

section HAdd

variable {R'' : Type} [CommRing R''] [Algebra R R''] {Ψ : PDF R'' C'} (p : SMor Φ Ψ (algebraMap R R''))
  {d : ℕ} (E : Frame (Φ := Φ) d) (E' : Frame (Φ := Ψ) d) (e : E.D ⟶ p.G.obj E'.D)

theorem hadd_Pt {N : Type} [AddCommGroup N] [Module R N] (ν : N →ₗ[R] R'') {a b : IdF Φ.A} {a' b' : IdF Ψ.A}
    (ha : ∀ n, p.LeC (ν n) a a') (hb : ∀ n, p.LeC (ν n) b b') (j : ℕ) :
    ∃ F : N ⊗[R] CH.H (Pt.U E ⋙ sq a b) j →+ CH.H (Pt.U E' ⋙ sq a' b') j,
      ∀ n x, F (n ⊗ₜ x) = (mPt p E E' e (ν n) (ha n) (hb n)).pull j x := by
  let f : N →+ (CH.H (Pt.U E ⋙ sq a b) j →+ CH.H (Pt.U E' ⋙ sq a' b') j) :=
    AddMonoidHom.mk' (fun n => ((mPt p E E' e (ν n) (ha n) (hb n)).pull j).toAddMonoidHom) (fun n n' => AddMonoidHom.ext fun x =>
      mPt_add p E E' e (map_add ν n n') (ha n) (hb n) (ha n') (hb n') (ha _) (hb _) j x)
  refine ⟨TensorProduct.liftAddHom f fun r n x => ?_, fun n x => ?_⟩
  · exact mPt_smul p E E' e r (by rw [map_smul, Algebra.smul_def]) (ha n) (hb n) (ha _) (hb _) j x
  · exact TensorProduct.liftAddHom_tmul _ _ _ _

end HAdd

end GlobalTheory.CompanionTheory.LocBC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullRestrictFirstPieceCompat
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'} (m : SMor Φ Φ' σ)

section Cuts

variable {d : ℕ} (E : Frame (Φ := Φ) (d + 1)) (E' : Frame (Φ := Φ') (d + 1)) (e : E.D ⟶ m.G.obj E'.D)
  (he : m.Fr E E' e) (hρ : ∀ T, Function.Injective (m.ρ T)) (Q : Poly Φ) (Q' : Poly Φ')

theorem le_cover_restrict_compat {c : R'} {a : IdF Φ.A} {a' : IdF Φ'.A} (h : m.LeC c a a') :
    (m1 m E E' e he hρ).LeC c (a.res (Cut.U E)) (a'.res (Cut.U E')) := fun T x hx => h T.T x hx

theorem pull_restrict_first_piece_compat (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') (j : ℕ)
    (x : CH.H (sq (a.res (Cut.U E)) (b.res (Cut.U E))) j) :
    (mP m E E' e he hρ Q Q' c ha hb).pull j
        ((CH.Mor.restrict (sq (a.res (Cut.U E)) (b.res (Cut.U E))) (Cut.P0 Q)).pull j x) =
      (CH.Mor.restrict (sq (a'.res (Cut.U E')) (b'.res (Cut.U E'))) (Cut.P0 Q')).pull j
        (((m1 m E E' e he hρ).sqC c (le_cover_restrict_compat m E E' e he hρ ha) (le_cover_restrict_compat m E E' e he hρ hb)).pull j x) := by
  let μ₁ : CH.Mor (sq (a.res (Cut.U E)) (b.res (Cut.U E))) (Cut.P0 Q' ⋙ Cut.U E' ⋙ sq a' b') σ :=
    (CH.Mor.restrict (sq (a.res (Cut.U E)) (b.res (Cut.U E))) (Cut.P0 Q)).comp (mP m E E' e he hρ Q Q' c ha hb)
  let μ₂ : CH.Mor (sq (a.res (Cut.U E)) (b.res (Cut.U E))) (Cut.P0 Q' ⋙ Cut.U E' ⋙ sq a' b') σ :=
    ((m1 m E E' e he hρ).sqC c (le_cover_restrict_compat m E E' e he hρ ha) (le_cover_restrict_compat m E E' e he hρ hb)).comp
      (CH.Mor.restrict (sq (a'.res (Cut.U E')) (b'.res (Cut.U E'))) (Cut.P0 Q'))
  have h := CrystallineSemistableComparison.P.prism μ₁ μ₂ (eta m E E' e he hρ Q Q') (fun T x => rfl) j x
  exact (CrystallineSemistableComparison.P.pull_comp _ _ j x).1.symm.trans (h.trans (CrystallineSemistableComparison.P.pull_comp _ _ j x).1)

def alpha {d : ℕ} {E : Frame (Φ := Φ) (d + 1)} (Q : Poly Φ) (a b : IdF Φ.A) : Pt.U E ⋙ sq a b ⟶ Cut.P0 Q ⋙ Cut.U E ⋙ sq a b :=
  Functor.whiskerRight (Cut.jNat (E := E) Q) (sq a b)

theorem alpha_τ (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') (X : Pt E')
    (y : sqM a b (m.G.obj X.T)) :
    (mP m E E' e he hρ Q Q' c ha hb).τ X (((alpha Q a b).app ((Gp m E E' e).obj X)).hom y) =
      ((alpha Q' a' b').app X).hom ((mPt m E E' e c ha hb).τ X y) := by
  change (m.sqC c ha hb).τ (Q'.P X.T) (((sq a b).map (etaC m E E' e he hρ Q Q' X).1).hom
      (((sq a b).map (Q.j (m.G.obj X.T))).hom y)) = ((sq a' b').map (Q'.j X.T)).hom ((m.sqC c ha hb).τ X.T y)
  rw [← (m.sqC c ha hb).nat]
  congr 1
  have h2 := congrArg (fun t => ((sq a b).map t).hom y) (j_eta m E E' e he hρ Q Q' X)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2

theorem alpha_hom (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') (k : ℕ)
    (x : CH.Cn (Pt.U E ⋙ sq a b) k) :
    (mP m E E' e he hρ Q Q' c ha hb).hom.f k ((CH.Mor.ofNatTrans (alpha Q a b)).hom.f k x) =
      (CH.Mor.ofNatTrans (alpha Q' a' b')).hom.f k ((mPt m E E' e c ha hb).hom.f k x) :=
  funext fun s => alpha_τ m E E' e he hρ Q Q' c ha hb _ _

theorem rho_finsupp_sum_dpow (c : R') {T P' : C'} (jj : T ⟶ P') (η : Q.P (m.G.obj T) ⟶ m.G.obj P') (X' : Φ'.A.obj P')
    (hj : Q.j (m.G.obj T) ≫ η = m.G.map jj) (hx : m.ρ P' ((Φ.A.map η).hom (Q.X (m.G.obj T))) = X')
    (cc : ℕ →₀ Φ.A.obj (m.G.obj T)) :
    algebraMap R' (Φ'.A.obj P') c * m.ρ P' ((Φ.A.map η).hom
        (cc.sum fun k y => (Φ.A.map (Q.j (m.G.obj T))).hom y * Φ.dp k (Q.X (m.G.obj T)))) =
      (cc.mapRange (fun x => algebraMap R' (Φ'.A.obj T) c * m.ρ T x) (by simp)).sum
        fun k y => (Φ'.A.map jj).hom y * Φ'.dp k X' := by
  rw [Finsupp.sum_mapRange_index (by intro k; simp), map_finsuppSum, map_finsuppSum, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun k _ => ?_
  have hX := Q.X_mem (m.G.obj T)
  have hX' := Φ.J.map_mem η hX
  have h1 : (Φ.A.map η).hom ((Φ.A.map (Q.j (m.G.obj T))).hom (cc k)) = (Φ.A.map (m.G.map jj)).hom (cc k) := by
    rw [← Cut.mapA_comp, hj]
  rw [map_mul, map_mul, h1, m.nat, Φ.dp_map _ _ hX, m.dp _ _ hX', hx, map_mul, AlgHom.commutes, mul_assoc]

theorem rho_sum (c : R') (X : Pt E') (cc : ℕ →₀ Φ.A.obj (m.G.obj X.T)) :
    algebraMap R' (Φ'.A.obj (Q'.P X.T)) c * m.ρ (Q'.P X.T) ((Φ.A.map (etaC m E E' e he hρ Q Q' X).1).hom
        (cc.sum fun k y => (Φ.A.map (Q.j (m.G.obj X.T))).hom y * Φ.dp k (Q.X (m.G.obj X.T)))) =
      (cc.mapRange (fun x => algebraMap R' (Φ'.A.obj X.T) c * m.ρ X.T x) (by simp)).sum
        fun k y => (Φ'.A.map (Q'.j X.T)).hom y * Φ'.dp k (Q'.X X.T) :=
  rho_finsupp_sum_dpow m Q c (Q'.j X.T) (etaC m E E' e he hρ Q Q' X).1 (Q'.X X.T) (j_eta m E E' e he hρ Q Q' X)
    (rho_eta m E E' e he hρ Q Q' X) cc

theorem beta_τ {a b : ℤ → IdF Φ.A} {a' b' : ℤ → IdF Φ'.A} {r : ℤ} (c : R')
    (ha : ∀ r', m.LeC c (a r') (a' r')) (hb : ∀ r', m.LeC c (b r') (b' r'))
    (hca : Q.Crit a r) (hca1 : Q.Crit a (r - 1))
    (β : Cut.P0 Q ⋙ Cut.U E ⋙ sq (a r) (b r) ⟶ Cut.P0 Q ⋙ Cut.U E ⋙ sq (a (r - 1)) (b (r - 1)))
    (hβ : ∀ (X : Pt E) (c c' : ℕ →₀ Φ.A.obj X.T) (z : sqM (a r) (b r) (Q.P X.T)) (z' : sqM (a (r - 1)) (b (r - 1)) (Q.P X.T)),
        (∀ k, c' k = c (k + 1)) →
        z.1 = Ideal.Quotient.mk _ (c.sum fun k y => (Φ.A.map (Q.j X.T)).hom y * Φ.dp k (Q.X X.T)) →
        z'.1 = Ideal.Quotient.mk _ (c'.sum fun k y => (Φ.A.map (Q.j X.T)).hom y * Φ.dp k (Q.X X.T)) →
        (β.app X).hom z = z')
    (β' : Cut.P0 Q' ⋙ Cut.U E' ⋙ sq (a' r) (b' r) ⟶ Cut.P0 Q' ⋙ Cut.U E' ⋙ sq (a' (r - 1)) (b' (r - 1)))
    (hβ' : ∀ (X : Pt E') (c c' : ℕ →₀ Φ'.A.obj X.T) (z : sqM (a' r) (b' r) (Q'.P X.T)) (z' : sqM (a' (r - 1)) (b' (r - 1)) (Q'.P X.T)),
        (∀ k, c' k = c (k + 1)) →
        z.1 = Ideal.Quotient.mk _ (c.sum fun k y => (Φ'.A.map (Q'.j X.T)).hom y * Φ'.dp k (Q'.X X.T)) →
        z'.1 = Ideal.Quotient.mk _ (c'.sum fun k y => (Φ'.A.map (Q'.j X.T)).hom y * Φ'.dp k (Q'.X X.T)) →
        (β'.app X).hom z = z')
    (X : Pt E') (y : sqM (a r) (b r) (Q.P (m.G.obj X.T))) :
    (mP m E E' e he hρ Q Q' c (ha (r - 1)) (hb (r - 1))).τ X ((β.app ((Gp m E E' e).obj X)).hom y) =
      (β'.app X).hom ((mP m E E' e he hρ Q Q' c (ha r) (hb r)).τ X y) := by
  obtain ⟨y, hy⟩ := y
  obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hy
  obtain ⟨cc, rfl⟩ := Q.span _ w
  have hmem := (hca (m.G.obj X.T) cc).1 hw
  let c' : ℕ →₀ Φ.A.obj (m.G.obj X.T) := cc.comapDomain (· + 1) (fun _ _ _ _ h => Nat.add_right_cancel h)
  have hc' : ∀ k, c' k = cc (k + 1) := fun k => Finsupp.comapDomain_apply _ _ _ _
  have hw' := (hca1 (m.G.obj X.T) c').2 fun k => by
    rw [hc']
    have h := hmem (k + 1)
    rwa [show r - ((k + 1 : ℕ) : ℤ) = r - 1 - (k : ℤ) by push_cast; ring] at h
  have hb1 := hβ ((Gp m E E' e).obj X) cc c' ⟨_, hy⟩ ⟨_, Ideal.mem_map_of_mem _ hw'⟩ hc' rfl rfl
  rw [hb1]
  symm
  refine hβ' X (cc.mapRange (fun x => algebraMap R' (Φ'.A.obj X.T) c * m.ρ X.T x) (by simp))
    (c'.mapRange (fun x => algebraMap R' (Φ'.A.obj X.T) c * m.ρ X.T x) (by simp)) _ _ (fun k => ?_) ?_ ?_
  · rw [Finsupp.mapRange_apply, Finsupp.mapRange_apply, hc']
  · exact congrArg (Ideal.Quotient.mk _) (rho_sum m E E' e he hρ Q Q' c X cc)
  · exact congrArg (Ideal.Quotient.mk _) (rho_sum m E E' e he hρ Q Q' c X c')

end Cuts

end GlobalTheory.CompanionTheory.LocBC
end
end

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

section Initial

universe u v w

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) {D : C} (hD : Limits.IsInitial D)

def toH0 : F.obj D →ₗ[R] CH.H F 0 where
  toFun x := (CH.cx F).cls (CH.aug F (fun T => (F.map (hD.to T)).hom) x) ((CrystallineSemistableComparison.P.initial F D hD).1 x)
  map_add' x y := by
    have := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) 0).2.2.2.1 _ _ ((CrystallineSemistableComparison.P.initial F D hD).1 x) ((CrystallineSemistableComparison.P.initial F D hD).1 y)
      (by rw [map_add (f := _), (CrystallineSemistableComparison.P.initial F D hD).1 x, (CrystallineSemistableComparison.P.initial F D hD).1 y, add_zero])
    exact (cls_congr (map_add _ x y) _ _).trans this
  map_smul' r x := by
    have := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) 0).2.2.2.2 r _ ((CrystallineSemistableComparison.P.initial F D hD).1 x)
      (by rw [map_smul, (CrystallineSemistableComparison.P.initial F D hD).1 x, smul_zero])
    exact (cls_congr (map_smul _ r x) _ _).trans this

theorem toH0_bijective_of_initial : Function.Bijective (toH0 F hD) := by
  obtain ⟨h1, h2, h3, -⟩ := CrystallineSemistableComparison.P.initial F D hD
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h := ((CrystallineSemistableComparison.P.cls_surj (CH.cx F) 0).2.1 _ (h1 x)).1 hx
    have h' := h2 x ((Submodule.mem_bot R).1 h)
    rwa [one_smul] at h'
  · intro c
    obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) 0).1 c
    obtain ⟨x, hx⟩ := h3 f hf
    rw [one_smul] at hx
    exact ⟨x, cls_congr hx _ _⟩

include hD in
theorem H_succ_sub (j : ℕ) : Subsingleton (CH.H F (j + 1)) := by
  obtain ⟨-, -, -, hex⟩ := CrystallineSemistableComparison.P.initial F D hD
  have key : ∀ x : CH.H F (j + 1), x = 0 := by
    intro x
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) (j + 1)).1 x
    refine ((CrystallineSemistableComparison.P.cls_surj (CH.cx F) (j + 1)).2.1 a ha).2 ?_
    obtain ⟨y, hy⟩ := hex j a ha
    rw [one_smul] at hy
    exact ⟨y, hy⟩
  exact ⟨fun x y => by rw [key x, key y]⟩

end Initial

variable {R R' : Type} [CommRing R] [CommRing R'] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ι → Type}
  [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

section Base

variable {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'} (m : SMor Φ Φ' σ)

theorem base_case {D : C} {D' : C'} (hD : Limits.IsInitial D) (hD' : Limits.IsInitial D') (e : D ⟶ m.G.obj D')
    (ν : ∀ i, N i → R') (a b : ι → IdF Φ.A) (a' b' : IdF Φ'.A) (ha : ∀ i n, m.LeC (ν i n) (a i) a')
    (hb : ∀ i n, m.LeC (ν i n) (b i) b')
    (h : Tens R (N := N) (M := fun i => (sq (a i) (b i)).obj D) (M' := (sq a' b').obj D')
      fun i n x => (m.sqC (ν i n) (ha i n) (hb i n)).τ D' (((sq (a i) (b i)).map e).hom x)) (j : ℕ) :
    Tens R (N := N) (M := fun i => CH.H (sq (a i) (b i)) j) (M' := CH.H (sq a' b') j)
      fun i n x => (m.sqC (ν i n) (ha i n) (hb i n)).pull j x := by
  cases j with
  | zero =>
    refine tens_transfer (fun i => LinearEquiv.ofBijective (toH0 (sq (a i) (b i)) hD) (toH0_bijective_of_initial _ hD))
      (LinearEquiv.ofBijective (toH0 (sq a' b') hD') (toH0_bijective_of_initial _ hD')).toAddEquiv _ _ (fun i n x => ?_) h
    change (m.sqC (ν i n) (ha i n) (hb i n)).hom.mapH 0 (toH0 (sq (a i) (b i)) hD x) = toH0 (sq a' b') hD' _
    have h1 := (CrystallineSemistableComparison.P.initial (sq (a i) (b i)) D hD).1 x
    refine (CrystallineSemistableComparison.P.mapH_cls _ 0 _ h1 (CrystallineSemistableComparison.CechClassBoundaries.cyc _ _ h1)).trans (cls_congr (funext fun s => ?_) _ _)
    change (m.sqC (ν i n) (ha i n) (hb i n)).τ _ (((sq (a i) (b i)).map (hD.to (m.G.obj (s.obj (Fin.last 0))))).hom x) =
      ((sq a' b').map (hD'.to (s.obj (Fin.last 0)))).hom ((m.sqC (ν i n) (ha i n) (hb i n)).τ D' (((sq (a i) (b i)).map e).hom x))
    rw [← (m.sqC (ν i n) (ha i n) (hb i n)).nat]
    congr 1
    have h2 := congrArg (fun t => ((sq (a i) (b i)).map t).hom x)
      (hD.hom_ext (hD.to (m.G.obj (s.obj (Fin.last 0)))) (e ≫ m.G.map (hD'.to (s.obj (Fin.last 0)))))
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    exact h2
  | succ j => exact tens_zero (fun i => H_succ_sub _ hD j) (H_succ_sub _ hD' j) _

end Base

section Step

variable [Algebra R R'] [∀ i, Module.Flat R (N i)] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} (m : SMor Φ Φ' (algebraMap R R')) (Q : Poly Φ) (Q' : Poly Φ')
  {d : ℕ} (E : Frame Φ (d + 1)) (E' : Frame Φ' (d + 1)) (e : E.D ⟶ m.G.obj E'.D) (he : m.Fr E E' e)
  (hρ : ∀ T, Function.Injective (m.ρ T)) (ν : ∀ i, N i →ₗ[R] R')

theorem step (a b : ι → ℤ → IdF Φ.A) (a' b' : ℤ → IdF Φ'.A) (r : ℤ) (hQ : ∀ i, Q.Ladder (a i) (b i) r)
    (hQ' : Q'.Ladder a' b' r) (ha : ∀ i n r', m.LeC (ν i n) (a i r') (a' r')) (hb : ∀ i n r', m.LeC (ν i n) (b i r') (b' r'))
    (c1 : ∀ r₀, (r₀ = r ∨ r₀ = r - 1) → ∀ j, Tens R (N := N) (M := fun i => CH.H (sq ((a i r₀).res (Cut.U E)) ((b i r₀).res (Cut.U E))) j)
      (M' := CH.H (sq ((a' r₀).res (Cut.U E')) ((b' r₀).res (Cut.U E'))) j)
      fun i n x => ((m1 m E E' e he hρ).sqC (ν i n) (le_cover_restrict_compat m E E' e he hρ (ha i n r₀)) (le_cover_restrict_compat m E E' e he hρ (hb i n r₀))).pull j x)
    (j : ℕ) :
    Tens R (N := N) (M := fun i => CH.H (sq (a i r) (b i r)) j) (M' := CH.H (sq (a' r) (b' r)) j)
      fun i n x => (m.sqC (ν i n) (ha i n r) (hb i n r)).pull j x := by
  have hle : r - 1 ≤ r := by omega
  choose β hinj hex hsurj hform using fun i => GlobalTheory.T.filtration_critical_comparison_map Q E (a i) (b i) r (hQ i).le ((hQ i).ca r le_rfl)
    ((hQ i).ca _ hle) ((hQ i).cb r le_rfl) ((hQ i).cb _ hle)
  obtain ⟨β', hinj', hex', hsurj', hform'⟩ := GlobalTheory.T.filtration_critical_comparison_map Q' E' a' b' r hQ'.le (hQ'.ca r le_rfl)
    (hQ'.ca _ hle) (hQ'.cb r le_rfl) (hQ'.cb _ hle)
  have sI := fun i => CrystallineSemistableComparison.P.ses_cochains (alpha Q (a i r) (b i r)) (β i) (hinj i) (hex i) (hsurj i)
  have sP := CrystallineSemistableComparison.P.ses_cochains (alpha Q' (a' r) (b' r)) β' hinj' hex' hsurj'
  have hP : ∀ r₀, (r₀ = r ∨ r₀ = r - 1) → ∀ j, Tens R (N := N) (M := fun i => (CH.cx (Cut.P0 Q ⋙ Cut.U E ⋙ sq (a i r₀) (b i r₀))).H j)
      (M' := (CH.cx (Cut.P0 Q' ⋙ Cut.U E' ⋙ sq (a' r₀) (b' r₀))).H j)
      fun i n x => (mP m E E' e he hρ Q Q' (ν i n) (ha i n r₀) (hb i n r₀)).hom.mapH j x := by
    intro r₀ hr₀ j
    exact tens_transfer
      (fun i => LinearEquiv.ofBijective ((CH.Mor.restrict (sq ((a i r₀).res (Cut.U E)) ((b i r₀).res (Cut.U E))) (Cut.P0 Q)).pull j)
        (CrystallineSemistableComparison.P.adj _ (Cut.P0 Q) (Cut.inc E) (Cut.adj Q) j))
      ((LinearEquiv.ofBijective ((CH.Mor.restrict (sq ((a' r₀).res (Cut.U E')) ((b' r₀).res (Cut.U E'))) (Cut.P0 Q')).pull j)
        (CrystallineSemistableComparison.P.adj _ (Cut.P0 Q') (Cut.inc E') (Cut.adj Q') j)).toAddEquiv) _ _
      (fun i n x => pull_restrict_first_piece_compat m E E' e he hρ Q Q' (ν i n) (ha i n r₀) (hb i n r₀) j x) (c1 r₀ hr₀ j)
  have hPt := tens_les
    (K := fun i => CH.cx (Pt.U E ⋙ sq (a i r) (b i r)))
    (L := fun i => CH.cx (Cut.P0 Q ⋙ Cut.U E ⋙ sq (a i r) (b i r)))
    (M := fun i => CH.cx (Cut.P0 Q ⋙ Cut.U E ⋙ sq (a i (r - 1)) (b i (r - 1))))
    (K' := CH.cx (Pt.U E' ⋙ sq (a' r) (b' r)))
    (L' := CH.cx (Cut.P0 Q' ⋙ Cut.U E' ⋙ sq (a' r) (b' r)))
    (M' := CH.cx (Cut.P0 Q' ⋙ Cut.U E' ⋙ sq (a' (r - 1)) (b' (r - 1))))
    (fun i => (CH.Mor.ofNatTrans (alpha Q (a i r) (b i r))).hom) (fun i => (CH.Mor.ofNatTrans (β i)).hom)
    (fun i => (sI i).1) (fun i => (sI i).2.1) (fun i => (sI i).2.2)
    (CH.Mor.ofNatTrans (alpha Q' (a' r) (b' r))).hom (CH.Mor.ofNatTrans β').hom sP.1 sP.2.1 sP.2.2
    (fun i n => (mPt m E E' e (ν i n) (ha i n r) (hb i n r)).hom)
    (fun i n => (mP m E E' e he hρ Q Q' (ν i n) (ha i n r) (hb i n r)).hom)
    (fun i n => (mP m E E' e he hρ Q Q' (ν i n) (ha i n (r - 1)) (hb i n (r - 1))).hom)
    (fun i n k x => alpha_hom m E E' e he hρ Q Q' (ν i n) (ha i n r) (hb i n r) k x)
    (fun i n k x => funext fun s => beta_τ m E E' e he hρ Q Q' (ν i n) (ha i n) (hb i n) ((hQ i).ca r le_rfl)
      ((hQ i).ca _ hle) (β i) (hform i) β' hform' _ _)
    (hP r (Or.inl rfl)) (hP (r - 1) (Or.inr rfl))
    (fun i j => hadd_Pt m E E' e (ν i) (ha i · r) (hb i · r) j) j
  let u := fun i => LinearEquiv.ofBijective ((CH.Mor.restrict (sq (a i r) (b i r)) (Pt.U E)).pull j)
    (CrystallineSemistableComparison.P.adj _ (Pt.U E) (Pt.S E) (Pt.adj E) j)
  let u' := LinearEquiv.ofBijective ((CH.Mor.restrict (sq (a' r) (b' r)) (Pt.U E')).pull j)
    (CrystallineSemistableComparison.P.adj _ (Pt.U E') (Pt.S E') (Pt.adj E') j)
  refine tens_transfer (fun i => (u i).symm) u'.toAddEquiv.symm _ _ (fun i n x => ?_) hPt
  obtain ⟨z, rfl⟩ := (u i).surjective x
  rw [LinearEquiv.symm_apply_apply]
  symm
  refine (AddEquiv.symm_apply_eq u'.toAddEquiv).2 ?_
  exact pull_U m E E' e (ν i n) (ha i n r) (hb i n r) j z

end Step

section Main

variable [Algebra R R'] [∀ i, Module.Flat R (N i)]

theorem ladder_mono {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Q : Poly Φ} {a b : ℤ → IdF Φ.A} {r r₀ : ℤ}
    (h : Q.Ladder a b r) (hr : r₀ ≤ r) : Q.Ladder a b r₀ :=
  ⟨h.le, fun r' hr' => h.ca r' (hr'.trans hr), fun r' hr' => h.cb r' (hr'.trans hr)⟩

theorem main (ν : ∀ i, N i →ₗ[R] R') : ∀ (d : ℕ) {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {Φ : PDF R C} {Φ' : PDF R' C'} (m : SMor Φ Φ' (algebraMap R R')) (Q : Poly Φ) (Q' : Poly Φ')
    (E : Frame Φ d) (E' : Frame Φ' d) (e : E.D ⟶ m.G.obj E'.D) (he : m.Fr E E' e)
    (hρ : ∀ T, Function.Injective (m.ρ T)) (a b : ι → ℤ → IdF Φ.A) (a' b' : ℤ → IdF Φ'.A) (r : ℤ)
    (hQ : ∀ i, Q.Ladder (a i) (b i) r) (hQ' : Q'.Ladder a' b' r)
    (ha : ∀ i n r', m.LeC (ν i n) (a i r') (a' r')) (hb : ∀ i n r', m.LeC (ν i n) (b i r') (b' r')),
    (∀ r', r - d ≤ r' → r' ≤ r → Tens R (N := N) (M := fun i => (sq (a i r') (b i r')).obj E.D) (M' := (sq (a' r') (b' r')).obj E'.D)
      fun i n x => (m.sqC (ν i n) (ha i n r') (hb i n r')).τ E'.D (((sq (a i r') (b i r')).map e).hom x)) →
    ∀ j, Tens R (N := N) (M := fun i => CH.H (sq (a i r) (b i r)) j) (M' := CH.H (sq (a' r) (b' r)) j)
      fun i n x => (m.sqC (ν i n) (ha i n r) (hb i n r)).pull j x := by
  intro d
  induction d with
  | zero =>
    intro C C' _ _ Φ Φ' m Q Q' E E' e he hρ a b a' b' r hQ hQ' ha hb h j
    exact base_case m (Frame.initial E) (Frame.initial E') e (fun i n => ν i n) (fun i => a i r) (fun i => b i r) (a' r) (b' r)
      (fun i n => ha i n r) (fun i n => hb i n r) (h r (by simp) le_rfl) j
  | succ d ih =>
    intro C C' _ _ Φ Φ' m Q Q' E E' e he hρ a b a' b' r hQ hQ' ha hb h j
    refine step m Q Q' E E' e he hρ ν a b a' b' r hQ hQ' ha hb (fun r₀ hr₀ j => ?_) j
    have hle : r₀ ≤ r := by rcases hr₀ with rfl | rfl <;> omega
    have hlo : r - 1 ≤ r₀ := by rcases hr₀ with rfl | rfl <;> omega
    exact ih (m1 m E E' e he hρ) (Cut.Q1 Q) (Cut.Q1 Q') (Cut.E1 E) (Cut.E1 E') (e1 m E E' e he hρ) (fr1 m E E' e he hρ)
      (fun T => hρ T.T) (fun i r => (a i r).res (Cut.U E)) (fun i r => (b i r).res (Cut.U E))
      (fun r => (a' r).res (Cut.U E')) (fun r => (b' r).res (Cut.U E')) r₀
      (fun i => Cut.ladder_truncation Q (ladder_mono (hQ i) hle)) (Cut.ladder_truncation Q' (ladder_mono hQ' hle))
      (fun i n r' => le_cover_restrict_compat m E E' e he hρ (ha i n r')) (fun i n r' => le_cover_restrict_compat m E E' e he hρ (hb i n r'))
      (fun r' h1 h2 => h r' (by push_cast; omega) (h2.trans hle)) j

end Main

theorem local_base_change : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {Φ : PDF R C} {Φ' : PDF R' C'} (m : SMor Φ Φ' (algebraMap R R')) (Q : Poly Φ) (Q' : Poly Φ') {d : ℕ} (E : Frame Φ d)
    (E' : Frame Φ' d) (e : E.D ⟶ m.G.obj E'.D) (he : m.Fr E E' e) (hρ : ∀ T, Function.Injective (m.ρ T)) {ι : Type} [Fintype ι] [DecidableEq ι] (N : ι → Type)
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] [∀ i, Module.Flat R (N i)] (ν : ∀ i, N i →ₗ[R] R')
    (a b : ι → ℤ → IdF Φ.A) (a' b' : ℤ → IdF Φ'.A) (r : ℤ) (hQ : ∀ i, Q.Ladder (a i) (b i) r) (hQ' : Q'.Ladder a' b' r)
    (ha : ∀ i n r', m.LeC (ν i n) (a i r') (a' r')) (hb : ∀ i n r', m.LeC (ν i n) (b i r') (b' r')),
    (∀ r', r - d ≤ r' → r' ≤ r → Tens R (N := N) (M := fun i => (sq (a i r') (b i r')).obj E.D) (M' := (sq (a' r') (b' r')).obj E'.D)
      fun i n x => (m.sqC (ν i n) (ha i n r') (hb i n r')).τ E'.D (((sq (a i r') (b i r')).map e).hom x)) →
    ∀ j, Tens R (N := N) (M := fun i => CH.H (sq (a i r) (b i r)) j) (M' := CH.H (sq (a' r) (b' r)) j)
      fun i n x => (m.sqC (ν i n) (ha i n r) (hb i n r)).pull j x := by
  intro R R' _ _ _ C C' _ _ Φ Φ' m Q Q' d E E' e he hρ ι _ _ N _ _ _ ν a b a' b' r hQ hQ' ha hb h j
  exact main ν d m Q Q' E E' e he hρ a b a' b' r hQ hQ' ha hb h j

end GlobalTheory.CompanionTheory.LocBC
