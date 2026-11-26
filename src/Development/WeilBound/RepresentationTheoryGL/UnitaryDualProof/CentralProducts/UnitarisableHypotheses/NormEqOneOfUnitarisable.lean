module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.TopProdD
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.AdmissibleParabolicInduction.IrrAdm
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.AdmissibleParabolicInduction.AdmProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellFunctorNonscalarOffdiag

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.AdmissibleParabolicInduction.AddChar
namespace PositivityTheory.PfBern.Props1

open PositivityTheory.PfBern.Assembly

theorem existsAddChar_holds : ExistsAddChar := fun k _ _ _ _ =>
  GroundTheory.LocalField.exists_addChar_continuous_ne_one (K := k)

end PositivityTheory.PfBern.Props1
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.UnitaryAdmissibleComplements.UnitaryAdmissibleComplementHolds
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace PositivityTheory.PfBern.Props2

section General

variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X]

theorem finite_orbit_of_isSmooth {ρ : Representation ℂ G X} (hρ : IsSmooth ρ) (K : Subgroup G)
    (hK : IsCompact (K : Set G)) (w : X) : (Set.range fun k : K => ρ k w).Finite := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  refine IsLocallyConstant.range_finite ?_
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have hc : Continuous fun y : K => (x : G)⁻¹ * (y : G) := continuous_const.mul continuous_subtype_val
  have hU : IsOpen ((fun y : K => (x : G)⁻¹ * (y : G)) ⁻¹' {g : G | ρ g w = w}) := (hρ w).preimage hc
  filter_upwards [hU.mem_nhds (by simp)] with y hy
  have hy' : ρ ((x : G)⁻¹ * (y : G)) w = w := hy
  calc ρ (y : G) w = ρ (x : G) (ρ ((x : G)⁻¹ * (y : G)) w) := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    _ = ρ (x : G) w := by rw [hy']

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unitSemisimple_hyp {N : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]
    {π : Representation ℂ (GL (Fin N) k) X} (hπ : IsAdmissible π) (v : X) :
    ∃ K : Subgroup (GL (Fin N) k), (∀ g ∈ K, π g v = v) ∧ FiniteDimensional ℂ (fixed π K) ∧
      ∀ w, (Set.range fun g : K => π g w).Finite := by
  have hU : {g : GL (Fin N) k | π g v = v} ∈ nhds (1 : GL (Fin N) k) :=
    (hπ.1 v).mem_nhds (by simp)
  obtain ⟨K, hKo, hKc, hKU⟩ := GlobalTheory.CompanionTheory.SmGL.exists_compact_open_subgroup_subset k N _ hU
  exact ⟨K, fun g hg => hKU hg, hπ.2 K hKo hKc, finite_orbit_of_isSmooth hπ.1 K hKc⟩

theorem unitaryAdmissibleComplement_at (N : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    (π : Representation ℂ (GL (Fin N) k) X) (hπ : IsAdmissible π) (hu : IsUnitarisable π)
    (S : Subrepresentation π) : ∃ T : Subrepresentation π, IsCompl S.toSubmodule T.toSubmodule := by
  obtain ⟨B, hs, hp, hi⟩ := hu
  have hdef : ∀ v, B.flip v v = 0 → v = 0 := fun v h => by
    by_contra hv
    have := hp v hv
    rw [LinearMap.flip_apply] at h
    rw [h, Complex.zero_re] at this
    exact lt_irrefl _ this
  have hinv : ∀ g u v, B.flip (π g u) (π g v) = B.flip u v := fun g u v => by
    simp only [LinearMap.flip_apply, hi]
  let T : Subrepresentation π :=
    { toSubmodule :=
        { carrier := {w | ∀ z ∈ S.toSubmodule, B.flip z w = 0}
          add_mem' := fun {a b} ha hb z hz => by rw [map_add (f := _), ha z hz, hb z hz, add_zero]
          zero_mem' := fun z _ => by rw [map_zero]
          smul_mem' := fun c w hw z hz => by rw [map_smul, hw z hz, smul_zero] }
      apply_mem_toSubmodule := fun g w hw =>
        GlobalTheory.UnitarySemisimple.orth_stable π B.flip hinv S w hw g }
  refine ⟨T, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hxS hxT
    exact hdef x (hxT x hxS)
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    obtain ⟨t, htS, ht⟩ := GlobalTheory.UnitarySemisimple.exists_compl_proj π B.flip hdef hinv
      (unitSemisimple_hyp hπ) S v
    have hvT : v - t ∈ T.toSubmodule := ht
    have := Submodule.add_mem_sup htS hvT
    rwa [add_sub_cancel] at this

end PositivityTheory.PfBern.Props2
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.UnitaryAdmissibleComplements.IsIrreducibleIffFinrank
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir

namespace PositivityTheory.PfBern.Props2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Zero

variable {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X]

end Zero

section GL0

variable {G X : Type} [Group G] [Subsingleton G] [AddCommGroup X] [Module ℂ X]

def subrepIso (ρ : Representation ℂ G X) : Subrepresentation ρ ≃o Submodule ℂ X where
  toFun S := S.toSubmodule
  invFun U := ⟨U, fun g v hv => by rw [Subsingleton.elim g 1, map_one]; exact hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_iff_finrank (ρ : Representation ℂ G X) :
    ρ.IsIrreducible ↔ Module.finrank ℂ X = 1 := by
  unfold Representation.IsIrreducible
  exact (PositivityTheory.PfBern.Props2.subrepIso ρ).isSimpleOrder_iff.trans
    ((isSimpleModule_iff ℂ X).symm.trans isSimpleModule_iff_finrank_eq_one)

theorem finrank_smoothPart_ind [TopologicalSpace G] [IsTopologicalGroup G] {Z : Type} [AddCommGroup Z]
    [Module ℂ Z] (H : Subgroup G) (σ : Representation ℂ H Z) :
    Module.finrank ℂ (smoothPart (ind H σ)) = Module.finrank ℂ Z := by
  haveI : DiscreteTopology G := Subsingleton.discreteTopology
  have hmem : ∀ z : Z, (fun _ : G => z) ∈ GlobalTheory.PRep.indSpace H σ := by
    intro z
    simp [GlobalTheory.PRep.indSpace, Subsingleton.elim _ (1 : H)]
  have hsmooth : ∀ v : GlobalTheory.PRep.indSpace H σ,
      v ∈ GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind H σ) := by
    intro v
    exact isOpen_discrete _
  let e : GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind H σ) →ₗ[ℂ] Z :=
    (LinearMap.proj (R := ℂ) (φ := fun _ : G => Z) 1).comp
      ((GlobalTheory.PRep.indSpace H σ).subtype.comp
        (GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind H σ)).subtype)
  have he_inj : Function.Injective e := by
    intro v w hvw
    apply Subtype.ext
    apply Subtype.ext
    funext g
    rw [Subsingleton.elim g 1]
    exact hvw
  have he_surj : Function.Surjective e := fun z => ⟨⟨⟨fun _ => z, hmem z⟩, hsmooth _⟩, rfl⟩
  exact (LinearEquiv.ofBijective e ⟨he_inj, he_surj⟩).finrank_eq

end GL0

instance subsingleton_GL0 : Subsingleton (GL (Fin 0) k) := inferInstance

theorem prodGL0Irreducible_at (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin 0) k) V) (π₂ : Representation ℂ (GL (Fin 0) k) W) :
    π₁.IsIrreducible → π₂.IsIrreducible → (prod₂ π₁ π₂).IsIrreducible := by
  intro h₁ h₂
  haveI : Subsingleton (GL (Fin (0 + 0)) k) := PositivityTheory.PfBern.Props2.subsingleton_GL0
  rw [PositivityTheory.PfBern.Props2.isIrreducible_iff_finrank] at h₁ h₂ ⊢
  erw [PositivityTheory.PfBern.Props2.finrank_smoothPart_ind]
  rw [Module.finrank_tensorProduct (R := ℂ) (S := ℂ), h₁, h₂]

end PositivityTheory.PfBern.Props2
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.UnitarisableHypotheses.IsUnitarisableCast
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Prod.Asm

section Tw

variable {G M V W Z : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Z] [Module ℂ Z]

def twHom {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) (f : ρ.IntertwiningMap σ) :
    (twAct ρ N θ s hs).IntertwiningMap (twAct σ N θ s hs) where
  toLinearMap := twMap ρ σ N θ f.toLinearMap (fun g v => LinearMap.congr_fun (f.isIntertwining' g) v)
  isIntertwining' m := by
    apply Submodule.linearMap_qext
    ext v
    exact congrArg Submodule.Quotient.mk (LinearMap.congr_fun (f.isIntertwining' (s m)) v)

theorem twHom_comp {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G Z} (N : Subgroup G)
    (θ : N →* ℂˣ) (s : M →* G) (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n)
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ) (f' : ρ.IntertwiningMap τ) (h : ∀ v, f' v = g (f v))
    (x : TwJacquet ρ N θ) : twHom N θ s hs f' x = twHom N θ s hs g (twHom N θ s hs f x) := by
  induction x using Submodule.Quotient.induction_on with
  | H v => exact congrArg Submodule.Quotient.mk (h v)

theorem twHom_id {ρ : Representation ℂ G V} (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n)
    (f : ρ.IntertwiningMap ρ) (h : ∀ v, f v = v) (x : TwJacquet ρ N θ) : twHom N θ s hs f x = x := by
  induction x using Submodule.Quotient.induction_on with
  | H v => exact congrArg Submodule.Quotient.mk (h v)

theorem twHom_zero {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n)
    (f : ρ.IntertwiningMap σ) (h : ∀ v, f v = 0) (x : TwJacquet ρ N θ) : twHom N θ s hs f x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H v => exact (congrArg Submodule.Quotient.mk (h v)).trans (Submodule.Quotient.mk_zero _)

end Tw

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def phiHom (ψ : AddChar k Circle) {n : ℕ} {τ τ' : MRep k (n + 1)} (f : τ.ρ.IntertwiningMap τ'.ρ) :
    (MRep.phiM k ψ τ).ρ.IntertwiningMap (MRep.phiM k ψ τ').ρ :=
  twHom (MirUin k (n + 1)) (mirChar k ψ n) ((levi k (n + 1)).comp (Mir k n).subtype) (levi_stab ψ n) f

def iterHom (ψ : AddChar k Circle) : (j : ℕ) → {n : ℕ} → {τ τ' : MRep k (n + j)} → τ.ρ.IntertwiningMap τ'.ρ →
    (iterPhi k ψ j τ).ρ.IntertwiningMap (iterPhi k ψ j τ').ρ
  | 0, _, _, _, f => f
  | j + 1, _, _, _, f => iterHom ψ j (phiHom ψ f)

theorem iterHom_comp (ψ : AddChar k Circle) : ∀ (j : ℕ) {n : ℕ} {τ τ' τ'' : MRep k (n + j)}
    (f : τ.ρ.IntertwiningMap τ'.ρ) (g : τ'.ρ.IntertwiningMap τ''.ρ) (f' : τ.ρ.IntertwiningMap τ''.ρ),
    (∀ v, f' v = g (f v)) → ∀ x, iterHom ψ j f' x = iterHom ψ j g (iterHom ψ j f x)
  | 0, _, _, _, _, _, _, _, h, x => h x
  | j + 1, _, _, _, _, f, g, f', h, x =>
    iterHom_comp ψ j (phiHom ψ f) (phiHom ψ g) (phiHom ψ f') (twHom_comp _ _ _ _ f g f' h) x

theorem iterHom_id (ψ : AddChar k Circle) : ∀ (j : ℕ) {n : ℕ} {τ : MRep k (n + j)}
    (f : τ.ρ.IntertwiningMap τ.ρ), (∀ v, f v = v) → ∀ x, iterHom ψ j f x = x
  | 0, _, _, _, h, x => h x
  | j + 1, _, _, f, h, x => iterHom_id ψ j (phiHom ψ f) (twHom_id _ _ _ _ f h) x

theorem iterHom_zero (ψ : AddChar k Circle) : ∀ (j : ℕ) {n : ℕ} {τ τ' : MRep k (n + j)}
    (f : τ.ρ.IntertwiningMap τ'.ρ), (∀ v, f v = 0) → ∀ x, iterHom ψ j f x = 0
  | 0, _, _, _, _, h, x => h x
  | j + 1, _, _, _, f, h, x => iterHom_zero ψ j (phiHom ψ f) (twHom_zero _ _ _ _ f h) x

def resHom {m : ℕ} {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {π : Representation ℂ (GL (Fin (m + 1)) k) X} {σ : Representation ℂ (GL (Fin (m + 1)) k) Y}
    (f : π.IntertwiningMap σ) : (resM k π).ρ.IntertwiningMap (resM k σ).ρ where
  toLinearMap := f.toLinearMap
  isIntertwining' g := f.isIntertwining' g

def dHom (ψ : AddChar k Circle) : (j : ℕ) → {n : ℕ} → {A B : GRep k (n + j)} → A.ρ.IntertwiningMap B.ρ →
    (derivB ψ j A).ρ.IntertwiningMap (derivB ψ j B).ρ
  | 0, _, _, _, f => f
  | j + 1, n, _, _, f => twHom (MirUin k n) 1 (levi k n) (levi_normalises n) (iterHom ψ j (resHom f))

theorem dHom_comp (ψ : AddChar k Circle) : ∀ (j : ℕ) {n : ℕ} {A B C : GRep k (n + j)}
    (f : A.ρ.IntertwiningMap B.ρ) (g : B.ρ.IntertwiningMap C.ρ) (f' : A.ρ.IntertwiningMap C.ρ),
    (∀ v, f' v = g (f v)) → ∀ x, dHom ψ j f' x = dHom ψ j g (dHom ψ j f x)
  | 0, _, _, _, _, _, _, _, h, x => h x
  | j + 1, _, _, _, _, f, g, f', h, x =>
    twHom_comp _ _ _ _ _ _ _ (iterHom_comp ψ j (resHom f) (resHom g) (resHom f') h) x

theorem dHom_id (ψ : AddChar k Circle) : ∀ (j : ℕ) {n : ℕ} {A : GRep k (n + j)}
    (f : A.ρ.IntertwiningMap A.ρ), (∀ v, f v = v) → ∀ x, dHom ψ j f x = x
  | 0, _, _, _, h, x => h x
  | j + 1, _, _, f, h, x => twHom_id _ _ _ _ _ (iterHom_id ψ j (resHom f) h) x

theorem dHom_zero (ψ : AddChar k Circle) : ∀ (j : ℕ) {n : ℕ} {A B : GRep k (n + j)}
    (f : A.ρ.IntertwiningMap B.ρ), (∀ v, f v = 0) → ∀ x, dHom ψ j f x = 0
  | 0, _, _, _, _, h, x => h x
  | j + 1, _, _, _, f, h, x => twHom_zero _ _ _ _ _ (iterHom_zero ψ j (resHom f) h) x

section Cast

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem cast_cast {a b c : ℕ} (e1 : a = b) (e2 : b = c) (X : GRep k a) :
    (X.cast e1).cast e2 = X.cast (e1.trans e2) := by
  subst e1; subst e2; rfl

def castHom {a b : ℕ} (e : a = b) {X Y : GRep k a} (f : X.ρ.IntertwiningMap Y.ρ) :
    (X.cast e).ρ.IntertwiningMap (Y.cast e).ρ := by
  subst e; exact f

theorem castHom_comp {a b : ℕ} (e : a = b) {X Y Z : GRep k a} (f : X.ρ.IntertwiningMap Y.ρ)
    (g : Y.ρ.IntertwiningMap Z.ρ) (f' : X.ρ.IntertwiningMap Z.ρ) (h : ∀ v, f' v = g (f v)) :
    ∀ v, castHom e f' v = castHom e g (castHom e f v) := by
  subst e; exact h

theorem castHom_id {a b : ℕ} (e : a = b) {X : GRep k a} (f : X.ρ.IntertwiningMap X.ρ) (h : ∀ v, f v = v) :
    ∀ v, castHom e f v = v := by
  subst e; exact h

theorem castHom_zero {a b : ℕ} (e : a = b) {X Y : GRep k a} (f : X.ρ.IntertwiningMap Y.ρ) (h : ∀ v, f v = 0) :
    ∀ v, castHom e f v = 0 := by
  subst e; exact h

theorem isSmooth_cast {a b : ℕ} (e : a = b) (X : GRep k a) : IsSmooth (X.cast e).ρ ↔ IsSmooth X.ρ := by
  subst e; rfl

theorem isIrreducible_cast {a b : ℕ} (e : a = b) (X : GRep k a) :
    (X.cast e).ρ.IsIrreducible ↔ X.ρ.IsIrreducible := by
  subst e; rfl

theorem isUnitarisable_cast {a b : ℕ} (e : a = b) (X : GRep k a) :
    IsUnitarisable (X.cast e).ρ ↔ IsUnitarisable X.ρ := by
  subst e; rfl

def DM (ψ : AddChar k Circle) (j : ℕ) {N n : ℕ} (e : N = n + j) {X Y : GRep k N} (f : X.ρ.IntertwiningMap Y.ρ) :
    (derivB ψ j (X.cast e)).ρ.IntertwiningMap (derivB ψ j (Y.cast e)).ρ :=
  dHom ψ j (castHom e f)

theorem DM_comp (ψ : AddChar k Circle) (j : ℕ) {N n : ℕ} (e : N = n + j) {X Y Z : GRep k N}
    (f : X.ρ.IntertwiningMap Y.ρ) (g : Y.ρ.IntertwiningMap Z.ρ) (f' : X.ρ.IntertwiningMap Z.ρ)
    (h : ∀ v, f' v = g (f v)) (x : (derivB ψ j (X.cast e)).V) : DM ψ j e f' x = DM ψ j e g (DM ψ j e f x) :=
  dHom_comp ψ j _ _ _ (castHom_comp e f g f' h) x

theorem DM_id (ψ : AddChar k Circle) (j : ℕ) {N n : ℕ} (e : N = n + j) {X : GRep k N}
    (f : X.ρ.IntertwiningMap X.ρ) (h : ∀ v, f v = v) (x : (derivB ψ j (X.cast e)).V) : DM ψ j e f x = x :=
  dHom_id ψ j _ (castHom_id e f h) x

theorem DM_zero (ψ : AddChar k Circle) (j : ℕ) {N n : ℕ} (e : N = n + j) {X Y : GRep k N}
    (f : X.ρ.IntertwiningMap Y.ρ) (h : ∀ v, f v = 0) (x : (derivB ψ j (X.cast e)).V) : DM ψ j e f x = 0 :=
  dHom_zero ψ j _ (castHom_zero e f h) x

theorem DM_comm (ψ : AddChar k Circle) (j : ℕ) {N n : ℕ} (e : N = n + j) {X Y : GRep k N}
    (f : X.ρ.IntertwiningMap Y.ρ) (g : GL (Fin n) k) (x : (derivB ψ j (X.cast e)).V) :
    DM ψ j e f ((derivB ψ j (X.cast e)).ρ g x) = (derivB ψ j (Y.cast e)).ρ g (DM ψ j e f x) :=
  LinearMap.congr_fun ((DM ψ j e f).isIntertwining' g) x

def ND (ψ : AddChar k Circle) {N : ℕ} (X : GRep k N) (j : ℕ) : Prop :=
  ∃ (n : ℕ) (e : N = n + j), Nontrivial (derivB ψ j (X.cast e)).V

theorem nd_iff (ψ : AddChar k Circle) {N : ℕ} (X : GRep k N) {n j : ℕ} (e : N = n + j) :
    ND ψ X j ↔ Nontrivial (derivB ψ j (X.cast e)).V := by
  constructor
  · rintro ⟨n', e', h⟩
    obtain rfl : n' = n := by omega
    exact h
  · exact fun h => ⟨n, e, h⟩

theorem le_of_nd (ψ : AddChar k Circle) {N : ℕ} (X : GRep k N) {j : ℕ} (h : ND ψ X j) : j ≤ N := by
  obtain ⟨n, e, _⟩ := h
  omega

theorem isTopD_iff (ψ : AddChar k Circle) {N n h : ℕ} (X : GRep k N) (e : N = n + h) :
    Prod.IsTopD ψ (X.cast e) ↔ ND ψ X h ∧ ∀ h', h < h' → ¬ ND ψ X h' := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(nd_iff ψ X e).2 h1, fun h' hlt hnd => ?_⟩
    obtain ⟨n', e', hnt⟩ := hnd
    have hs := h2 n' h' (e.symm.trans e') hlt
    rw [cast_cast] at hs
    exact not_subsingleton _ hs
  · rintro ⟨h1, h2⟩
    refine ⟨(nd_iff ψ X e).1 h1, fun n' h' e' hlt => ?_⟩
    rw [cast_cast]
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact h2 h' hlt ⟨n', _, hns⟩

def subG {N : ℕ} {X : GRep k N} (S : Subrepresentation X.ρ) : GRep k N := ⟨S.toSubmodule, S.toRepresentation⟩

end Cast

end PositivityTheory.RgUd.Prod.Asm
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.UnitarisableHypotheses.IrrSub
noncomputable section

open Classical

namespace PositivityTheory.RgUd.Prod.Asm

open GlobalTheory.PRep

section Gen

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

theorem mem_fixed_iff (K : Subgroup G) (v : V) : v ∈ fixed ρ K ↔ ∀ k : K, ρ (k : G) v = v := by
  show (∀ h : K, ρ (h : G) v = ((1 : K →* ℂˣ) h : ℂ) • v) ↔ _
  simp

def genSub (M : Submodule ℂ V) : Subrepresentation ρ where
  toSubmodule := Submodule.span ℂ {w | ∃ g : G, ∃ x ∈ M, w = ρ g x}
  apply_mem_toSubmodule := by
    intro g v hv
    have : Submodule.span ℂ {w | ∃ g : G, ∃ x ∈ M, w = ρ g x} ≤
        (Submodule.span ℂ {w | ∃ g : G, ∃ x ∈ M, w = ρ g x}).comap (ρ g) := by
      refine Submodule.span_le.2 ?_
      intro w hw
      obtain ⟨h, x, hx, rfl⟩ := hw
      rw [SetLike.mem_coe, Submodule.mem_comap]
      refine Submodule.subset_span ⟨g * h, x, hx, ?_⟩
      simp [map_mul]
    exact this hv

theorem le_genSub (M : Submodule ℂ V) : M ≤ (genSub ρ M).toSubmodule := by
  intro x hx
  exact Submodule.subset_span ⟨1, x, hx, by simp⟩

theorem genSub_le (M : Submodule ℂ V) (U : Subrepresentation ρ) (h : M ≤ U.toSubmodule) :
    (genSub ρ M).toSubmodule ≤ U.toSubmodule := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨g, x, hx, rfl⟩
  exact U.apply_mem_toSubmodule g (h hx)

theorem fixed_split (U C : Subrepresentation ρ) (hUC : U.toSubmodule ⊓ C.toSubmodule = ⊥) (g : G)
    {u c : V} (hu : u ∈ U.toSubmodule) (hc : c ∈ C.toSubmodule) (h : ρ g (u + c) = u + c) :
    ρ g u = u := by
  have h1 : ρ g u - u = c - ρ g c := by
    rw [map_add (f := _)] at h
    rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
  have h2 : ρ g u - u ∈ U.toSubmodule ⊓ C.toSubmodule := by
    refine ⟨sub_mem (U.apply_mem_toSubmodule g hu) hu, ?_⟩
    rw [h1]
    exact sub_mem hc (C.apply_mem_toSubmodule g hc)
  rw [hUC] at h2
  exact sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 h2)

theorem irreducible_of_fixed (K : Subgroup G)
    (hcompl : ∀ S : Subrepresentation ρ, ∃ T : Subrepresentation ρ, IsCompl S.toSubmodule T.toSubmodule)
    (W : Subrepresentation ρ) (h1 : fixed ρ K ⊓ W.toSubmodule ≠ ⊥)
    (h2 : ∀ U : Subrepresentation ρ, U.toSubmodule ≤ W.toSubmodule → fixed ρ K ⊓ U.toSubmodule ≠ ⊥ →
      fixed ρ K ⊓ W.toSubmodule ≤ U.toSubmodule)
    (h3 : ∀ U : Subrepresentation ρ, fixed ρ K ⊓ W.toSubmodule ≤ U.toSubmodule →
      W.toSubmodule ≤ U.toSubmodule) :
    W.toRepresentation.IsIrreducible := by
  obtain ⟨w, hwF, hwW, hw0⟩ : ∃ w, w ∈ fixed ρ K ∧ w ∈ W.toSubmodule ∧ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply h1
    rw [Submodule.eq_bot_iff]
    intro x hx
    exact hcon x hx.1 hx.2
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    have h1' : (⟨w, hwW⟩ : W.toSubmodule) ∈ (⊤ : Subrepresentation W.toRepresentation).toSubmodule :=
      Submodule.mem_top
    rw [← h] at h1'
    have h2' : (⟨w, hwW⟩ : W.toSubmodule) = 0 := (Submodule.mem_bot ℂ).1 h1'
    exact hw0 (congrArg Subtype.val h2')
  · intro U
    let U' : Subrepresentation ρ :=
      { toSubmodule := U.toSubmodule.map W.toSubmodule.subtype
        apply_mem_toSubmodule := by
          intro g v hv
          obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hv
          exact Submodule.mem_map.2 ⟨W.toRepresentation g u, U.apply_mem_toSubmodule g hu, rfl⟩ }
    have hU'le : U'.toSubmodule ≤ W.toSubmodule := by
      intro v hv
      obtain ⟨u, _, rfl⟩ := Submodule.mem_map.1 hv
      exact u.2
    by_cases hF : fixed ρ K ⊓ U'.toSubmodule = ⊥
    · left
      obtain ⟨C, hC⟩ := hcompl U'
      have hFC : fixed ρ K ⊓ W.toSubmodule ≤ C.toSubmodule := by
        rintro x ⟨hxF, hxW⟩
        have hx : x ∈ U'.toSubmodule ⊔ C.toSubmodule := by
          rw [hC.sup_eq_top]
          exact Submodule.mem_top
        obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 hx
        have huF : u ∈ fixed ρ K := (mem_fixed_iff ρ K u).2 fun k =>
          fixed_split ρ U' C hC.inf_eq_bot k hu hc ((mem_fixed_iff ρ K _).1 hxF k)
        have hu0 : u ∈ fixed ρ K ⊓ U'.toSubmodule := ⟨huF, hu⟩
        rw [hF] at hu0
        rw [(Submodule.mem_bot ℂ).1 hu0, zero_add]
        exact hc
      have hWC := h3 C hFC
      apply Subrepresentation.ext
      show U.toSubmodule = (⊥ : Submodule ℂ W.toSubmodule)
      rw [Submodule.eq_bot_iff]
      intro u hu
      have hm : (u : V) ∈ U'.toSubmodule ⊓ C.toSubmodule :=
        ⟨Submodule.mem_map_of_mem hu, hWC u.2⟩
      rw [hC.inf_eq_bot] at hm
      exact Subtype.ext ((Submodule.mem_bot ℂ).1 hm)
    · right
      have hWU := h3 U' (h2 U' hU'le hF)
      apply Subrepresentation.ext
      show U.toSubmodule = (⊤ : Submodule ℂ W.toSubmodule)
      rw [eq_top_iff]
      intro x _
      obtain ⟨u, hu, hux⟩ := Submodule.mem_map.1 (hWU x.2)
      have : u = x := Subtype.ext hux
      rw [← this]
      exact hu

end Gen

theorem exists_irreducible_le {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V)
    (hsmall : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (hA : GlobalTheory.PRep.IsAdmissible ρ)
    (hcompl : ∀ S : Subrepresentation ρ, ∃ T : Subrepresentation ρ, IsCompl S.toSubmodule T.toSubmodule)
    (S : Subrepresentation ρ) (hS : S ≠ ⊥) :
    ∃ S₀ : Subrepresentation ρ, S₀ ≠ ⊥ ∧ S₀.toSubmodule ≤ S.toSubmodule ∧ S₀.toRepresentation.IsIrreducible := by
  obtain ⟨v, hvS, hv0⟩ : ∃ v ∈ S.toSubmodule, v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hS
    apply Subrepresentation.ext
    show S.toSubmodule = (⊥ : Submodule ℂ V)
    rw [Submodule.eq_bot_iff]
    exact hcon
  obtain ⟨K, hKo, hKc, hKv⟩ := hsmall {g | ρ g v = v} ((hA.1 v).mem_nhds (by simp))
  have hFd : FiniteDimensional ℂ (fixed ρ K) := hA.2 K hKo hKc
  have hvF : v ∈ fixed ρ K := (mem_fixed_iff ρ K v).2 fun k => hKv k.2
  have hex : ∃ n, ∃ W : Subrepresentation ρ, W.toSubmodule ≤ S.toSubmodule ∧
      fixed ρ K ⊓ W.toSubmodule ≠ ⊥ ∧ Module.finrank ℂ (fixed ρ K ⊓ W.toSubmodule : Submodule ℂ V) = n := by
    refine ⟨_, S, le_rfl, ?_, rfl⟩
    intro h
    have : v ∈ fixed ρ K ⊓ S.toSubmodule := ⟨hvF, hvS⟩
    rw [h] at this
    exact hv0 ((Submodule.mem_bot ℂ).1 this)
  obtain ⟨W, hWS, hW0, hWn⟩ := Nat.find_spec hex
  set W₀ := genSub ρ (fixed ρ K ⊓ W.toSubmodule) with hW₀def
  have hW₀W : W₀.toSubmodule ≤ W.toSubmodule := genSub_le ρ _ W inf_le_right
  have hF₀ : fixed ρ K ⊓ W₀.toSubmodule = fixed ρ K ⊓ W.toSubmodule :=
    le_antisymm (inf_le_inf_left _ hW₀W) (le_inf inf_le_left (le_genSub ρ _))
  refine ⟨W₀, ?_, hW₀W.trans hWS, ?_⟩
  · intro h
    apply hW0
    rw [← hF₀, h]
    exact inf_bot_eq _
  · refine irreducible_of_fixed ρ K hcompl W₀ (by rwa [hF₀]) ?_ ?_
    · intro U hU hUne
      have hmin := Nat.find_min' hex ⟨U, hU.trans (hW₀W.trans hWS), hUne, rfl⟩
      rw [← hWn] at hmin
      have : FiniteDimensional ℂ (fixed ρ K ⊓ W.toSubmodule : Submodule ℂ V) :=
        Submodule.finiteDimensional_of_le inf_le_left
      have hle : fixed ρ K ⊓ U.toSubmodule ≤ fixed ρ K ⊓ W.toSubmodule := hF₀ ▸ inf_le_inf_left _ hU
      have heq := Submodule.eq_of_le_of_finrank_le hle hmin
      rw [hF₀, ← heq]
      exact inf_le_right
    · intro U hU
      rw [hF₀] at hU
      exact genSub_le ρ _ U hU

end PositivityTheory.RgUd.Prod.Asm
end
end

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Prod.Asm

open PositivityTheory.PfBern.Assembly (subIncl subProj subProj_subIncl_left subProj_subIncl_right isSmooth_sub
  eq_bot_or_eq_top_of_equiv_twist range_ne_bot_ne_top)

section Gen

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isUnitarisable_sub {ρ : Representation ℂ G V} (h : IsUnitarisable ρ) (S : Subrepresentation ρ) :
    IsUnitarisable S.toRepresentation := by
  obtain ⟨B, h1, h2, h3⟩ := h
  exact ⟨(B.comp S.toSubmodule.subtype).compl₂ S.toSubmodule.subtype, fun v w => h1 _ _,
    fun v hv => h2 _ (fun h0 => hv (Subtype.ext h0)), fun g v w => h3 g v w⟩

theorem isUnitarisable_of_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (E : ρ.Equiv σ)
    (h : IsUnitarisable σ) : IsUnitarisable ρ := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨(B.comp E.toLinearMap).compl₂ E.toLinearMap, fun v w => h1 _ _,
    fun v hv => h2 _ (fun h0 => hv (E.toLinearEquiv.map_eq_zero_iff.1 h0)), fun g v w => ?_⟩
  have hc : ∀ u, E.toLinearMap (ρ g u) = σ g (E.toLinearMap u) := fun u =>
    LinearMap.congr_fun (E.isIntertwining' g) u
  simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, hc]
  exact h3 g _ _

theorem norm_eq_one_of_unitarisable {ρ : Representation ℂ G V} (h : IsUnitarisable ρ) (g : G) {v : V} {c : ℂ}
    (hv : v ≠ 0) (hc : ρ g v = c • v) : ‖c‖ = 1 := by
  obtain ⟨B, -, h2, h3⟩ := h
  have e := h3 g v v
  rw [hc, LinearMap.map_smulₛₗ (B (c • v)), map_smul B c v, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at e
  have hB : B v v ≠ 0 := fun h0 => by
    have := h2 v hv
    rw [h0] at this
    simp at this
  have hcc : c * (starRingEnd ℂ) c = 1 := by
    have e' : (c * (starRingEnd ℂ) c) * B v v = 1 * B v v := by
      rw [one_mul]
      exact (by ring : (c * (starRingEnd ℂ) c) * B v v = (starRingEnd ℂ) c * (c * B v v)).trans e
    exact mul_right_cancel₀ hB e'
  rw [Complex.mul_conj] at hcc
  have hn : ‖c‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact_mod_cast hcc
  have h0 := norm_nonneg c
  have h4 : (‖c‖ - 1) * (‖c‖ + 1) = 0 := by ring_nf; linarith
  rcases mul_eq_zero.1 h4 with h5 | h5 <;> linarith

end Gen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Maps

def idH {N : ℕ} (X : GRep k N) : X.ρ.IntertwiningMap X.ρ where
  toLinearMap := LinearMap.id
  isIntertwining' _ := rfl

def zeroH {N : ℕ} (X Y : GRep k N) : X.ρ.IntertwiningMap Y.ρ where
  toLinearMap := 0
  isIntertwining' _ := by ext; simp

def inclLe {N : ℕ} {X : GRep k N} {S T : Subrepresentation X.ρ} (h : S.toSubmodule ≤ T.toSubmodule) :
    (subG S).ρ.IntertwiningMap (subG T).ρ where
  toLinearMap := Submodule.inclusion h
  isIntertwining' _ := by ext; rfl

theorem DM_proj_incl (ψ : AddChar k Circle) (j : ℕ) {N n : ℕ} (e : N = n + j) {X : GRep k N}
    (S T : Subrepresentation X.ρ) (hc : IsCompl T.toSubmodule S.toSubmodule) (a : (derivB ψ j ((subG S).cast e)).V) :
    DM ψ j e (X := X) (Y := subG S) (subProj T S hc) (DM ψ j e (X := subG S) (Y := X) (subIncl S) a) = a :=
  (DM_comp ψ j e (subIncl S) (subProj T S hc) (idH _) (fun v => (subProj_subIncl_right T S hc v).symm) a).symm.trans
    (DM_id ψ j e (idH _) (fun _ => rfl) a)

theorem DM_subIncl_injective (ψ : AddChar k Circle) (j : ℕ) {N n : ℕ} (e : N = n + j) {X : GRep k N}
    (S T : Subrepresentation X.ρ) (hc : IsCompl T.toSubmodule S.toSubmodule) :
    Function.Injective (DM ψ j e (X := subG S) (Y := X) (subIncl S)) := fun a b hab => by
  rw [← DM_proj_incl ψ j e S T hc a, ← DM_proj_incl ψ j e S T hc b, hab]

theorem nontrivial_of_nd (ψ : AddChar k Circle) {N j : ℕ} (X : GRep k N) (h : ND ψ X j) : Nontrivial X.V := by
  obtain ⟨n, e, hnt⟩ := h
  by_contra hX
  rw [not_nontrivial_iff_subsingleton] at hX
  obtain ⟨y, hy⟩ := exists_ne (0 : (derivB ψ j (X.cast e)).V)
  apply hy
  rw [← DM_id ψ j e (idH X) (fun _ => rfl) y]
  exact DM_zero ψ j e (idH X) (fun v => Subsingleton.elim _ _) y

theorem nd_mono (ψ : AddChar k Circle) {N h : ℕ} {X : GRep k N} (S₀ S T₀ : Subrepresentation X.ρ)
    (hle : S₀.toSubmodule ≤ S.toSubmodule) (hc : IsCompl T₀.toSubmodule S₀.toSubmodule) (hnd : ND ψ (subG S₀) h) :
    ND ψ (subG S) h := by
  obtain ⟨n, e, hnt⟩ := hnd
  refine ⟨n, e, ?_⟩
  by_contra hS
  rw [not_nontrivial_iff_subsingleton] at hS
  obtain ⟨a, ha⟩ := exists_ne (0 : (derivB ψ h ((subG S₀).cast e)).V)
  apply ha
  apply DM_subIncl_injective ψ h e S₀ T₀ hc
  rw [DM_comp ψ h e (inclLe hle) (subIncl S) (subIncl S₀) (fun v => rfl) a,
    Subsingleton.elim (DM ψ h e (inclLe hle) a) 0, map_zero, map_zero]

end Maps

section Steps

theorem exists_top (ψ : AddChar k Circle) {N : ℕ} (X : GRep k N) {j₀ : ℕ} (h₀ : ND ψ X j₀) :
    ∃ j, j₀ ≤ j ∧ ND ψ X j ∧ ∀ j', j < j' → ¬ ND ψ X j' := by
  classical
  refine ⟨Nat.findGreatest (ND ψ X) N, Nat.le_findGreatest (le_of_nd ψ X h₀) h₀,
    Nat.findGreatest_spec (le_of_nd ψ X h₀) h₀, fun j' hlt hj' => ?_⟩
  exact Nat.findGreatest_is_greatest hlt (le_of_nd ψ X hj') hj'

theorem exists_nd_pos (ψ : AddChar k Circle) (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) {N : ℕ} (X : GRep k N)
    (hN : 0 < N) (hs : IsSmooth X.ρ) (hX : Nontrivial X.V) : ∃ j, 1 ≤ j ∧ ND ψ X j := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  obtain ⟨n, hn, hnt⟩ := GlobalTheory.T.exists_nontrivial_derivative k ψ hψc hψ1 m (resM k X.ρ).V (resM k X.ρ).ρ
    (fun v => (hs v).preimage continuous_subtype_val) hX
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨E⟩ := GlobalTheory.T.twisted_jacquet_iterated_phi_equiv k ψ n j (resM k X.ρ)
  exact ⟨j + 1, by omega, n, rfl, E.symm.injective.nontrivial⟩

theorem norm_dpow_sc (n : ℕ) (s : ℝ) (x : kˣ) :
    ‖((dpow n s (Prod.sc n x) : ℂˣ) : ℂ)‖ = nabs k x ^ ((n : ℝ) * s) := by
  have hdet : GeneralLinearGroup.det (Prod.sc n x) = x ^ n := by
    ext; simp [Prod.sc]
  simp only [dpow, detChar_apply, hdet]
  rw [val_absPow_ofReal, Complex.norm_of_nonneg (Real.rpow_nonneg (nabs_pos' k _).le _)]
  rw [show nabs k (x ^ n) = nabs k x ^ n by simp [nabs, map_pow]]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (nabs_pos' k x).le]

theorem exists_eig_top (ψ : AddChar k Circle) (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) (hT : DerivTop k) {n j : ℕ}
    (π : GRep k (n + j)) (hj : 1 ≤ j) (hs : IsSmooth π.ρ) (hi : π.ρ.IsIrreducible) (hu : IsUnitarisable π.ρ)
    (htop : Prod.IsTopD ψ π) (x : kˣ) :
    ∃ (v : (derivB ψ j π).V) (c : ℂ), v ≠ 0 ∧ (derivB ψ j π).ρ (Prod.sc n x) v = c • v ∧
      ‖c‖ = nabs k x ^ ((n : ℝ) * ((j : ℝ) - 1) / 2) := by
  obtain ⟨hirr, hunit⟩ := hT ψ hψc hψ1 n j π hj hs hi hu htop.1 htop.2
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hDs : IsSmooth (derivB ψ (j' + 1) π).ρ := GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_deriv ψ j' hs
  have hTs : IsSmooth ((derivB ψ (j' + 1) π).tw ((1 - ((j' + 1 : ℕ) : ℝ)) / 2)).ρ :=
    isSmooth_twist hDs (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar
  have := hirr
  obtain ⟨c', hc'⟩ := GroundTheory.Automorphic.exists_central_character
    ((PositivityTheory.PfBern.Props1.isSmooth_found_iff _).2 hTs) (z := Prod.sc n x)
    (Submonoid.mem_center_iff.2 fun g => (GlobalTheory.CuspRep.scalar_comm x g).symm)
  have : Nontrivial (derivB ψ (j' + 1) π).V := htop.1
  obtain ⟨v, hv⟩ := exists_ne (0 : (derivB ψ (j' + 1) π).V)
  have h1 := norm_eq_one_of_unitarisable hunit (Prod.sc n x) hv (hc' v)
  set d : ℂ := ((dpow n ((1 - ((j' + 1 : ℕ) : ℝ)) / 2) (Prod.sc n x) : ℂˣ) : ℂ) with hd
  have htw : ((derivB ψ (j' + 1) π).tw ((1 - ((j' + 1 : ℕ) : ℝ)) / 2)).ρ (Prod.sc n x) v =
      d • (derivB ψ (j' + 1) π).ρ (Prod.sc n x) v := rfl
  have hd0 : d ≠ 0 := Units.ne_zero _
  refine ⟨v, d⁻¹ * c', hv, ?_, ?_⟩
  · have hc'' : c' • v = d • (derivB ψ (j' + 1) π).ρ (Prod.sc n x) v := (hc' v).symm.trans htw
    rw [mul_smul, hc'', smul_smul, inv_mul_cancel₀ hd0, one_smul]
  · rw [norm_mul, h1, mul_one, norm_inv, hd, norm_dpow_sc, ← Real.rpow_neg (nabs_pos' k x).le]
    congr 1
    push_cast
    ring

end Steps

section Main

theorem irreducible_of_top (ψ : AddChar k Circle) {N n h : ℕ} (X : GRep k N) (e : N = n + h) [Nontrivial X.V]
    (hcompl : ∀ S : Subrepresentation X.ρ, ∃ T : Subrepresentation X.ρ, IsCompl S.toSubmodule T.toSubmodule)
    (hdepth : ∀ S : Subrepresentation X.ρ, S ≠ ⊥ → ND ψ (subG S) h)
    {Z : Type} [AddCommGroup Z] [Module ℂ Z] (τ : Representation ℂ (GL (Fin n) k) Z) (hτ : τ.IsIrreducible)
    (χ : GL (Fin n) k →* ℂˣ) (eqv : (derivB ψ h (X.cast e)).ρ.Equiv (twist τ χ)) : X.ρ.IsIrreducible := by
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h0 => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (α := Submodule ℂ X.V) (congrArg Subrepresentation.toSubmodule h0)
  · by_contra hS
    rw [not_or] at hS
    obtain ⟨hS0, hS1⟩ := hS
    obtain ⟨T, hc⟩ := hcompl S
    have hT0 : T ≠ ⊥ := by
      rintro rfl
      apply hS1
      apply Subrepresentation.toSubmodule_injective
      have h2 := hc.sup_eq_top
      rw [show (⊥ : Subrepresentation X.ρ).toSubmodule = ⊥ from rfl, sup_bot_eq] at h2
      exact h2
    have := (nd_iff ψ (subG S) e).1 (hdepth S hS0)
    have := (nd_iff ψ (subG T) e).1 (hdepth T hT0)
    have h0 : ∀ a, DM ψ h e (X := X) (Y := subG T) (subProj S T hc)
        (DM ψ h e (X := subG S) (Y := X) (subIncl S) a) = 0 := fun a =>
      (DM_comp ψ h e (X := subG S) (Y := X) (Z := subG T) (subIncl S) (subProj S T hc) (zeroH _ _)
        (fun v => (subProj_subIncl_left S T hc v).symm) a).symm.trans (DM_zero ψ h e _ (fun _ => rfl) a)
    have key := range_ne_bot_ne_top (DM ψ h e (X := subG S) (Y := X) (subIncl S)).toLinearMap
      (DM ψ h e (X := subG T) (Y := X) (subIncl T)).toLinearMap
      (DM ψ h e (X := X) (Y := subG T) (subProj S T hc)).toLinearMap
      (DM_subIncl_injective ψ h e S T hc.symm)
      h0 (DM_proj_incl ψ h e T S hc)
    rcases eq_bot_or_eq_top_of_equiv_twist eqv hτ
        (LinearMap.range (DM ψ h e (X := subG S) (Y := X) (subIncl S)).toLinearMap) (by
        rintro g _ ⟨a, rfl⟩
        exact ⟨_, DM_comm ψ h e (subIncl S) g a⟩) with h1 | h1
    · exact key.1 h1
    · exact key.2 h1

theorem nd_of_irr (hT : DerivTop k) (hP : PosProdD k) (ψ : AddChar k Circle) (hψc : Continuous ψ) (hψ1 : ψ ≠ 1)
    {r t : ℕ} (π₁ : GRep k r) (π₂ : GRep k t) (s₁ : IsSmooth π₁.ρ) (i₁ : π₁.ρ.IsIrreducible)
    (u₁ : IsUnitarisable π₁.ρ) (s₂ : IsSmooth π₂.ρ) (i₂ : π₂.ρ.IsIrreducible) (u₂ : IsUnitarisable π₂.ρ)
    {n h : ℕ} (e : r + t = n + h) (htop : Prod.IsTopD ψ ((π₁.prod π₂).cast e)) (hsm : IsSmooth (π₁.prod π₂).ρ)
    (hun : IsUnitarisable (π₁.prod π₂).ρ)
    (hcompl : ∀ S : Subrepresentation (π₁.prod π₂).ρ, ∃ T : Subrepresentation (π₁.prod π₂).ρ,
      IsCompl S.toSubmodule T.toSubmodule)
    (S₀ : Subrepresentation (π₁.prod π₂).ρ) (hS₀ : S₀ ≠ ⊥) (hirr : S₀.toRepresentation.IsIrreducible) :
    ND ψ (subG S₀) h := by
  have hS₀nt : Nontrivial (subG S₀).V :=
    Submodule.nontrivial_iff_ne_bot.2 (fun h0 => hS₀ (Subrepresentation.toSubmodule_injective h0))
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · exact ⟨r + t, rfl, hS₀nt⟩
  have htop' := (isTopD_iff ψ _ e).1 htop
  have hN : 0 < r + t := by have := le_of_nd ψ _ htop'.1; omega
  obtain ⟨j₀, hj₀, hnd₀⟩ := exists_nd_pos ψ hψc hψ1 (subG S₀) hN (isSmooth_sub hsm S₀) hS₀nt
  obtain ⟨j, hjj, hndj, hgreat⟩ := exists_top ψ (subG S₀) hnd₀
  obtain ⟨T₀, hc⟩ := hcompl S₀
  have hjN := le_of_nd ψ _ hndj
  have ej : r + t = (r + t - j) + j := by omega
  have hinj := DM_subIncl_injective ψ j ej S₀ T₀ hc.symm
  rcases lt_trichotomy j h with hlt | heq | hgt
  · exfalso
    have htopS : Prod.IsTopD ψ ((subG S₀).cast ej) := (isTopD_iff ψ (subG S₀) ej).2 ⟨hndj, hgreat⟩
    obtain ⟨x, hx⟩ := GlobalTheory.CompanionTheory.CellOff.exists_nabs_lt k
    obtain ⟨v, c, hv0, hv, hc'⟩ := exists_eig_top ψ hψc hψ1 hT ((subG S₀).cast ej) (by omega)
      ((isSmooth_cast ej _).2 (isSmooth_sub hsm S₀)) ((isIrreducible_cast ej _).2 hirr)
      ((isUnitarisable_cast ej _).2 (isUnitarisable_sub hun S₀)) htopS x
    have hne : DM ψ j ej (X := subG S₀) (Y := π₁.prod π₂) (subIncl S₀) v ≠ 0 := fun h0 =>
      hv0 (hinj (h0.trans (map_zero _).symm))
    have hev : (derivB ψ j ((π₁.prod π₂).cast ej)).ρ (Prod.sc (r + t - j) x)
        (DM ψ j ej (X := subG S₀) (Y := π₁.prod π₂) (subIncl S₀) v) =
        c • DM ψ j ej (X := subG S₀) (Y := π₁.prod π₂) (subIncl S₀) v := by
      rw [← DM_comm ψ j ej (subIncl S₀) (Prod.sc (r + t - j) x) v, hv, map_smul]
    have hlt' := hP ψ hψc hψ1 r t π₁ π₂ s₁ i₁ u₁ s₂ i₂ u₂ n h e htop (r + t - j) j ej hlt x hx _ c hne hev
    linarith
  · exact heq ▸ hndj
  · exfalso
    have : Nontrivial (derivB ψ j ((subG S₀).cast ej)).V := (nd_iff ψ _ ej).1 hndj
    exact htop'.2 j hgt ⟨_, ej, hinj.nontrivial⟩

theorem prod_irreducible (hT : DerivTop k) (hP : PosProdD k) (hTop : TopProdD k) (ψ : AddChar k Circle)
    (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) : ∀ (N r t : ℕ), r + t = N → ∀ (π₁ : GRep k r) (π₂ : GRep k t),
      IsSmooth π₁.ρ → π₁.ρ.IsIrreducible → IsUnitarisable π₁.ρ → IsSmooth π₂.ρ → π₂.ρ.IsIrreducible →
      IsUnitarisable π₂.ρ → (π₁.prod π₂).ρ.IsIrreducible := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro r t hN π₁ π₂ s₁ i₁ u₁ s₂ i₂ u₂
  obtain ⟨E⟩ := GlobalTheory.CompanionTheory.HighestDeriv.nonempty_prod2_equiv π₁.ρ π₂.ρ
  rcases Nat.eq_zero_or_pos N with hN0 | hpos
  · subst hN0
    obtain ⟨rfl, rfl⟩ : r = 0 ∧ t = 0 := ⟨by omega, by omega⟩
    exact (GlobalTheory.SmGL.MultiIrr.isIrreducible_iff_of_equiv E).2
      (PositivityTheory.PfBern.Props2.prodGL0Irreducible_at _ _ π₁.ρ π₂.ρ i₁ i₂)
  obtain ⟨n, h, e, hh, htop, r', t', e₂, σ₁, σ₂, χ, sm1, ir1, un1, sm2, ir2, un2, ⟨eqv⟩⟩ :=
    hTop ψ hψc hψ1 r t π₁ π₂ s₁ i₁ u₁ s₂ i₂ u₂ (by omega)
  have hY := IH n (by omega) r' t' e₂ σ₁ σ₂ sm1 ir1 un1 sm2 ir2 un2
  have hadm : IsAdmissible (π₁.prod π₂).ρ := PositivityTheory.PfBern.Props1.isAdmissible_of_equiv E
    (PositivityTheory.PfBern.Props1.admissibleProd_holds k r t π₁.V π₂.V π₁.ρ π₂.ρ
      (PositivityTheory.PfBern.Props1.irrSmoothAdmissible_holds k r π₁.V π₁.ρ s₁ i₁)
      (PositivityTheory.PfBern.Props1.irrSmoothAdmissible_holds k t π₂.V π₂.ρ s₂ i₂))
  have hun : IsUnitarisable (π₁.prod π₂).ρ :=
    isUnitarisable_of_equiv E (GlobalTheory.SmGL.UnitInd.isUnitarisable_prod₂ u₁ u₂)
  have hcompl := PositivityTheory.PfBern.Props2.unitaryAdmissibleComplement_at (r + t) _ (π₁.prod π₂).ρ hadm hun
  have : Nontrivial (π₁.prod π₂).V := nontrivial_of_nd ψ _ ((isTopD_iff ψ _ e).1 htop).1
  refine irreducible_of_top ψ (π₁.prod π₂) e hcompl (fun S hS => ?_) _ ((isIrreducible_cast e₂ _).2 hY) χ eqv
  obtain ⟨S₀, hS₀, hle, hirr⟩ := exists_irreducible_le (π₁.prod π₂).ρ (GlobalTheory.T.compact_open_subgroups_basis k (r + t)) hadm hcompl S hS
  obtain ⟨T₀, hc⟩ := hcompl S₀
  exact nd_mono ψ S₀ S T₀ hle hc.symm
    (nd_of_irr hT hP ψ hψc hψ1 π₁ π₂ s₁ i₁ u₁ s₂ i₂ u₂ e htop hadm.1 hun hcompl S₀ hS₀ hirr)

end Main


variable (k) in
theorem bern_of_parts : DerivTop k → PosProdD k → TopProdD k → BernAt k := by
  intro hT hP hTop r t V W _ _ _ _ π₁ π₂ s₁ i₁ u₁ s₂ i₂ u₂
  obtain ⟨ψ, hψc, hψ1⟩ := PositivityTheory.PfBern.Props1.existsAddChar_holds k
  obtain ⟨E⟩ := GlobalTheory.CompanionTheory.HighestDeriv.nonempty_prod2_equiv π₁ π₂
  exact (GlobalTheory.SmGL.MultiIrr.isIrreducible_iff_of_equiv E).1
    (prod_irreducible hT hP hTop ψ hψc hψ1 (r + t) r t rfl ⟨V, π₁⟩ ⟨W, π₂⟩ s₁ i₁ u₁ s₂ i₂ u₂)

end PositivityTheory.RgUd.Prod.Asm
