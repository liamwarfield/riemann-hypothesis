module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivProdIrrZero
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open GlobalTheory.Parabolic (Embeds isIrreducible_of_equiv mem_fixed)

namespace GlobalTheory.LocGL.Tests

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem nonempty_equiv_parInd_zero {d : Fin 0 → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin 0)
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) V) (L : ℂ ≃ₗ[ℂ] V) :
    Nonempty ((detRep (Fin 0) (1 : kˣ →* ℂˣ)).Equiv (parInd e ρ)) := by
  have hg : ∀ g : GL (Fin 0) k, g = 1 := fun g => Units.ext (Subsingleton.elim _ _)
  let f : ℂ →ₗ[ℂ] IndSp e ρ :=
    { toFun := fun c => ⟨⟨fun _ => L c, fun p g => by
          obtain rfl : p = 1 := Subtype.ext (hg _)
          simp⟩, mem_smoothPart_of_nhds (Filter.Eventually.of_forall fun g => rfl)⟩
      map_add' := fun a b => Subtype.ext (Subtype.ext (funext fun _ => map_add L a b))
      map_smul' := fun a b => Subtype.ext (Subtype.ext (funext fun _ => map_smul L a b)) }
  refine ⟨equivOfBijective ⟨f, fun g => by rw [hg g, map_one, map_one]; rfl⟩ ⟨fun a b h => ?_, fun φ => ?_⟩⟩
  · have h1 : L a = L b := congrArg (fun φ : IndSp e ρ => φ.1.1 1) h
    exact L.injective h1
  · refine ⟨L.symm (φ.1.1 1), Subtype.ext (Subtype.ext (funext fun g => ?_))⟩
    rw [hg g]
    exact L.apply_symm_apply _

theorem nonempty_equiv_prodIrr_zero (x : Fin 0 → IrrGL (k := k)) (hd : ∑ a, (x a).1 = 0) :
    Nonempty ((detRep (Fin 0) (1 : kˣ →* ℂˣ)).Equiv (prodIrr x hd)) :=
  nonempty_equiv_parInd_zero _ _ (PiTensorProduct.isEmptyEquiv (R := ℂ) (Fin 0) (s := fun a => (x a).2.rep.V)).symm

theorem empty_spec : IsZ (0 : Multiset (Segment k)) (detRep (Fin 0) (1 : kˣ →* ℂˣ)) ∧
    IsL (0 : Multiset (Segment k)) (detRep (Fin 0) (1 : kˣ →* ℂˣ)) := by
  obtain ⟨φ⟩ := nonempty_equiv_prodIrr_zero (k := k) Fin.elim0 rfl
  have ho : IsOrderedForm (k := k) (Fin.elim0 : Fin 0 → Segment k) 0 := ⟨rfl, fun i => i.elim0⟩
  exact ⟨⟨0, Fin.elim0, rfl, ⟨_, ho, fun i => i.elim0⟩, (isSocle_self (isIrreducible_ofChar _)).of_equiv (.refl _) φ⟩,
    ⟨0, Fin.elim0, rfl, ⟨_, ho, fun i => i.elim0⟩, (isCosocle_self (isIrreducible_ofChar _)).of_equiv (.refl _) φ⟩⟩

end GlobalTheory.LocGL.Tests
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsLevelProjLevelProj
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL
open scoped Topology

namespace GlobalTheory.LBC

section Groups

variable {k k' : Type} [Field k] [Field k'] [Algebra k k']

def galAct (s : k' ≃ₐ[k] k') (n : ℕ) : GL (Fin n) k' →* GL (Fin n) k' :=
  GeneralLinearGroup.map s.toAlgHom.toRingHom

@[simp] theorem galAct_one (n : ℕ) : galAct (1 : k' ≃ₐ[k] k') n = MonoidHom.id _ := by
  ext g i j; rfl

theorem galAct_mul (s t : k' ≃ₐ[k] k') (n : ℕ) : galAct (s * t) n = (galAct s n).comp (galAct t n) := by
  ext g i j; rfl

def incl (k' : Type) [Field k'] [Algebra k k'] (n : ℕ) : GL (Fin n) k →* GL (Fin n) k' :=
  GeneralLinearGroup.map (algebraMap k k')

@[simp] theorem incl_apply {n : ℕ} (γ : GL (Fin n) k) (i j : Fin n) :
    (incl k' n γ : Matrix (Fin n) (Fin n) k') i j = algebraMap k k' ((γ : Matrix (Fin n) (Fin n) k) i j) := rfl

@[simp] theorem galAct_incl (s : k' ≃ₐ[k] k') {n : ℕ} (γ : GL (Fin n) k) : galAct s n (incl k' n γ) = incl k' n γ := by
  ext i j
  change s (algebraMap k k' ((γ : Matrix (Fin n) (Fin n) k) i j)) = _
  exact s.commutes _


variable (k) in
def norm (s : k' ≃ₐ[k] k') {n : ℕ} (g : GL (Fin n) k') : GL (Fin n) k' :=
  (List.ofFn fun j : Fin (Module.finrank k k') => galAct (s ^ (j : ℕ)) n g).prod

def IsStable (s : k' ≃ₐ[k] k') {n : ℕ} (K : Subgroup (GL (Fin n) k')) : Prop := K.map (galAct s n) = K

end Groups

section Traces

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def IsLevelProj (π : Representation ℂ G V) (K : Subgroup G) (A : V →ₗ[ℂ] V)
    (T : fixed π K →ₗ[ℂ] fixed π K) : Prop :=
  ∀ v : fixed π K, ((T v : V) - A v) ∈ twKer π K 1

def HasLevelTrace (π : Representation ℂ G V) (K : Subgroup G) (A : V →ₗ[ℂ] V) (c : ℂ) : Prop :=
  FiniteDimensional ℂ (fixed π K) ∧ ∃ T, IsLevelProj π K A T ∧ LinearMap.trace ℂ _ T = c

end Traces

section Unique

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V} {K : Subgroup G}
  {A : V →ₗ[ℂ] V}

def levelProj (hc : IsCompl (fixed π K) (twKer π K 1)) (A : V →ₗ[ℂ] V) : fixed π K →ₗ[ℂ] fixed π K :=
  Submodule.projectionOnto _ _ hc ∘ₗ A ∘ₗ (fixed π K).subtype

end Unique

section Lift

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [Algebra k k']
  {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]


variable (k) in
def IsTwInt (s : k' ≃ₐ[k] k') (P : Representation ℂ (GL (Fin n) k') W) (I : W →ₗ[ℂ] W) : Prop :=
  (∀ g, P (galAct s n g) ∘ₗ I = I ∘ₗ P g) ∧ 0 < Module.finrank k k' ∧ I ^ Module.finrank k k' = 1

theorem IsTwInt.mem_fixed {s : k' ≃ₐ[k] k'} {P : Representation ℂ (GL (Fin n) k') W} {I : W →ₗ[ℂ] W}
    (hI : IsTwInt k s P I) {K : Subgroup (GL (Fin n) k')} (hK : IsStable s K) {v : W} (hv : v ∈ fixed P K) :
    I v ∈ fixed P K := by
  intro x
  have hx : (x : GL (Fin n) k') ∈ K.map (galAct s n) := by rw [hK]; exact x.2
  obtain ⟨y, hy, e⟩ := Subgroup.mem_map.1 hx
  have h1 := LinearMap.congr_fun (hI.1 y) v
  simp only [LinearMap.comp_apply] at h1
  have h2 : P y v = v := by simpa using hv ⟨y, hy⟩
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  rw [← e, h1, h2]


variable (k) in
def TwCharVal (s : k' ≃ₐ[k] k') (P : Representation ℂ (GL (Fin n) k') W) (I : W →ₗ[ℂ] W) (g' : GL (Fin n) k')
    (c : ℂ) : Prop :=
  ∃ U ∈ 𝓝 (1 : GL (Fin n) k'), ∀ K : Subgroup (GL (Fin n) k'), IsOpen (K : Set (GL (Fin n) k')) →
    IsCompact (K : Set (GL (Fin n) k')) → IsStable s K → (K : Set (GL (Fin n) k')) ⊆ U →
      HasLevelTrace P K (P g' ∘ₗ I) c

def CharVal (π : Representation ℂ (GL (Fin n) k) V) (γ : GL (Fin n) k) (c : ℂ) : Prop :=
  ∃ U ∈ 𝓝 (1 : GL (Fin n) k), ∀ K : Subgroup (GL (Fin n) k), IsOpen (K : Set (GL (Fin n) k)) →
    IsCompact (K : Set (GL (Fin n) k)) → (K : Set (GL (Fin n) k)) ⊆ U → HasLevelTrace π K (π γ) c

def IsLBC (s : k' ≃ₐ[k] k') (π : Representation ℂ (GL (Fin n) k) V) (P : Representation ℂ (GL (Fin n) k') W) :
    Prop :=
  IsSmooth π ∧ π.IsIrreducible ∧ IsSmooth P ∧ P.IsIrreducible ∧
  ∃ I : W →ₗ[ℂ] W, IsTwInt k s P I ∧
    ∀ g' : GL (Fin n) k', (norm k s g' : Matrix (Fin n) (Fin n) k').charpoly.Separable →
      ∀ γ : GL (Fin n) k, (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k k') =
          (norm k s g' : Matrix (Fin n) (Fin n) k').charpoly →
        ∃ c : ℂ, TwCharVal k s P I g' c ∧ CharVal π γ c

def IsLBCCl (s : k' ≃ₐ[k] k') (x : IrrGL (k := k)) (y : IrrGL (k := k')) : Prop :=
  ∃ (m : ℕ) (π : IrrRep (GL (Fin m) k)) (P : IrrRep (GL (Fin m) k')), x = ⟨m, π.cl⟩ ∧ y = ⟨m, P.cl⟩ ∧
    IsLBC s π.ρ P.ρ

end Lift

end GlobalTheory.LBC
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntegrandPeriodic
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift.Model

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
  {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}

theorem cA_inc (e : D.host.E) : cA D (incA D e) = incA D (star e) := by
  rfl

theorem hO_eq_trace (x y : WO V W) :
    hO V W x y = Matrix.trace ((V.gram⁻¹).map (incA D) * ((y.map (cA D))ᵀ * W.gram.map (incA D) * x)) := by
  simp only [hO, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

theorem hO_ratMul (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (u v : WO V W) :
    hO V W (ratMul C u) (ratMul C v) =
      Matrix.trace ((V.gram⁻¹).map (incA D) * ((v.map (cA D))ᵀ * (Cᴴ * W.gram * C).map (incA D) * u)) := by
  have h : (C.map (incA D)).map (cA D) = (Cᴴ.map (incA D))ᵀ := by
    ext i j; simp [Matrix.map_apply, cA_inc]
  rw [hO_eq_trace]
  unfold ratMul
  rw [Matrix.map_mul, h, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem gram_eq {Y : Lag W} {C} (h : IsLagFrame W Y C) : C.1ᴴ * W.gram * C.1 = C.2ᴴ * W.gram * C.2 := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  funext j k
  have m : ∀ j, ((fun a => C.1 a j), (fun a => C.2 a j)) ∈ Y.1 := fun j => h ▸ Submodule.subset_span ⟨j, rfl⟩
  have := Y.2.2 _ (m j) _ (m k)
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply] at this
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply] using this

theorem ratMul_add (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (γ) (u : WO V W) :
    ratMul C (ratW W V γ + u) = ratW W V (C * γ) + ratMul C u := by
  unfold ratMul ratW
  rw [Matrix.mul_add, Matrix.map_mul]

theorem integrand_periodic (hψ : ∀ x, ‖ψ x‖ = 1) {Y : Lag W} {C} (h : IsLagFrame W Y C) {f₁ f₂ : WO V W → ℂ}
    (h₁ : IsThetaFunO ψ V W f₁) (h₂ : IsThetaFunO ψ V W f₂) (γ) (u : WO V W) :
    f₁ (ratMul C.1 (ratW W V γ + u)) * star (f₂ (ratMul C.2 (ratW W V γ + u))) =
      f₁ (ratMul C.1 u) * star (f₂ (ratMul C.2 u)) := by
  have e : ∀ B : Matrix (Fin W.rank) (Fin W.rank) D.host.E, ratW W V (B * γ) = ratMul B (ratW W V γ) := fun B => by
    unfold ratMul ratW; rw [Matrix.map_mul]
  have s : symplOH V W (ratW W V (C.1 * γ)) (ratMul C.1 u) = symplOH V W (ratW W V (C.2 * γ)) (ratMul C.2 u) := by
    rw [e, e]; unfold symplOH symplO; rw [hO_ratMul, hO_ratMul, gram_eq h]
  rw [ratMul_add, ratMul_add, h₁.quasi, h₂.quasi, s, star_mul']
  set z := ψ (-(symplOH V W (ratW W V (C.2 * γ)) (ratMul C.2 u))) with hz
  have : z * star z = 1 := by
    have := Complex.mul_conj' z
    rw [hz, hψ] at this
    simpa using this
  calc _ = (z * star z) * (f₁ (ratMul C.1 u) * star (f₂ (ratMul C.2 u))) := by ring
    _ = _ := by rw [this, one_mul]

theorem swPair_rank_zero {νV 𝓗 νW 𝓖 μ 𝓕 fr} (hs : SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr) (h : W.rank = 0)
    (f₁ f₂ : WO V W → ℂ) :
    HasSum (fun Y : Lag W => ((νV 𝓗).toReal : ℂ) * lagTerm μ 𝓕 (fr Y) f₁ f₂)
      (∫ h in 𝓗, thetaKO om h 1 f₁ * star (thetaKO om h 1 f₂) ∂νV) := by
  haveI : IsEmpty (Fin W.rank) := by rw [h]; infer_instance
  haveI : Subsingleton (WO V W) := ⟨fun a b => by funext i; exact isEmptyElim i⟩
  haveI : Subsingleton (Lag W) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  haveI : Unique (Lag W) := uniqueOfSubsingleton default
  have hμ : μ 𝓕 = 1 := hs.covol.2.2
  have hc : ∀ g : WO V W → ℂ, g = fun _ => g 0 := fun g => funext fun w => by rw [Subsingleton.elim w 0]
  have z : ∀ x y : WO V W, symplOH V W x y = 0 := fun x y => by simp [symplOH, symplO, hO]
  have one : IsThetaFunO ψ V W (fun _ => 1) :=
    ⟨fun γ w => by simp [z], ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp [heisO, z]⟩, continuous_const,
      fun _ _ _ _ _ => contDiff_const⟩
  have key : ∀ p, ∀ f : WO V W → ℂ, om p f 0 = f 0 * om p (fun _ => 1) 0 := fun p f => by
    have : f = f 0 • (fun _ => (1 : ℂ)) := by funext w; simp [Subsingleton.elim w 0]
    conv_lhs => rw [this, map_smul]
    simp
  have nm : ∀ p, om p (fun _ => 1) 0 * star (om p (fun _ => 1) 0) = 1 := fun p => by
    have u := hs.weil.om_unit μ 𝓕 hs.covol.1 hs.covol.2.1 p _ one
    rw [hc (om p fun _ => 1)] at u
    simp only [setLIntegral_const, hμ, mul_one, enorm_one, one_pow] at u
    have u2 : ‖om p (fun _ => 1) 0‖ ^ 2 = 1 := by
      have := congrArg ENNReal.toReal u
      rwa [ENNReal.toReal_pow, toReal_enorm, ENNReal.toReal_one] at this
    have := Complex.mul_conj' (om p (fun _ => 1) 0)
    rw [← Complex.ofReal_pow, u2] at this
    simpa using this
  have I : ∀ g, thetaKO om g 1 f₁ * star (thetaKO om g 1 f₂) = f₁ 0 * star (f₂ 0) := fun g => by
    unfold thetaKO
    rw [key _ f₁, key _ f₂, star_mul']
    calc _ = (om (g, 1) (fun _ => 1) 0 * star (om (g, 1) (fun _ => 1) 0)) * (f₁ 0 * star (f₂ 0)) := by ring
      _ = _ := by rw [nm, one_mul]
  have L : ∀ C, lagTerm μ 𝓕 C f₁ f₂ = f₁ 0 * star (f₂ 0) := fun C => by
    have : μ.real 𝓕 = 1 := by rw [Measure.real, hμ, ENNReal.toReal_one]
    unfold lagTerm
    simp only [Subsingleton.elim (ratMul _ _ : WO V W) 0]
    rw [setIntegral_const, this, one_smul]
  simp only [I, L, setIntegral_const]
  convert hasSum_unique (fun _ : Lag W => ((νV 𝓗).toReal : ℂ) * (f₁ 0 * star (f₂ 0))) using 1
  simp [Measure.real]

end GlobalTheory.RawLift.Model

end
end
