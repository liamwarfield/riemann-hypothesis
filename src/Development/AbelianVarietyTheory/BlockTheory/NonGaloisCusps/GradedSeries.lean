module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GradedSeries
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Series

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

def IsLaurent (u : ℤ → M) : Prop := ∃ m : ℤ, ∀ k < m, u k = 0

def serMul (f : PowerSeries L) (u : ℤ → M) : ℤ → M :=
  fun k => ∑ᶠ j : ℕ, PowerSeries.coeff j f • u (k - (j : ℤ))


theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serMul_finite (f : PowerSeries L) {u : ℤ → M}
    (hu : _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.IsLaurent u) (k : ℤ) :
    (Function.support fun j : ℕ => PowerSeries.coeff j f • u (k - (j : ℤ))).Finite := by
  obtain ⟨m, hm⟩ := hu
  refine (Set.finite_Iic (k - m).toNat).subset ?_
  intro j hj
  rw [Function.mem_support] at hj
  rw [Set.mem_Iic]
  by_contra h
  push Not at h
  exact hj (by rw [hm _ (by omega), smul_zero])


theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serMul_one (u : ℤ → M) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serMul (1 : PowerSeries L) u = u := by
  funext k
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serMul
  rw [finsum_eq_single _ 0 (fun j hj => by simp [PowerSeries.coeff_one, hj])]
  simp

variable (L) in
def serSpan (S : Set (ℤ → M)) : Submodule L (ℤ → M) :=
  Submodule.span L {w | ∃ (f : PowerSeries L) (u : ℤ → M), u ∈ S ∧ IsLaurent u ∧ w = serMul f u}

def shiftSer (a : ℤ) (F : Submodule L M) : Submodule L (ℤ → M) where
  carrier := {u | (∀ k < -a, u k = 0) ∧ ∀ k, u k ∈ F}
  zero_mem' := ⟨fun _ _ => rfl, fun _ => F.zero_mem⟩
  add_mem' := by
    rintro u w ⟨hu, hu'⟩ ⟨hw, hw'⟩
    exact ⟨fun k hk => by simp [hu k hk, hw k hk], fun k => F.add_mem (hu' k) (hw' k)⟩
  smul_mem' := by
    rintro c u ⟨hu, hu'⟩
    exact ⟨fun k hk => by simp [hu k hk], fun k => F.smul_mem c (hu' k)⟩

def gradedSer (F : ℤ → Submodule L M) : Submodule L (ℤ → M) := ⨆ a : ℤ, shiftSer a (F a)

end Series

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def Dlet (i : ZMod n) : Submodule LL (T.V ⊗[Qp] B) := DcrisL PD T.ρ (W.emb i)

def FilLet (i : ZMod n) (τ : K →ₐ[Qp] LL) (a : ℤ) : Submodule LL (T.V ⊗[Qp] B) :=
  Dlet W T i ⊓
    (FildR PD T.ρ τ a ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ').comap
      (ιV PD (LL := LL) (V := T.V))

def toDR (F : Submodule LL (T.V ⊗[Qp] B)) : Submodule LL (T.V ⊗[Qp] BdR) :=
  F.map (ιV PD (LL := LL) (V := T.V))

def Nlev (i : ZMod n) (ζ : LL) : Submodule LL (ℤ → T.V ⊗[Qp] BdR) :=
  serSpan LL (Set.range (W.levN T i ζ))

def IsExpansion (i : ZMod n) (ζ : LL) (y : W.DD T) (u : ℤ → T.V ⊗[Qp] BdR) : Prop :=
  IsLaurent u ∧ ∃ (m : ℕ) (hy : W.Q ^ m • y ∈ W.N T),
    serMul (W.lev i ζ (W.Q ^ m)) u = W.levN T i ζ ⟨W.Q ^ m • y, hy⟩

def phiNlev (i : ZMod n) (ζ : LL) : Submodule LL (ℤ → T.V ⊗[Qp] BdR) :=
  serSpan LL {u | ∃ y ∈ W.N T, IsExpansion W T i ζ (W.φD T y) u}

variable (PD) in
def phiSer (j : ℕ) (u : ℤ → T.V ⊗[Qp] B) : ℤ → T.V ⊗[Qp] BdR :=
  fun k => ιV PD (LL := LL) (V := T.V)
    ((((PD.p : LL) ^ j) ^ k) • ((φVB PD (LL := LL) (V := T.V)) ^ j) (u k))


variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.levN_mem_Nlev (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) :
    W.levN T i ζ x ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.Nlev W T i ζ := by
  refine Submodule.subset_span ⟨1, W.levN T i ζ x, ⟨x, rfl⟩, ?_,
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serMul_one _).symm⟩
  obtain ⟨m, hm⟩ := W.levN_supp T i ζ x
  exact ⟨m, hm⟩

end Generic

section Statement

variable {l : ℕ} [Fact l.Prime]

def resEmb {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)
    (τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1) : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1 :=
  τ.comp (IntermediateField.inclusion h.2.2.1)

def LatticeAtLevels (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (H : LocHW l P) (F : LocFon l P AI H) (C : LocCmpT l P AI H F) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ →
    ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1),
      (∀ j : ℕ, j < s → IsPrimitiveRoot ζ (l ^ j) →
        Nlev (H.W K s LL h) T i ζ =
          shiftSer 0 (toDR (PD := P.PD K) T (Dlet (H.W K s LL h) T i))) ∧
      (∀ τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1, H.IsPt h i ζ τ →
        phiNlev (H.W K s LL h) T i ζ =
            shiftSer 0 (toDR (PD := P.PD K) T (Dlet (H.W K s LL h) T i)) ∧
          Nlev (H.W K s LL h) T i ζ =
            gradedSer fun a =>
              toDR (PD := P.PD K) T (FilLet (H.W K s LL h) T i (resEmb h τ) a)) ∧
      (∀ j : ℕ, 1 ≤ j → IsPrimitiveRoot ζ (l ^ (s + j)) →
        Nlev (H.W K s LL h) T i ζ =
            serSpan ↥LL.1 (phiSer (P.PD K) T j ''
              (serSpan ↥LL.1 (Set.range
                ((C.C K s LL h).tie.levB T (i - (j : ZMod _)) (ζ ^ (l ^ j)))) :
                  Set (ℤ → T.V ⊗[ℚ_[l]] P.R.B))) ∧
          ∀ τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1, H.IsPt h (i - (j : ZMod _)) (ζ ^ (l ^ j)) τ →
            Nlev (H.W K s LL h) T i ζ =
              gradedSer fun a =>
                toDR (PD := P.PD K) T
                  ((FilLet (H.W K s LL h) T (i - (j : ZMod _)) (resEmb h τ) a).map
                    ((φVB (P.PD K) (LL := ↥LL.1) (V := T.V)) ^ j)))

end Statement

end GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)

section Objects

variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

def IsEquivariant (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V') :
    Prop :=
  ∀ g x, f (ρ g x) = ρ' g (f x)

theorem mem_Dcris (ρ : Representation LL G V) (x : V ⊗[Qp] B) :
    x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp [Dcris, Submodule.mem_iInf, sub_eq_zero]

theorem actVB_mulVB (ρ : Representation LL G V) (g : G) (c : K₀) (x : V ⊗[Qp] B) :
    actVB PD ρ g (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x) =
      mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c (actVB PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, mulVB]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem comm_smul (c : K₀) (x : B ⊗[Qp] V) :
    TensorProduct.comm Qp B V (c • x) =
      mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c (TensorProduct.comm Qp B V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b v =>
    rw [TensorProduct.smul_tmul', Algebra.smul_def]
    simp [mulVB]
  | add a b ha hb => simp only [smul_add, map_add (f := _), ha, hb]

def DcrisK₀ (ρ : Representation LL G V) : Submodule K₀ (B ⊗[Qp] V) where
  carrier := {x | TensorProduct.comm Qp B V x ∈ Dcris PD ρ}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add (f := _)] at ha hb ⊢
    exact (Dcris PD ρ).add_mem ha hb
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, mem_Dcris] at hx ⊢
    intro g
    rw [comm_smul (LL := LL), actVB_mulVB, hx]

def comparison (ρ : Representation LL G V) :
    B ⊗[K₀] ↥(DcrisK₀ PD ρ) →ₗ[B] B ⊗[Qp] V :=
  LinearMap.liftBaseChange B (DcrisK₀ PD ρ).subtype

theorem comparison_tmul (ρ : Representation LL G V) (b : B) (d : ↥(DcrisK₀ PD ρ)) :
    comparison PD ρ (b ⊗ₜ[K₀] d) = b • (d : B ⊗[Qp] V) := by
  simp [comparison]

def tensorB (f : V →ₗ[LL] V') : V ⊗[Qp] B →ₗ[LL] V' ⊗[Qp] B :=
  AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B)

theorem tensorB_mem {ρ : Representation LL G V} {ρ' : Representation LL G V'} {f : V →ₗ[LL] V'}
    (hf : IsEquivariant ρ ρ' f) (x : V ⊗[Qp] B) (hx : x ∈ Dcris PD ρ) :
    tensorB (Qp := Qp) (B := B) f x ∈ Dcris PD ρ' := by
  have hm : ∀ g y, tensorB (Qp := Qp) (B := B) f (actVB PD ρ g y) =
      actVB PD ρ' g (tensorB (Qp := Qp) (B := B) f y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [tensorB, actVB, hf g]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  rw [mem_Dcris] at hx ⊢
  intro g
  rw [← hm, hx]

def DcrisMap {ρ : Representation LL G V} {ρ' : Representation LL G V'} {f : V →ₗ[LL] V'}
    (hf : IsEquivariant ρ ρ' f) : ↥(Dcris PD ρ) →ₗ[LL] ↥(Dcris PD ρ') :=
  (tensorB (Qp := Qp) (B := B) f).restrict (tensorB_mem PD hf)

def prodB : (V ⊗[Qp] B) ⊗[LL] (V' ⊗[Qp] B) →ₗ[LL] (V ⊗[LL] V') ⊗[Qp] B :=
  (AlgebraTensorModule.map (LinearMap.id : V ⊗[LL] V' →ₗ[LL] V ⊗[LL] V')
      (LinearMap.mul' Qp B)).comp
    (AlgebraTensorModule.tensorTensorTensorComm Qp Qp LL LL V B V' B).toLinearMap

theorem prodB_tmul (v : V) (b : B) (v' : V') (b' : B) :
    prodB (LL := LL) ((v ⊗ₜ[Qp] b) ⊗ₜ[LL] (v' ⊗ₜ[Qp] b')) = (v ⊗ₜ[LL] v') ⊗ₜ[Qp] (b * b') := by
  simp [prodB]

end Objects

def InvariantsEq : Prop :=
  ∀ b : B, (∀ g, PD.actB g b = b) ↔ b ∈ Set.range (algebraMap K₀ B)

theorem invariantsEq : InvariantsEq PD := fun b =>
  ⟨fun h => PD.invB b h, by
    rintro ⟨c, rfl⟩ g
    exact (PD.actB g).commutes c⟩

variable (LL : Type) [Field LL] [Algebra Qp LL]

def DimLe : Prop :=
  FontaineLe PD LL ∧
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V), FiniteDimensional LL ↥(Dcris PD ρ)

def ComparisonBij : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V),
    IsCrys PD ρ → Function.Bijective (comparison PD ρ)

def SubCrys : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V)
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL G V') (f : V' →ₗ[LL] V),
    IsEquivariant ρ' ρ f → Function.Injective f → IsCrys PD ρ → IsCrys PD ρ'

def QuotCrys : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V)
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL G V') (f : V →ₗ[LL] V'),
    IsEquivariant ρ ρ' f → Function.Surjective f → IsCrys PD ρ → IsCrys PD ρ'

def SumCrys : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V)
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL G V'),
    IsCrys PD ρ → IsCrys PD ρ' → IsCrys PD (ρ.prod ρ')

def TensorCrys : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V)
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL G V'),
    IsCrys PD ρ → IsCrys PD ρ' → IsCrys PD (ρ.tprod ρ')

def DualCrys : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V),
    IsCrys PD ρ → IsCrys PD ρ.dual

def DcrisExact : Prop :=
  ∀ (V₀ : Type) [AddCommGroup V₀] [Module LL V₀] [Module Qp V₀] [IsScalarTower Qp LL V₀]
    [FiniteDimensional LL V₀] (ρ₀ : Representation LL G V₀)
    (V₁ : Type) [AddCommGroup V₁] [Module LL V₁] [Module Qp V₁] [IsScalarTower Qp LL V₁]
    [FiniteDimensional LL V₁] (ρ₁ : Representation LL G V₁)
    (V₂ : Type) [AddCommGroup V₂] [Module LL V₂] [Module Qp V₂] [IsScalarTower Qp LL V₂]
    [FiniteDimensional LL V₂] (ρ₂ : Representation LL G V₂)
    (i : V₀ →ₗ[LL] V₁) (p : V₁ →ₗ[LL] V₂) (hi : IsEquivariant ρ₀ ρ₁ i) (hp : IsEquivariant ρ₁ ρ₂ p),
    Function.Injective i → Function.Exact i p → Function.Surjective p →
    IsCrys PD ρ₀ → IsCrys PD ρ₁ → IsCrys PD ρ₂ →
    Function.Injective (DcrisMap PD hi) ∧ Function.Exact (DcrisMap PD hi) (DcrisMap PD hp) ∧
      Function.Surjective (DcrisMap PD hp)

def LetterDim : Prop :=
  Nat.card (K₀ →ₐ[Qp] LL) = finrank Qp K₀ →
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V), IsCrys PD ρ →
    ∀ τ₀ : K₀ →ₐ[Qp] LL,
      FiniteDimensional LL ↥(DcrisL PD ρ τ₀) ∧ finrank LL ↥(DcrisL PD ρ τ₀) = finrank LL V

def FormalismFor : Prop :=
  InvariantsEq PD ∧ DimLe PD LL ∧ ComparisonBij PD LL ∧ SubCrys PD LL ∧ QuotCrys PD LL ∧
    SumCrys PD LL ∧ TensorCrys PD LL ∧ DualCrys PD LL ∧ DcrisExact PD LL ∧ LetterDim PD LL

end Generic

section Local

variable (l : ℕ) [Fact l.Prime] (P : LocPrime l)

def LocInvariantsEq : Prop := ∀ K : FinExt l, InvariantsEq (P.PD K)

def LocDimLe : Prop := ∀ K LL : FinExt l, DimLe (P.PD K) ↥LL.1

def LocComparisonBij : Prop := ∀ K LL : FinExt l, ComparisonBij (P.PD K) ↥LL.1

def LocSubCrys : Prop := ∀ K LL : FinExt l, SubCrys (P.PD K) ↥LL.1

def LocQuotCrys : Prop := ∀ K LL : FinExt l, QuotCrys (P.PD K) ↥LL.1

def LocSumCrys : Prop := ∀ K LL : FinExt l, SumCrys (P.PD K) ↥LL.1

def LocTensorCrys : Prop := ∀ K LL : FinExt l, TensorCrys (P.PD K) ↥LL.1

def LocDualCrys : Prop := ∀ K LL : FinExt l, DualCrys (P.PD K) ↥LL.1

def LocDcrisExact : Prop := ∀ K LL : FinExt l, DcrisExact (P.PD K) ↥LL.1

def LocLetterDim : Prop := ∀ K LL : FinExt l, LetterDim (P.PD K) ↥LL.1

def FontaineFormalism : Prop :=
  LocInvariantsEq l P ∧ LocDimLe l P ∧ LocComparisonBij l P ∧ LocSubCrys l P ∧ LocQuotCrys l P ∧
    LocSumCrys l P ∧ LocTensorCrys l P ∧ LocDualCrys l P ∧ LocDcrisExact l P ∧ LocLetterDim l P

theorem fontaineFormalism_iff :
    FontaineFormalism l P ↔ ∀ K LL : FinExt l, FormalismFor (P.PD K) ↥LL.1 :=
  ⟨fun h K LL => ⟨h.1 K, h.2.1 K LL, h.2.2.1 K LL, h.2.2.2.1 K LL, h.2.2.2.2.1 K LL,
      h.2.2.2.2.2.1 K LL, h.2.2.2.2.2.2.1 K LL, h.2.2.2.2.2.2.2.1 K LL, h.2.2.2.2.2.2.2.2.1 K LL,
      h.2.2.2.2.2.2.2.2.2 K LL⟩,
    fun h => ⟨fun K => (h K K).1, fun K LL => (h K LL).2.1, fun K LL => (h K LL).2.2.1,
      fun K LL => (h K LL).2.2.2.1, fun K LL => (h K LL).2.2.2.2.1,
      fun K LL => (h K LL).2.2.2.2.2.1, fun K LL => (h K LL).2.2.2.2.2.2.1,
      fun K LL => (h K LL).2.2.2.2.2.2.2.1, fun K LL => (h K LL).2.2.2.2.2.2.2.2.1,
      fun K LL => (h K LL).2.2.2.2.2.2.2.2.2⟩⟩

end Local

end GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.UnitDualParts
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def IsSumLat {T T' T'' : LocLat G Qp LL O} (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L) : Prop :=
  Function.Bijective (fun p : T.V × T'.V => i.f p.1 + i'.f p.2) ∧
    ∀ z ∈ T''.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = i.f x + i'.f y

def SumFor (W : LocWach PD LL O v n) : Prop :=
  ∀ (T T' T'' : LocLat G Qp LL O), IsCrys PD T.ρ → IsCrys PD T'.ρ →
    ∀ (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L), IsSumLat i i' →
      ∃ σ : (W.DD T × W.DD T') ≃ₗ[W.EE] W.DD T'',
        (∀ x y, σ (x, y) = W.map i x + W.map i' y) ∧
        (∀ x y, W.φD T'' (σ (x, y)) = σ (W.φD T x, W.φD T' y)) ∧
        (∀ (g : W.Gam) x y, W.γD T'' g (σ (x, y)) = σ (W.γD T g x, W.γD T' g y)) ∧
        ∀ x y, σ (x, y) ∈ W.N T'' ↔ (x ∈ W.N T ∧ y ∈ W.N T')

variable {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

def UnitFor (E : EtTie W RA RW inclR φR gR πA) : Prop :=
  ∀ e₀ : ↥W.one.L.T, Submodule.span O {e₀} = ⊤ →
    ∃ e : W.DD W.one,
      E.jD W.one e = (1 : RW) ⊗ₜ[O] e₀ ∧
      Function.Bijective (fun c : W.EE => c • e) ∧
      W.φD W.one e = e ∧
      (∀ g : W.Gam, W.γD W.one g e = e) ∧
      W.N W.one = Submodule.span (LetA O n) {e}

end Generic

def UnitPart (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), UnitFor (F.E K s LL h).tie

def SumPart (l : ℕ) [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), SumFor (H.W K s LL h)

end GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.LettersFreeOfRank
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

abbrev rk : ℕ := finrank O ↥T.L.T

abbrev letterModule (i : ZMod n) : Module (PowerSeries O) ↥(W.Nl T i) :=
  Module.compHom _ (Pi.constRingHom (ZMod n) (PowerSeries O))

attribute [local instance] letterModule


variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) in
attribute [local instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.letterModule in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.letter_smul (i : ZMod n) (c : PowerSeries O)
    (x : ↥(W.Nl T i)) :
    ((c • x : ↥(W.Nl T i)) : W.DD T) = (Pi.single i c : _root_.Formalism.BasicNotions.LetA O n) • (x : W.DD T) := by
  obtain ⟨x, hx⟩ := x
  have hx' : x ∈ Submodule.map (_root_.Formalism.BasicNotions.letE i • LinearMap.id) (W.N T) := hx
  obtain ⟨y, -, rfl⟩ := Submodule.mem_map.mp hx'
  change (Pi.constRingHom (ZMod n) (PowerSeries O) c : _root_.Formalism.BasicNotions.LetA O n) • ((_root_.Formalism.BasicNotions.letE i : _root_.Formalism.BasicNotions.LetA O n) • y) =
    (Pi.single i c : _root_.Formalism.BasicNotions.LetA O n) • ((_root_.Formalism.BasicNotions.letE i : _root_.Formalism.BasicNotions.LetA O n) • y)
  rw [smul_smul, smul_smul]
  congr 1
  unfold _root_.Formalism.BasicNotions.letE
  ext j : 1
  by_cases h : j = i
  · subst h
    simp
  · simp [Pi.single_apply, h]

abbrev LetterBasis (i : ZMod n) : Type := Basis (Fin (rk T)) (PowerSeries O) ↥(W.Nl T i)

def LettersDecompose : Prop := iSupIndep (W.Nl T) ∧ ⨆ i, W.Nl T i = W.N T

def LettersFree : Prop := ∀ i : ZMod n, Nonempty (LetterBasis W T i)

def GlobalBasis : Prop :=
  ∃ b : Basis (Fin (rk T)) (LetA O n) ↥(W.N T),
    LinearIndependent W.EE (fun j => (b j : W.DD T)) ∧
      Submodule.span W.EE (Set.range fun j => (b j : W.DD T)) = ⊤

variable {W T}

variable (W T)

end Generic

end GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.WachLettersFree
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def IsLetterBasis (i : ZMod n) {r : ℕ} (b : Fin r → W.DD T) : Prop :=
  (∀ k, b k ∈ W.Nl T i) ∧
    ∀ x ∈ W.Nl T i, ∃! c : Fin r → PowerSeries O,
      x = ∑ k, (Pi.single i (c k) : LetA O n) • b k

end Generic

end GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.PointRingCommRing
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PointRingCommRing

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def LiesOver (W : LocWach PD LL O v n) (τ : K →ₐ[Qp] LL) (i : ZMod n) : Prop :=
  ∀ c : K₀, τ (algebraMap K₀ K c) = W.emb i c

def JumpsOverLetters (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (M h : ZMod n → ℕ) : Prop :=
  ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), LiesOver W τ i →
    JumpsInV PD T.ρ τ (Set.Icc (-(M i : ℤ)) (h i : ℤ))

def phiPullLetter (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) :
    Submodule (LetA O n) (W.DD T) :=
  Submodule.span (LetA O n) (W.φD T '' (W.Nl T (i - 1) : Set (W.DD T)))

def InLetterAwayQ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (y : W.DD T) : Prop :=
  ∃ k : ℕ, W.Q ^ k • y ∈ W.Nl T i

def PointRing (_W : LocWach PD LL O v n) (_i : ZMod n) (_ζ : LL) : Type := PowerSeries LL

instance PointRing.commRing (W : LocWach PD LL O v n) (i : ZMod n) (ζ : LL) :
    CommRing (PointRing W i ζ) :=
  inferInstanceAs (CommRing (PowerSeries LL))

instance PointRing.algebra (W : LocWach PD LL O v n) (i : ZMod n) (ζ : LL) :
    Algebra (LetA O n) (PointRing W i ζ) :=
  RingHom.toAlgebra (R := LetA O n) (S := PointRing W i ζ) (W.lev i ζ).toRingHom

abbrev CompletedAt (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) : Type :=
  PointRing W i ζ ⊗[LetA O n] ↥(W.Nl T i)

def InCompletedAt (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL)
    (y : W.DD T) : Prop :=
  ∃ (k : ℕ) (hk : W.Q ^ k • y ∈ W.Nl T i) (w : CompletedAt W T i ζ),
    (1 : PointRing W i ζ) ⊗ₜ[LetA O n] (⟨W.Q ^ k • y, hk⟩ : ↥(W.Nl T i)) = W.Q ^ k • w

def HeightBounds (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (M h : ZMod n → ℕ) : Prop :=
  ∀ i : ZMod n,
    (∀ y ∈ phiPullLetter W T i, W.Q ^ M i • y ∈ W.Nl T i) ∧
    (∀ y ∈ W.Nl T i, W.Q ^ h i • y ∈ phiPullLetter W T i)

def RootTest (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) : Prop :=
  ∀ (i : ZMod n) (y : W.DD T), InLetterAwayQ W T i y →
    (y ∈ W.Nl T i ↔ ∀ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ W.s) → InCompletedAt W T i ζ y)

variable {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

def latticeAinf (inclR : RA →ₐ[O] RW) (T : LocLat G Qp LL O) : Submodule O (TW RW T) :=
  LinearMap.range (TWincl inclR T)

def wachAinf (E : EtTie W RA RW inclR φR gR πA) (T : LocLat G Qp LL O) : Submodule O (TW RW T) :=
  Submodule.span O {z | ∃ (a : RA) (x : W.DD T), x ∈ W.N T ∧ z = inclR a • E.jD T x}

def Sandwich (E : EtTie W RA RW inclR φR gR πA) (T : LocLat G Qp LL O) (M h : ℕ) : Prop :=
  (∀ z ∈ latticeAinf inclR T, inclR (E.io W.X) ^ h • z ∈ wachAinf E T) ∧
  (∀ z ∈ wachAinf E T, inclR (E.io W.X) ^ M • z ∈ latticeAinf inclR T)

end Generic


theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.PointRingCommRing.letters_neZero {l : ℕ} [Fact l.Prime] (K : _root_.Formalism.BasicNotions.Loc.FinExt l) :
    NeZero (Module.finrank ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K)) := by
  haveI : FiniteDimensional ℚ_[l] ↥(K : IntermediateField ℚ_[l] (_root_.Formalism.BasicNotions.Loc.Om l)) := K.2
  have hle : _root_.Formalism.BasicNotions.Loc.K0 K ≤ (K : IntermediateField ℚ_[l] (_root_.Formalism.BasicNotions.Loc.Om l)) := by
    unfold _root_.Formalism.BasicNotions.Loc.K0; exact inf_le_left
  haveI : FiniteDimensional ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K) :=
    Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  exact ⟨Module.finrank_pos.ne'⟩

def letterMax {l : ℕ} [Fact l.Prime] (K : FinExt l)
    (f : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ) : ℕ :=
  haveI := letters_neZero K
  Finset.univ.sup f

def HeightsFromJumps (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H) (_C : LocCmpT l P AI H F) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ →
    ∀ Mi hi : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ,
      JumpsOverLetters (H.W K s LL h) T Mi hi →
        HeightBounds (H.W K s LL h) T Mi hi ∧
        RootTest (H.W K s LL h) T ∧
        Sandwich (F.E K s LL h).tie T (letterMax K Mi) (letterMax K hi)

end GlobalTheory.IndefiniteRowSideFullHecke.PointRingCommRing
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DualExactSequence
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

variable {l : ℕ} [Fact l.Prime]

abbrev Lat (K LL : FinExt l) : Type 1 := LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)

abbrev Emb (K LL : FinExt l) : Type := ↥K.1 →ₐ[ℚ_[l]] ↥LL.1

def embeddingRestrictMaxUnramified {K LL : FinExt l} (τ : Emb K LL) : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1 :=
  τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)

section Objects

variable (P : LocPrime l) {K LL : FinExt l}

abbrev iota (T : Lat K LL) : T.V ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] T.V ⊗[ℚ_[l]] P.R.BdR :=
  ιV (P.PD K) (LL := ↥LL.1) (V := T.V)

abbrev filV (T : Lat K LL) (a : ℤ) : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.BdR) :=
  FilV (P.PD K) (LL := ↥LL.1) (V := T.V) a

abbrev mulK (T : Lat K LL) (c : ↥K.1) :
    T.V ⊗[ℚ_[l]] P.R.BdR →ₗ[↥LL.1] T.V ⊗[ℚ_[l]] P.R.BdR :=
  mulVdR (Qp := ℚ_[l]) (K := ↥K.1) (BdR := P.R.BdR) (LL := ↥LL.1) (V := T.V) c

def filD (T : Lat K LL) (a : ℤ) : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.BdR) :=
  DdR (P.PD K) T.ρ ⊓ filV P T a

def tdR (K : FinExt l) : P.R.BdRˣ := ((P.PD K).t_unit.map (P.PD K).ι).unit

def offComp (T : Lat K LL) (τ : Emb K LL) : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.BdR) :=
  Submodule.span ↥LL.1 {z | ∃ (c : ↥K.1), ∃ y ∈ DdR (P.PD K) T.ρ, z = mulK P T c y - τ c • y}

def mapdR {T T' : Lat K LL} (f : T.V →ₗ[↥LL.1] T'.V) :
    T.V ⊗[ℚ_[l]] P.R.BdR →ₗ[↥LL.1] T'.V ⊗[ℚ_[l]] P.R.BdR :=
  AlgebraTensorModule.map f (LinearMap.id : P.R.BdR →ₗ[ℚ_[l]] P.R.BdR)

end Objects

section Shapes

variable {K LL : FinExt l}

def IsSES {T₀ T₁ T₂ : Lat K LL} (f : T₀.V →ₗ[↥LL.1] T₁.V) (g : T₁.V →ₗ[↥LL.1] T₂.V) : Prop :=
  (∀ σ x, f (T₀.ρ σ x) = T₁.ρ σ (f x)) ∧ (∀ σ x, g (T₁.ρ σ x) = T₂.ρ σ (g x)) ∧
    Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g

def IsDualRep {T T' : Lat K LL} (β : T.V →ₗ[↥LL.1] T'.V →ₗ[↥LL.1] ↥LL.1) : Prop :=
  (∀ σ x y, β (T.ρ σ x) (T'.ρ σ y) = β x y) ∧ Function.Bijective β.flip

def IsTensorRep {T₁ T₂ T₃ : Lat K LL} (e : T₁.V ⊗[↥LL.1] T₂.V ≃ₗ[↥LL.1] T₃.V) : Prop :=
  ∀ σ x y, T₃.ρ σ (e (x ⊗ₜ[↥LL.1] y)) = e (T₁.ρ σ x ⊗ₜ[↥LL.1] T₂.ρ σ y)

def SubSES (P : LocPrime l) {T₀ T₁ T₂ : Lat K LL} (f : T₀.V →ₗ[↥LL.1] T₁.V)
    (g : T₁.V →ₗ[↥LL.1] T₂.V) (A₀ : Submodule ↥LL.1 (T₀.V ⊗[ℚ_[l]] P.R.BdR))
    (A₁ : Submodule ↥LL.1 (T₁.V ⊗[ℚ_[l]] P.R.BdR))
    (A₂ : Submodule ↥LL.1 (T₂.V ⊗[ℚ_[l]] P.R.BdR)) : Prop :=
  (∀ x ∈ A₀, mapdR P f x = 0 → x = 0) ∧
    (∀ y, (∃ x ∈ A₀, mapdR P f x = y) ↔ (y ∈ A₁ ∧ mapdR P g y = 0)) ∧
    (∀ z, (∃ y ∈ A₁, mapdR P g y = z) ↔ z ∈ A₂)

end Shapes

section At

variable (P : LocPrime l) (K LL : FinExt l)

def CrysDeRhamAt : Prop :=
  ∀ T : Lat K LL, IsCrys (P.PD K) T.ρ → IsDR (P.PD K) T.ρ

def DdRSpanAt : Prop :=
  ∀ T : Lat K LL, IsCrys (P.PD K) T.ρ →
    DdR (P.PD K) T.ρ = Submodule.span ↥LL.1
      {z | ∃ (c : ↥K.1), ∃ x ∈ Dcris (P.PD K) T.ρ, z = mulK P T c (iota P T x)}

def ComponentIsoAt : Prop :=
  ∀ T : Lat K LL, IsCrys (P.PD K) T.ρ → ∀ τ : Emb K LL,
    ∃ e : ↥(DcrisL (P.PD K) T.ρ (embeddingRestrictMaxUnramified τ)) ≃ₗ[↥LL.1] ↥(DdRE (P.PD K) T.ρ τ),
      ∀ x : ↥(DcrisL (P.PD K) T.ρ (embeddingRestrictMaxUnramified τ)), iota P T (x : T.V ⊗[ℚ_[l]] P.R.B) - (e x : T.V ⊗[ℚ_[l]] P.R.BdR) ∈ offComp P T τ

def UnramOntoAt : Prop :=
  K.1 ≤ MaximalUnramifiedExtension l → ∀ T : Lat K LL, IsCrys (P.PD K) T.ρ →
    (Dcris (P.PD K) T.ρ).map (iota P T) = DdR (P.PD K) T.ρ

def FilZeroAt : Prop :=
  ∀ T : Lat K LL, IsDR (P.PD K) T.ρ →
    filV P T 0 = Submodule.span ↥LL.1
      {z | ∃ (a : ℤ), ∃ b ∈ (P.PD K).Fil 0, ∃ d ∈ filD P T a,
        z = mulVR T (((tdR P K ^ (-a) : P.R.BdRˣ) : P.R.BdR) * b) d}

def StrictAt : Prop :=
  ∀ (T₀ T₁ T₂ : Lat K LL) (f : T₀.V →ₗ[↥LL.1] T₁.V) (g : T₁.V →ₗ[↥LL.1] T₂.V), IsSES f g →
    IsDR (P.PD K) T₀.ρ → IsDR (P.PD K) T₁.ρ → IsDR (P.PD K) T₂.ρ →
    ∀ (τ : Emb K LL) (a : ℤ), SubSES P f g
      (FildR (P.PD K) T₀.ρ τ a) (FildR (P.PD K) T₁.ρ τ a) (FildR (P.PD K) T₂.ρ τ a)

def DualJumpsAt : Prop :=
  ∀ (T T' : Lat K LL) (β : T.V →ₗ[↥LL.1] T'.V →ₗ[↥LL.1] ↥LL.1), IsDualRep β →
    IsDR (P.PD K) T.ρ →
    IsDR (P.PD K) T'.ρ ∧ ∀ (τ : Emb K LL) (a : ℤ),
      (IsJumpV (P.PD K) T'.ρ τ a ↔ IsJumpV (P.PD K) T.ρ τ (-a)) ∧
        multV (P.PD K) T'.ρ τ a = multV (P.PD K) T.ρ τ (-a)

def TensorJumpsAt : Prop :=
  ∀ (T₁ T₂ T₃ : Lat K LL) (e : T₁.V ⊗[↥LL.1] T₂.V ≃ₗ[↥LL.1] T₃.V), IsTensorRep e →
    IsDR (P.PD K) T₁.ρ → IsDR (P.PD K) T₂.ρ →
    IsDR (P.PD K) T₃.ρ ∧ ∀ (τ : Emb K LL) (c : ℤ),
      (IsJumpV (P.PD K) T₃.ρ τ c ↔
        ∃ a b : ℤ, IsJumpV (P.PD K) T₁.ρ τ a ∧ IsJumpV (P.PD K) T₂.ρ τ b ∧ a + b = c) ∧
      ∀ S : Finset ℤ, JumpsInV (P.PD K) T₁.ρ τ (S : Set ℤ) →
        multV (P.PD K) T₃.ρ τ c =
          ∑ a ∈ S, multV (P.PD K) T₁.ρ τ a * multV (P.PD K) T₂.ρ τ (c - a)

def TwistJumpsAt : Prop :=
  ∀ T T' : Lat K LL, IsTwistRep (cycLL (P.PD K) ↥LL.1) T.ρ T'.ρ → IsDR (P.PD K) T.ρ →
    IsDR (P.PD K) T'.ρ ∧ ∀ (τ : Emb K LL) (a : ℤ),
      (IsJumpV (P.PD K) T'.ρ τ (a - 1) ↔ IsJumpV (P.PD K) T.ρ τ a) ∧
        multV (P.PD K) T'.ρ τ (a - 1) = multV (P.PD K) T.ρ τ a

def PotCrysDeRhamAt : Prop :=
  ∀ (T : Lat K LL) (K' : FinExt l) (hK : K.1 ≤ K'.1),
    IsCrys (P.PD K') (T.ρ.comp (Subgroup.inclusion (GK_le hK))) → IsDR (P.PD K) T.ρ

end At

def OverGood (C : FinExt l → FinExt l → Prop) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → C K LL

section Good

variable (l) (P : LocPrime l)

def CrysDeRham : Prop := OverGood (CrysDeRhamAt P)
def DdRSpan : Prop := OverGood (DdRSpanAt P)
def ComponentIso : Prop := OverGood (ComponentIsoAt P)
def UnramOnto : Prop := OverGood (UnramOntoAt P)
def FilZero : Prop := OverGood (FilZeroAt P)
def Strict : Prop := OverGood (StrictAt P)
def DualJumps : Prop := OverGood (DualJumpsAt P)
def TensorJumps : Prop := OverGood (TensorJumpsAt P)
def TwistJumps : Prop := OverGood (TwistJumpsAt P)
def PotCrysDeRham : Prop := OverGood (PotCrysDeRhamAt P)

def DeRhamComparison : Prop :=
  CrysDeRham l P ∧ DdRSpan l P ∧ ComponentIso l P ∧ UnramOnto l P ∧ FilZero l P ∧ Strict l P ∧
    DualJumps l P ∧ TensorJumps l P ∧ TwistJumps l P ∧ PotCrysDeRham l P

end Good

end GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence
end
end
