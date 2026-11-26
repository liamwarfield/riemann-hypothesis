module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TreeParts
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free

def hypOne {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    Matrix (Fin (M + 2)) (Fin (M + 2)) K :=
  Matrix.of (Fin.cons (Fin.cons 0 (Fin.cons 1 fun _ => 0))
    (Fin.cons (Fin.cons 1 (Fin.cons 0 fun _ => 0)) fun i => Fin.cons 0 (Fin.cons 0 (A i))))

section Entries

variable {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K)

theorem hypOne_zero_zero : hypOne A 0 0 = 0 := rfl
theorem hypOne_zero_one : hypOne A 0 1 = 1 := rfl
theorem hypOne_one_zero : hypOne A 1 0 = 1 := rfl
theorem hypOne_one_one : hypOne A 1 1 = 0 := rfl
theorem hypOne_zero_rest (j : Fin M) : hypOne A 0 j.succ.succ = 0 := rfl
theorem hypOne_one_rest (j : Fin M) : hypOne A 1 j.succ.succ = 0 := rfl
theorem hypOne_rest_zero (i : Fin M) : hypOne A i.succ.succ 0 = 0 := rfl
theorem hypOne_rest_one (i : Fin M) : hypOne A i.succ.succ 1 = 0 := rfl
theorem hypOne_rest_rest (i j : Fin M) : hypOne A i.succ.succ j.succ.succ = A i j := rfl

end Entries

end GlobalTheory.CompanionTheory.WeilSiegel.Free
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramNear
noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct ENNReal Matrix

section Loc

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def gramNear (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : HermR R σ n) (U : Set (HermR R σ n)) :
    Set (Fin n → Fin M → R ⊗[F] E) :=
  {X | ∃ u ∈ U, (c : Matrix (Fin n) (Fin n) (R ⊗[F] E)) - gramR R σ J X = (u : Matrix (Fin n) (Fin n) (R ⊗[F] E))}

def gramTest (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : HermR R σ n) (ρ : HermR R σ n → ℝ)
    (X : Fin n → Fin M → R ⊗[F] E) : ℝ := by
  classical
  exact if h : (c : Matrix (Fin n) (Fin n) (R ⊗[F] E)) - gramR R σ J X ∈ HermR R σ n then ρ ⟨_, h⟩ else 0

end Loc

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def boxF {M n : ℕ} (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)) :
    Set (Fin n → Fin M → Af F ⊗[F] E) :=
  {X | ∀ v, projV v X ∈ A v}

def pureN {M n : ℕ} (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (X : Fin n → Fin M → AF F ⊗[F] E) : ℂ :=
  φ (projInf X) * (boxF A).indicator (fun _ => (1 : ℂ)) (projFin X)

def intH (σ : E →ₐ[F] E) {d n : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Set (HermR (AF F) σ n) :=
  {B | ∀ v, v ∉ S → projV v (projFin (fun a i => (B : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a i)) ∈ latV (M := n) (n := n) b v}

def coefS (σ : E →ₐ[F] E) {d M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (T : Matrix (Fin n) (Fin n) E)
    (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) : ℂ :=
  ∫ B, (intH σ b S).indicator (fun _ => (1 : ℂ)) B *
    (GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ B * ψ (-(algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace (T.map (inclR (AF F)) * (B : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))))))) ∂db

end Adelic

end GlobalTheory.CompanionTheory.WhitFree
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

noncomputable def Red : {N : ℕ} → Tr E N → Prop
  | _, .leaf _ _ => True
  | _, @Tr.node _ _ _ _ r s t₁ t₂ => 0 < r ∧ 0 < s ∧ Red t₁ ∧ Red t₂

inductive Conv : {N : ℕ} → (ℕ → Tr E N) → Tr E N → Prop
  | leaf {N : ℕ} (V : Submodule ℂ (Sm E N)) (z : ℕ → ℂ) (z₀ : ℂ) (h : Tendsto z atTop (𝓝 z₀)) :
      Conv (fun k => .leaf V (z k)) (.leaf V z₀)
  | node {r s : ℕ} {t₁ : ℕ → Tr E r} {t₂ : ℕ → Tr E s} {s₁ : Tr E r} {s₂ : Tr E s} (h₁ : Conv t₁ s₁) (h₂ : Conv t₂ s₂) :
      Conv (fun k => .node (t₁ k) (t₂ k)) (.node s₁ s₂)

noncomputable def LeafZ (P : ∀ M : ℕ, Submodule ℂ (Sm E M) → ℂ → Prop) : {N : ℕ} → Tr E N → Prop
  | M, .leaf V z => P M V z
  | _, .node t₁ t₂ => LeafZ P t₁ ∧ LeafZ P t₂

variable {a b : ℕ}

def sl₁ (F : H E a b → ℂ) (m₂ : GA E b) : Sm E a :=
  open Classical in if h : ∃ φ : Sm E a, φ.1 = fun x => F (x, m₂) then h.choose else 0

def sl₂ (F : H E a b → ℂ) (m₁ : GA E a) : Sm E b :=
  open Classical in if h : ∃ φ : Sm E b, φ.1 = fun x => F (m₁, x) then h.choose else 0

def ap₁ (A : Sm E a →ₗ[ℂ] Sm E a) (F : H E a b → ℂ) : H E a b → ℂ := fun x => (A (sl₁ F x.2)).1 x.1

def ap₂ (B : Sm E b →ₗ[ℂ] Sm E b) (F : H E a b → ℂ) : H E a b → ℂ := fun x => (B (sl₂ F x.1)).1 x.2

theorem good_disc : ∀ {N : ℕ} {t : Tr E N}, t.Good → t.Disc := by
  intro N t
  induction t with
  | leaf V z =>
    intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.1, h.2.1⟩
  | node t₁ t₂ i₁ i₂ => exact fun h => ⟨i₁ h.1, i₂ h.2⟩

theorem disc_stable : ∀ {N : ℕ} {t : Tr E N}, t.Disc → t.AllLeaves fun _ V => _root_.GlobalTheory.CuspRep.IsStable V := by
  intro N t
  induction t with
  | leaf V z =>
    intro h
    rcases h with ⟨-, rfl, -⟩ | h
    · exact fun _ _ _ => trivial
    · exact h.2.stable
  | node t₁ t₂ i₁ i₂ => exact fun h => ⟨i₁ h.1, i₂ h.2⟩

theorem rank_pos_of_leaves {Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} : ∀ {N : ℕ} {t : Tr E N},
    t.AllLeaves (fun M V => 0 < M ∧ Q M V) → 0 < N := by
  intro N t
  induction t with
  | leaf V z => exact fun h => h.1
  | node t₁ t₂ i₁ i₂ => exact fun h => Nat.add_pos_left (i₁ h.1) _

theorem red_of_leaves {Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} : ∀ {N : ℕ} {t : Tr E N},
    t.AllLeaves (fun M V => 0 < M ∧ Q M V) → Red t := by
  intro N t
  induction t with
  | leaf V z => exact fun _ => trivial
  | node t₁ t₂ i₁ i₂ => exact fun h => ⟨rank_pos_of_leaves h.1, rank_pos_of_leaves h.2, i₁ h.1, i₂ h.2⟩

section Props

def ListLeaf (Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) :
    ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop :=
  fun M V => M = 0 ∨ ∃ K' ∈ Θ M, ∃ W' ∈ Ω M, HasType K' W' V

def CapEig {N : ℕ} (ψ : Sm E N) (m : (E →+* ℂ) → Multiset ℂ) : Prop :=
  ∀ τ u, cap τ u ψ = ((m τ).map (u + ·)).prod • ψ

def FinGen {N : ℕ} (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) (U : Submodule ℂ (Sm E N)) : Prop :=
  ∃ S : Finset (Sm E N), (∀ φ ∈ S, TypeB K W φ) ∧ ↑S ⊆ (U : Set (Sm E N)) ∧
    ∀ U' : Submodule ℂ (Sm E N), _root_.GlobalTheory.CuspRep.IsStable U' → ↑S ⊆ (U' : Set (Sm E N)) → U ≤ U'

def Fac {N : ℕ} (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ))
    (Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) : Prop :=
  ∀ U : Submodule ℂ (Sm E N), _root_.GlobalTheory.CuspRep.IsStable U → (∀ φ ∈ U, IsAutForm φ) → FinGen K W U → NonPos U → CentIm U →
    (∀ τ : E →+* ℂ, ∃ m, HasInfCharGL U τ m ∧ m.Nodup) → U ≠ ⊥ →
    ∃ (t : Tr E N) (T : Sm E N →ₗ[ℂ] Sm E N), Red t ∧ t.Good ∧ t.AllLeaves (ListLeaf Θ Ω) ∧
      (∀ o, ∀ ψ ∈ U, T (act o ψ) = act o (T ψ)) ∧ (∀ ψ ∈ U, T ψ ∈ t.space) ∧ ∃ ψ ∈ U, T ψ ≠ 0

def ReproAll (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (ν : Measure (GA E N)) [ν.IsHaarMeasure]
    (K' : Subgroup (GL (Fin N) (Af E))) (W' : Submodule ℂ (Kinf E N → ℂ)) (R' : ℝ),
    IsOpen (K' : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W' → Repro ν K' W' R'

def LimLeafP (N : ℕ) (Θs : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ωs : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)))
    (Θf : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ωf : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) : Prop :=
  ∀ M, 0 < M → M ≤ N → ∀ (V : ℕ → Submodule ℂ (Sm E M)) (z : ℕ → ℂ) (R : ℝ), ReproAll E →
    (∀ k, IsDiscrete (V k)) → (∀ k, (z k).re = 0) → (∀ k, ∃ K' ∈ Θs M, ∃ W' ∈ Ωs M, HasType K' W' (V k)) →
    (∀ k, InfBdd R (V k)) → (∀ k, ‖z k‖ ≤ R) →
    ∃ (φ : ℕ → ℕ) (t : ℕ → Tr E M) (s : Tr E M), StrictMono φ ∧ Conv t s ∧ Red s ∧ s.Good ∧
      s.AllLeaves (ListLeaf Θf Ωf) ∧ (∀ k, (t k).Disc) ∧ ∀ k, Emb (tw (V (φ k)) (z (φ k))) (· ∈ (t k).space)

end Props

def PairSlices : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (F : H E a b → ℂ), F ∈ pairSpace U₁ U₂ →
  (∀ m₂, sl₁ F m₂ ∈ U₁ ∧ (sl₁ F m₂).1 = fun x => F (x, m₂)) ∧
  (∀ m₁, sl₂ F m₁ ∈ U₂ ∧ (sl₂ F m₁).1 = fun x => F (m₁, x))

def PairRestrict : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  (U₁ : Submodule ℂ (Sm E a)) (U₂ U₂' : Submodule ℂ (Sm E b)) (F : H E a b → ℂ), F ∈ pairSpace U₁ U₂ →
  (∀ m₁ (φ : Sm E b), (φ.1 = fun x => F (m₁, x)) → φ ∈ U₂') → F ∈ pairSpace U₁ U₂'

def PairFD : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (ι : Type) [Fintype ι]
  (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (f : ι → H E a b → ℂ), (∀ i, f i ∈ pairSpace U₁ U₂) →
  FiniteDimensional ℂ (Submodule.span ℂ (slices₁ f)) ∧ FiniteDimensional ℂ (Submodule.span ℂ (slices₂ f))

def SliceType : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
  (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)) (F : H E a b → ℂ), TypeH K₁ K₂ W₁ W₂ F →
  (∀ (φ : Sm E a) m₂, (φ.1 = fun x => F (x, m₂)) → TypeB K₁ W₁ φ) ∧
  (∀ (φ : Sm E b) m₁, (φ.1 = fun x => F (m₁, x)) → TypeB K₂ W₂ φ)

def PairStep₁ : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (ι : Type) [Fintype ι]
  (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
  (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ))
  (U₁ U₁' : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (T : Sm E a →ₗ[ℂ] Sm E a) (f : ι → H E a b → ℂ),
  FiniteDimensional ℂ W₁ → FiniteDimensional ℂ W₂ → _root_.GlobalTheory.CuspRep.IsStable U₁ → (∀ o, ∀ ψ ∈ U₁, T (act o ψ) = act o (T ψ)) →
  (∀ ψ ∈ U₁, T ψ ∈ U₁') → (∀ i, f i ∈ pairSpace U₁ U₂) → (∀ i, TypeH K₁ K₂ W₁ W₂ (f i)) →
  (∃ i m₂, ∃ φ : Sm E a, (φ.1 = fun x => f i (x, m₂)) ∧ T φ ≠ 0) →
  (fun i => ap₁ T (f i)) ≠ 0 ∧ (∀ i, ap₁ T (f i) ∈ pairSpace U₁' U₂) ∧ (∀ i, TypeH K₁ K₂ W₁ W₂ (ap₁ T (f i))) ∧
    ∀ (h : HeckeM E a b ι) (c : ℂ), heckeAct h f = c • f → heckeAct h (fun i => ap₁ T (f i)) = c • fun i => ap₁ T (f i)

def PairStep₂ : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (ι : Type) [Fintype ι]
  (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
  (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ))
  (U₁ : Submodule ℂ (Sm E a)) (U₂ U₂' : Submodule ℂ (Sm E b)) (T : Sm E b →ₗ[ℂ] Sm E b) (f : ι → H E a b → ℂ),
  FiniteDimensional ℂ W₁ → FiniteDimensional ℂ W₂ → _root_.GlobalTheory.CuspRep.IsStable U₂ → (∀ o, ∀ ψ ∈ U₂, T (act o ψ) = act o (T ψ)) →
  (∀ ψ ∈ U₂, T ψ ∈ U₂') → (∀ i, f i ∈ pairSpace U₁ U₂) → (∀ i, TypeH K₁ K₂ W₁ W₂ (f i)) →
  (∃ i m₁, ∃ φ : Sm E b, (φ.1 = fun x => f i (m₁, x)) ∧ T φ ≠ 0) →
  (fun i => ap₂ T (f i)) ≠ 0 ∧ (∀ i, ap₂ T (f i) ∈ pairSpace U₁ U₂') ∧ (∀ i, TypeH K₁ K₂ W₁ W₂ (ap₂ T (f i))) ∧
    ∀ (h : HeckeM E a b ι) (c : ℂ), heckeAct h f = c • f → heckeAct h (fun i => ap₂ T (f i)) = c • fun i => ap₂ T (f i)

def PairEmb : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (ι : Type) [Fintype ι]
  (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
  (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ))
  (X₁ Y₁ : Submodule ℂ (Sm E a)) (X₂ Y₂ : Submodule ℂ (Sm E b)) (G : ι → H E a b → ℂ),
  FiniteDimensional ℂ W₁ → FiniteDimensional ℂ W₂ → _root_.GlobalTheory.CuspRep.IsStable X₁ → _root_.GlobalTheory.CuspRep.IsStable X₂ → Emb X₁ (· ∈ Y₁) → Emb X₂ (· ∈ Y₂) →
  G ≠ 0 → (∀ i, G i ∈ pairSpace X₁ X₂) → (∀ i, TypeH K₁ K₂ W₁ W₂ (G i)) →
  ∃ G' : ι → H E a b → ℂ, G' ≠ 0 ∧ (∀ i, G' i ∈ pairSpace Y₁ Y₂) ∧ (∀ i, TypeH K₁ K₂ W₁ W₂ (G' i)) ∧
    ∀ (h : HeckeM E a b ι) (c : ℂ), heckeAct h G = c • G → heckeAct h G' = c • G'

def HullGen : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
  (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) (S : Set (Sm E N)),
  (∀ φ ∈ S, TypeB K W φ) → FiniteDimensional ℂ (Submodule.span ℂ S) → _root_.GlobalTheory.CuspRep.IsStable (hull S) ∧ FinGen K W (hull S)

def CapEquiv : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (U : Submodule ℂ (Sm E N))
  (T : Sm E N →ₗ[ℂ] Sm E N) (ψ : Sm E N) (m : (E →+* ℂ) → Multiset ℂ), _root_.GlobalTheory.CuspRep.IsStable U →
  (∀ o, ∀ χ ∈ U, T (act o χ) = act o (T χ)) → ψ ∈ U → CapEig ψ m → CapEig (T ψ) m

def DiscInf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (M : ℕ) (V : Submodule ℂ (Sm E M)),
  IsDiscrete V → ∀ τ : E →+* ℂ, ∃ m, HasInfCharGL V τ m

def TopInf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (τ : E →+* ℂ),
  HasInfCharGL (⊤ : Submodule ℂ (Sm E 0)) τ 0

def InfOfEq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : Tr E N) (ψ : Sm E N)
  (m : (E →+* ℂ) → Multiset ℂ) (τ : E →+* ℂ) (m' : Multiset ℂ), InfTree → t.InfOf τ m' → ψ ∈ t.space → ψ ≠ 0 → CapEig ψ m →
  m' = m τ

def LeafBound : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : Tr E N) (ψ : Sm E N)
  (m : (E →+* ℂ) → Multiset ℂ) (B : ℝ), InfTree → t.Good → ψ ∈ t.space → ψ ≠ 0 → CapEig ψ m →
  (∀ τ, ∀ x ∈ m τ, ‖x‖ ≤ B) → LeafZ (fun M V z => 0 < M → InfBdd (2 * B) V ∧ ‖z‖ ≤ 2 * B) t

def ConvStrip : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : ℕ → Tr E N) (s : Tr E N),
  Conv t s ↔ (∀ k, (t k).strip = s.strip) ∧
    ∀ i, Tendsto (fun k => ((t k).twists.getD i 0)) atTop (𝓝 (s.twists.getD i 0))

def ConvShift : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : ℕ → Tr E N) (s : Tr E N)
  (z : ℕ → ℂ) (z₀ : ℂ), Conv t s → Tendsto z atTop (𝓝 z₀) → Conv (fun k => (t k).shift (z k)) (s.shift z₀)

def ConvComp : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : ℕ → Tr E N) (s : Tr E N)
  (φ : ℕ → ℕ), Conv t s → StrictMono φ → Conv (fun k => t (φ k)) s

def ConvInf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : ℕ → Tr E N) (s : Tr E N)
  (τ : E →+* ℂ), Conv t s → s.Good → ∃ (m₀ : Multiset ℂ) (m : ℕ → Multiset ℂ), s.InfOf τ m₀ ∧ (∀ k, (t k).InfOf τ (m k)) ∧
    ∀ u, Tendsto (fun k => ((m k).map (u + ·)).prod) atTop (𝓝 ((m₀.map (u + ·)).prod))

def FactorStep : Prop := Sep4 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
  (W : Submodule ℂ (Kinf E N → ℂ)), FiniteDimensional ℂ W →
  ∃ Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)), KTypes E Ω ∧
  ∀ K : Subgroup (GL (Fin N) (Af E)), IsOpen (K : Set (GL (Fin N) (Af E))) →
  ∃ Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))), Levels E Θ ∧ Fac K W Θ Ω

def OneStep : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (ι : Type) [Fintype ι]
  (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
  (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ))
  (Θ₁ Θ₂ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ω₁ Ω₂ : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)))
  (f : ι → H E a b → ℂ) (m₁ m₂ : (E →+* ℂ) → Multiset ℂ),
  FiniteDimensional ℂ W₁ → FiniteDimensional ℂ W₂ → Fac K₁ W₁ Θ₁ Ω₁ → Fac K₂ W₂ Θ₂ Ω₂ → f ≠ 0 →
  (∀ i, TypeH K₁ K₂ W₁ W₂ (f i)) →
  (∀ i (m₂ : GA E b), ∃ φ : Sm E a, φ.1 = fun x => f i (x, m₂)) →
  (∀ i (m₁ : GA E a), ∃ φ : Sm E b, φ.1 = fun x => f i (m₁, x)) →
  (∀ φ ∈ hull (slices₁ f), IsAutForm φ) → (∀ φ ∈ hull (slices₂ f), IsAutForm φ) →
  NonPos (hull (slices₁ f)) → NonPos (hull (slices₂ f)) → CentIm (hull (slices₁ f)) → CentIm (hull (slices₂ f)) →
  (∀ τ, HasInfCharGL (hull (slices₁ f)) τ (m₁ τ)) → (∀ τ, HasInfCharGL (hull (slices₂ f)) τ (m₂ τ)) →
  (∀ τ, (m₁ τ).Nodup) → (∀ τ, (m₂ τ).Nodup) → (∀ i, f i ∈ pairSpace (hull (slices₁ f)) (hull (slices₂ f))) →
  ∃ (t₁ : Tr E a) (t₂ : Tr E b) (G : ι → H E a b → ℂ) (ψ₁ : Sm E a) (ψ₂ : Sm E b),
    Red t₁ ∧ Red t₂ ∧ t₁.Good ∧ t₂.Good ∧ t₁.AllLeaves (ListLeaf Θ₁ Ω₁) ∧ t₂.AllLeaves (ListLeaf Θ₂ Ω₂) ∧
    G ≠ 0 ∧ (∀ i, G i ∈ pairSpace t₁.space t₂.space) ∧ (∀ i, TypeH K₁ K₂ W₁ W₂ (G i)) ∧
    (∀ (h : HeckeM E a b ι) (c : ℂ), heckeAct h f = c • f → heckeAct h G = c • G) ∧
    ψ₁ ∈ t₁.space ∧ ψ₁ ≠ 0 ∧ CapEig ψ₁ m₁ ∧ ψ₂ ∈ t₂.space ∧ ψ₂ ≠ 0 ∧ CapEig ψ₂ m₂

def LimLists : Prop := Lim5 → TwShift → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
  (Ωs : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))), KTypes E Ωs →
  ∃ Ωf : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)), KTypes E Ωf ∧
  ∀ Θs : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))), Levels E Θs →
  ∃ Θf : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))), Levels E Θf ∧ LimLeafP N Θs Ωs Θf Ωf

def LimTrees : Prop := TrStable → Graft → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
  (Θs Θf : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ωs Ωf : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) (N : ℕ),
  LimLeafP N Θs Ωs Θf Ωf → ReproAll E → ∀ (n : ℕ), n ≤ N → ∀ (t : ℕ → Tr E n) (R : ℝ), (∀ k, Red (t k)) → (∀ k, (t k).Good) →
  (∀ k, (t k).AllLeaves (ListLeaf Θs Ωs)) → (∀ k, LeafZ (fun M V z => 0 < M → InfBdd R V ∧ ‖z‖ ≤ R) (t k)) →
  ∃ (φ : ℕ → ℕ) (t' : ℕ → Tr E n) (s : Tr E n), StrictMono φ ∧ Conv t' s ∧ Red s ∧ s.Good ∧
    s.AllLeaves (ListLeaf Θf Ωf) ∧ (∀ k, (t' k).Disc) ∧ ∀ k, Emb (t (φ k)).space (· ∈ (t' k).space)

def MCloseFacts : Prop := (∀ (ε : ℝ) (m n : Multiset ℂ) (B : ℝ), MClose ε m n → (∀ y ∈ n, ‖y‖ ≤ B) → ∀ x ∈ m, ‖x‖ ≤ B + ε) ∧
  (∀ (ε : ℝ) (m n : Multiset ℂ), ε < 1 / 4 → MClose ε m n → GapM n → m.Nodup) ∧
  ∀ (m : ℕ → Multiset ℂ) (n : Multiset ℂ), (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, MClose ε (m k) n) →
    ∀ u : ℂ, Tendsto (fun k => ((m k).map (u + ·)).prod) atTop (𝓝 ((n.map (u + ·)).prod))

def FactorLim : Prop := TrStable → Graft → InfTree → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
  (Θs Θf : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ωs Ωf : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) (N : ℕ)
  (t : ℕ → Tr E N) (ψ : ℕ → Sm E N) (m : ℕ → (E →+* ℂ) → Multiset ℂ) (n : (E →+* ℂ) → Multiset ℂ) (B : ℝ),
  LimLeafP N Θs Ωs Θf Ωf → ReproAll E → (∀ k, Red (t k)) → (∀ k, (t k).Good) →
  (∀ k, (t k).AllLeaves (ListLeaf Θs Ωs)) → (∀ k, ψ k ∈ (t k).space) → (∀ k, ψ k ≠ 0) → (∀ k, CapEig (ψ k) (m k)) →
  (∀ k τ, ∀ x ∈ m k τ, ‖x‖ ≤ B) → (∀ τ (ε : ℝ), 0 < ε → ∀ᶠ k in atTop, MClose ε (m k τ) (n τ)) →
  ∃ (φ : ℕ → ℕ) (t' : ℕ → Tr E N) (s : Tr E N), StrictMono φ ∧ Conv t' s ∧ Red s ∧ s.Good ∧ s.AllLeaves (ListLeaf Θf Ωf) ∧
    (∀ k, (t' k).Disc) ∧ (∀ τ, HasInfCharGL s.space τ (n τ)) ∧ ∀ k, Emb (t (φ k)).space (· ∈ (t' k).space)

end GlobalTheory.CompanionTheory.EGlue

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix TensorProduct

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def hermE (σ : E →ₐ[F] E) (n : ℕ) : Submodule F (Matrix (Fin n) (Fin n) E) where
  carrier := {c | ∀ a b, σ (c b a) = c a b}
  add_mem' := by
    intro c d hc hd a b
    simp [map_add (f := _), hc a b, hd a b]
  zero_mem' := by
    intro a b
    simp
  smul_mem' := by
    intro t c hc a b
    simp [hc a b]

def hermIn (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (n : ℕ) :
    hermE σ n →+ HermR R σ n where
  toFun c := hermOf R σ c.1 c.2
  map_zero' := by
    apply Subtype.ext
    ext a b
    simp [hermOf]
  map_add' := by
    intro c d
    apply Subtype.ext
    ext a b
    simp [hermOf]

variable [NumberField E]

def hermO (σ : E →ₐ[F] E) (n : ℕ) : AddSubgroup (hermE σ n) where
  carrier := {c | ∀ a b, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = c.1 a b}
  add_mem' := by
    intro c d hc hd a b
    obtain ⟨o, ho⟩ := hc a b
    obtain ⟨p, hp⟩ := hd a b
    exact ⟨o + p, by simp [ho, hp]⟩
  zero_mem' := fun a b => ⟨0, by simp⟩
  neg_mem' := by
    intro c hc a b
    obtain ⟨o, ho⟩ := hc a b
    exact ⟨-o, by simp [ho]⟩

def Kc {n : ℕ} (c : Matrix (Fin n) (Fin n) E) : AddSubgroup (Fin n → 𝓞 E) where
  carrier := {y | ∀ i, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = (c *ᵥ fun j => algebraMap (𝓞 E) E (y j)) i}
  add_mem' := by
    intro y z hy hz i
    obtain ⟨o, ho⟩ := hy i
    obtain ⟨p, hp⟩ := hz i
    refine ⟨o + p, ?_⟩
    have : (fun j => algebraMap (𝓞 E) E ((y + z) j)) =
        (fun j => algebraMap (𝓞 E) E (y j)) + fun j => algebraMap (𝓞 E) E (z j) := by
      funext j
      simp
    rw [this, Matrix.mulVec_add, Pi.add_apply, ← ho, ← hp, map_add (f := _)]
  zero_mem' := fun i => ⟨0, by
    have h0 : (fun _ : Fin n => (0 : E)) = 0 := rfl
    simp [h0, Matrix.mulVec_zero]⟩
  neg_mem' := by
    intro y hy i
    obtain ⟨o, ho⟩ := hy i
    refine ⟨-o, ?_⟩
    have : (fun j => algebraMap (𝓞 E) E ((-y) j)) = -fun j => algebraMap (𝓞 E) E (y j) := by
      funext j
      simp
    rw [this, Matrix.mulVec_neg, Pi.neg_apply, ← ho, map_neg]

def delta {n : ℕ} (c : Matrix (Fin n) (Fin n) E) : ℕ := (Kc c).index

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureData
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageF

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.WeilSiegel.Frame NumberField MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def BsetF (σ : E →ₐ[F] E) {n : ℕ} (B₀ : Set R) : Set (HermR R σ (n + 1)) :=
  {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀}

end Alg

section Meas

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : F) {n : ℕ}
  {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
  (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E))
  (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
  (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J))
  (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0)

def fibSF (S : HermR R σ (n + 1)) : Measure (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) :=
  (BsetF R σ B₀).indicator (fun S : HermR R σ (n + 1) =>
    (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) *
        cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) ^ n) •
      ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))).map (fun p =>
        actW R σ (blockOne (algebraMap F E t) J) (s p.1)
          (vec (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E))
            (cvec R t a S) p.2))) S

def UsetF (B₀ : Set R) : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) :=
  gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' BsetF R σ B₀) ∩
    {X | LinearIndependent (R ⊗[F] E) X}

def MidF {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x in B₀, (κ₁ (a x) : ℝ≥0∞) * ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S',
    Pint σ J t m₁ m' s φ ((a x : Rˣ) : R) c S' ∂(coordHerm R σ b lam n)
    ∂(Measure.pi fun _ => coordK R b lam) ∂lam

end Meas

section Data

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

structure HermitianMeasureData (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ)
    {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E))
    (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J))
    (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0) : Prop where
  hCM : IsCMExt F E σ
  hJ : IsHermND σ J
  ht : t ≠ 0
  hR : IsLocR R
  hlam : lam.IsAddHaarMeasure
  hm₁ : IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁
  hm' : IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m'
  hs : Measurable s
  hsec : ∀ y, gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) →
    actW R σ _ (s y) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) = y
  hcpt : ∀ C : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E), IsCompact C →
    ∃ C' : Set (HA R σ (blockOne (algebraMap F E t) J)), IsCompact C' ∧ ∀ y ∈ C,
      gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → s y ∈ C'
  hB₀ : IsOpen B₀
  htB : algebraMap F R t ∈ B₀
  hac : ContinuousOn a B₀
  hoff : ∀ x, x ∉ B₀ → a x = 1
  hsq : ∀ x ∈ B₀, x = ((a x : Rˣ) : R) ^ 2 * algebraMap F R t
  ha1 : a (algebraMap F R t) = 1
  hκc : Continuous κ₁
  hκ1 : κ₁ 1 = 1
  hscale : ∀ u : Rˣ, m₁ (hermScal R σ ((u : R) ^ 2 * algebraMap F R t)) =
    κ₁ u • (m₁ (hermScal R σ (algebraMap F R t))).map (scl ((u : R) ⊗ₜ[F] (1 : E)))
  hcmc : Continuous cm
  hmod : ∀ u : Rˣ, (coordK R b lam).map (fun y => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y) = cm u • coordK R b lam

end Data

end GlobalTheory.CompanionTheory.SW.StageF
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
noncomputable section

open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocalHypotheses

section Generic

variable {G : Type} [Group G] [TopologicalSpace G]

def LocConds (θ : G →* G) (K : Subgroup G) (d : G) (f : G → ℂ) : Prop :=
  (∀ x ∈ twCent θ d, ∀ y ∈ twCent θ d, x * y = y * x) ∧
  (∀ y : G, (rStab fun k : K => f ((y * k)⁻¹ * d * θ (y * k))).index ≠ 0) ∧
  {q : DoubleCoset.Quotient (twCent θ d : Set G) (K : Set G) |
    ∃ k ∈ K, f ((Quotient.out q * k)⁻¹ * d * θ (Quotient.out q * k)) ≠ 0}.Finite ∧
  (∀ y : G, twCent θ d ⊓ K.map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent θ d) ∧
    (twCent θ d ⊓ K.map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent θ d)) ≠ 0)

def UnitConds (θ : G →* G) (K : Subgroup G) (d : G) (f : G → ℂ) : Prop :=
  f = (K : Set G).indicator 1 ∧ d ∈ K ∧ cptPart (twCent θ d) ≤ K ∧
    ∀ y, y⁻¹ * d * θ y ∈ K → ∃ t ∈ twCent θ d, ∃ k ∈ K, y = t * k

end Generic

section Split

variable {H : Type} [Group H]

def swTw (σ : H →* H) : H × H →* H × H :=
  (MonoidHom.prodMap σ σ).comp (MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom

theorem mem_twCent_swTw (σ : H →* H) (hσ : ∀ g, σ (σ g) = g) (d d' : H) (g : H × H) :
    g ∈ twCent (swTw σ) (d, d') ↔
      g.1 ∈ twCent (MonoidHom.id H) (d * σ d') ∧ g.2 = d' * σ g.1 * d'⁻¹ := by
  obtain ⟨g₁, g₂⟩ := g
  show (g₁, g₂) * (d, d') = (d, d') * (σ g₂, σ g₁) ↔ g₁ * (d * σ d') = d * σ d' * g₁ ∧ g₂ = d' * σ g₁ * d'⁻¹
  simp only [Prod.mk_mul_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨h₁, h₂⟩
    have e : g₂ = d' * σ g₁ * d'⁻¹ := by rw [← h₂]; group
    refine ⟨?_, e⟩
    rw [← mul_assoc, h₁, e]
    simp only [map_mul, map_inv, hσ]
    group
  · rintro ⟨h₁, rfl⟩
    refine ⟨?_, by group⟩
    simp only [map_mul, map_inv, hσ]
    have : g₁ * d = d * σ d' * g₁ * (σ d')⁻¹ := by
      rw [← h₁]; group
    rw [this]; group

end Split

section Place

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep PositivityTheory.Rg.BcB.G8

variable {E : Type} [Field E] [NumberField E]

def sgP (a b : ℕ) (w : Pl E) : GLw a w × GLw b w →* GLw a w × GLw b w :=
  (thetaGL a (RingHom.id _)).prodMap (thetaGL b (RingHom.id _))

def ratW (n : ℕ) (w : Pl E) : GL (Fin n) E →* GLw n w := GeneralLinearGroup.map (algebraMap E (w.adicCompletion E))

end Place

end GlobalTheory.CompanionTheory.LocalHypotheses

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRightHaarMeasure
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRightHaarMeasure
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.AdelicHaar

theorem exists_haar_rightInvariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ μ : Measure (GA E a), μ.IsHaarMeasure ∧ μ.IsMulRightInvariant :=
  fun E _ _ _ a => ⟨Measure.haar, inferInstance, GlobalTheory.CovolGL.isMulRightInvariant E a Measure.haar⟩

end GlobalTheory.CompanionTheory.AdelicHaar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRightHaarMeasureStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_right_haar_measure : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ μ : Measure (GA E a), μ.IsHaarMeasure ∧ μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.CompanionTheory.AdelicHaar.exists_haar_rightInvariant | exact GlobalTheory.CompanionTheory.AdelicHaar.exists_haar_rightInvariant | (intros; apply GlobalTheory.CompanionTheory.AdelicHaar.exists_haar_rightInvariant <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteRestrictionVanishing
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteRestrictionVanishing
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.EulerV

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem finite_above (v : PlF E) : Finite (Above v) := by
  by_cases h : Nonempty (Above v)
  · obtain ⟨u⟩ := h
    refine Finite.of_injective (β := (GlobalTheory.EulerTw.orb E u.1 : Finset (Pl E)))
      (fun w => ⟨w.1, (GlobalTheory.EulerTwRestr.mem_orb_iff u.1 w.1).2 (w.2.trans u.2.symm)⟩) ?_
    intro x y hxy
    exact Subtype.ext (congrArg (fun z => z.1) hxy)
  · haveI := not_nonempty_iff.1 h
    infer_instance

def pn (n : ℕ) (v : PlF E) : GL (Fin n) (Af E) →* GL (Fin n) (Av v) := GeneralLinearGroup.map (projv v)

def ev {v : PlF E} (w : Above v) : GL (Fin n) (Av v) →* GLw n w.1 :=
  GeneralLinearGroup.map (Pi.evalRingHom (fun w : Above v => w.1.adicCompletion E) w)

def Kn (n : ℕ) (v : PlF E) : Subgroup (GL (Fin n) (Av v)) :=
  ⨅ w : Above v, (GlobalTheory.LFun.KGL w.1 (n := n)).comap (ev w)

theorem mem_Kn {v : PlF E} {y : GL (Fin n) (Av v)} : y ∈ Kn n v ↔ ∀ w : Above v, ev w y ∈ GlobalTheory.LFun.KGL w.1 (n := n) := by
  simp only [Kn, Subgroup.mem_iInf, Subgroup.mem_comap]

theorem ev_pn {v : PlF E} (w : Above v) (g : GL (Fin n) (Af E)) :
    ev w (pn n v g) = GeneralLinearGroup.map (pLoc E w.1) g := rfl

theorem mem_Kv {a b : ℕ} {v : PlF E} {y : Yv a b v} : y ∈ Kv a b v ↔ y.1 ∈ Kn a v ∧ y.2 ∈ Kn b v := by
  simp only [Kv, Subgroup.mem_iInf, Subgroup.mem_comap, mem_Kn, Subgroup.mem_prod, forall_and]
  rfl

theorem mem_Kf_iff {g : GL (Fin n) (Af E)} : g ∈ Kf E n ↔ ∀ v : PlF E, pn n v g ∈ Kn n v := by
  have h : g ∈ Kf E n ↔ ∀ w : Pl E, GeneralLinearGroup.map (pLoc E w) g ∈ GlobalTheory.LFun.KGL w (n := n) := by
    simp only [Kf, Subgroup.mem_iInf, Subgroup.mem_comap]
  rw [h]
  refine ⟨fun H v => mem_Kn.2 fun w => H w.1, fun H w => ?_⟩
  exact mem_Kn.1 (H (w.under (𝓞 (maximalRealSubfield E)))) ⟨w, rfl⟩

theorem continuous_projv (v : PlF E) : Continuous (projv v) :=
  continuous_pi fun w => RestrictedProduct.continuous_eval w.1

theorem continuous_pn (v : PlF E) : Continuous (pn n v) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id (continuous_projv v))

theorem continuous_ev {v : PlF E} (w : Above v) : Continuous (ev (n := n) w) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id (continuous_apply w))

theorem isOpen_Kn (v : PlF E) : IsOpen (Kn n v : Set (GL (Fin n) (Av v))) := by
  haveI := finite_above v
  rw [Kn, Subgroup.coe_iInf]
  exact isOpen_iInter_of_finite fun w =>
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w.1 n).1.preimage (continuous_ev w)

theorem pn_ext {g h : GL (Fin n) (Af E)} (H : ∀ v : PlF E, pn n v g = pn n v h) : g = h :=
  GlobalTheory.EulerTwRestr.gl_ext fun w => by
    exact congrArg (ev ⟨w, rfl⟩) (H (w.under (𝓞 (maximalRealSubfield E))))

theorem eventually_mem_Kn (g : GL (Fin n) (Af E)) : ∀ᶠ v : PlF E in cofinite, pn n v g ∈ Kn n v := by
  have h1 : ∀ᶠ w : Pl E in cofinite, ∀ i j, pLoc E w (g.1 i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => (g.1 i j).2
  have h2 : ∀ᶠ w : Pl E in cofinite, ∀ i j, pLoc E w ((g⁻¹).1 i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => ((g⁻¹).1 i j).2
  have hx : ∀ᶠ w : Pl E in cofinite, GeneralLinearGroup.map (pLoc E w) g ∈ GlobalTheory.LFun.KGL w (n := n) := by
    filter_upwards [h1, h2] with w h1 h2
    exact GlobalTheory.EulerTwRestr.mem_KGL_iff.2 ⟨fun i j => by rw [GlobalTheory.EulerTwRestr.loc_val]; exact h1 i j,
      fun i j => by rw [GlobalTheory.EulerTwRestr.loc_inv_val]; exact h2 i j⟩
  refine eventually_cofinite.2 (((eventually_cofinite.1 hx).image
    fun w : Pl E => w.under (𝓞 (maximalRealSubfield E))).subset ?_)
  intro v hv
  simp only [Set.mem_setOf_eq, mem_Kn, not_forall, ev_pn] at hv
  obtain ⟨w, hw⟩ := hv
  exact ⟨w.1, hw, w.2⟩

theorem exists_lift (y : ∀ v : PlF E, GL (Fin n) (Av v)) (hy : ∀ᶠ v : PlF E in cofinite, y v ∈ Kn n v) :
    ∃ x : GL (Fin n) (Af E), ∀ v, pn n v x = y v := by
  let un : Pl E → PlF E := fun w => w.under (𝓞 (maximalRealSubfield E))
  let Y : ∀ w : Pl E, GLw n w := fun w => ev (⟨w, rfl⟩ : Above (un w)) (y (un w))
  have hc : ∀ᶠ w : Pl E in cofinite, Y w ∈ GlobalTheory.LFun.KGL w (n := n) := by
    have hB := eventually_cofinite.1 hy
    refine eventually_cofinite.2 ((hB.biUnion fun v _ => (Set.finite_coe_iff (s := {w : Pl E | un w = v})).1 (finite_above v)).subset ?_)
    intro w hw
    refine Set.mem_iUnion₂.2 ⟨un w, fun h => hw (mem_Kn.1 h ⟨w, rfl⟩), rfl⟩
  let M : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => (Y w).1 i j, hc.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).1 i j⟩
  let M' : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => ((Y w)⁻¹).1 i j, hc.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).2 i j⟩
  have hloc : ∀ P Q : Matrix (Fin n) (Fin n) (Af E), (∀ w : Pl E, P.map (pLoc E w) = Q.map (pLoc E w)) → P = Q :=
    fun P Q h => Matrix.ext fun i j => Subtype.ext (funext fun w => congrFun (congrFun (h w) i) j)
  have hMM' : M * M' = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (Y w).mul_inv
  have hM'M : M' * M = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (Y w).inv_mul
  refine ⟨⟨M, M', hMM', hM'M⟩, fun v => Units.ext (Matrix.ext fun i j => funext ?_)⟩
  rintro ⟨w, rfl⟩
  rfl

theorem exists_Kf_lift {v : PlF E} {k : GL (Fin n) (Av v)} (hk : k ∈ Kn n v) :
    ∃ x ∈ Kf E n, pn n v x = k := by
  have hm : ∀ u : PlF E, (Function.update (fun u : PlF E => (1 : GL (Fin n) (Av u))) v k) u ∈ Kn n u := by
    intro u
    by_cases h : u = v
    · subst h
      simpa using hk
    · simp [Function.update_of_ne h, one_mem]
  obtain ⟨x, hx⟩ := exists_lift _ (Eventually.of_forall hm)
  exact ⟨x, mem_Kf_iff.2 fun u => by rw [hx]; exact hm u, by rw [hx]; simp⟩

theorem isCompact_Kn (v : PlF E) : IsCompact (Kn n v : Set (GL (Fin n) (Av v))) := by
  have e : (Kn n v : Set (GL (Fin n) (Av v))) = pn n v '' (Kf E n : Set (GL (Fin n) (Af E))) := by
    ext k
    refine ⟨fun hk => ?_, ?_⟩
    · obtain ⟨x, hx, rfl⟩ := exists_Kf_lift hk
      exact ⟨x, hx, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact mem_Kf_iff.1 hg v
  rw [e]
  exact (GlobalTheory.EulerTwRestr.isCompact_Kglob (E := E) (n := n)).image (continuous_pn v)

theorem coe_Kv (a b : ℕ) (v : PlF E) : (Kv a b v : Set (Yv a b v)) =
    (Kn a v : Set (GL (Fin a) (Av v))) ×ˢ (Kn b v : Set (GL (Fin b) (Av v))) :=
  Set.ext fun _ => mem_Kv

theorem mem_prod_iff (a b : ℕ) (x : Gf E a b) :
    x ∈ (Kf E a).prod (Kf E b) ↔ ∀ v, pv a b v x ∈ Kv a b v := by
  rw [Subgroup.mem_prod, mem_Kf_iff, mem_Kf_iff]
  simp only [mem_Kv, forall_and]
  rfl

theorem isOpen_Kf : IsOpen (Kf E n : Set (GL (Fin n) (Af E))) := GlobalTheory.EulerTwRestr.isOpen_Kglob

theorem isCompact_Kf : IsCompact (Kf E n : Set (GL (Fin n) (Af E))) := GlobalTheory.EulerTwRestr.isCompact_Kglob

theorem coe_level (a b : ℕ) : {x : Gf E a b | ∀ v, pv a b v x ∈ Kv a b v} =
    (Kf E a : Set (GL (Fin a) (Af E))) ×ˢ (Kf E b : Set (GL (Fin b) (Af E))) :=
  Set.ext fun x => (mem_prod_iff a b x).symm

theorem isRestrGroup (a b : ℕ) :
    GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch (Gf E a b)) (pv (E := E) a b) (Kv a b) := by
  refine ⟨fun w => w.elim, fun v => ?_, fun v => ?_, fun v => ?_, fun x y _ H => ?_, fun x => ?_, fun c y hy => ?_, ?_, fun C _ => ?_⟩
  · exact ((continuous_pn v).comp continuous_fst).prodMk ((continuous_pn v).comp continuous_snd)
  · rw [coe_Kv]
    exact (isOpen_Kn v).prod (isOpen_Kn v)
  · rw [coe_Kv]
    exact (isCompact_Kn v).prod (isCompact_Kn v)
  · exact Prod.ext (pn_ext fun v => congrArg Prod.fst (H v)) (pn_ext fun v => congrArg Prod.snd (H v))
  · filter_upwards [eventually_mem_Kn x.1, eventually_mem_Kn x.2] with v h1 h2
    exact mem_Kv.2 ⟨h1, h2⟩
  · obtain ⟨x₁, h₁⟩ := exists_lift (fun v => (y v).1) (hy.mono fun v h => (mem_Kv.1 h).1)
    obtain ⟨x₂, h₂⟩ := exists_lift (fun v => (y v).2) (hy.mono fun v h => (mem_Kv.1 h).2)
    exact ⟨(x₁, x₂), fun w => w.elim, fun v => Prod.ext (h₁ v) (h₂ v)⟩
  · rw [coe_level]
    exact isOpen_Kf.prod isOpen_Kf
  · have e : {x : Gf E a b | (∀ w, GlobalTheory.RestrMeas.noArch (Gf E a b) w x ∈ C w) ∧ ∀ v, pv a b v x ∈ Kv a b v} =
        (Kf E a : Set (GL (Fin a) (Af E))) ×ˢ (Kf E b : Set (GL (Fin b) (Af E))) := by
      rw [← coe_level]
      exact Set.ext fun x => ⟨fun h => h.2, fun h => ⟨fun w => w.elim, h⟩⟩
    rw [e]
    exact isCompact_Kf.prod isCompact_Kf

theorem cjv_spec (hC : CjEx) (v : PlF E) (x : Af E) :
    projv v (conjFin (IsCMField.complexConj E).toRingEquiv x) = cjv v (projv v x) := by
  have h := hC E v
  rw [cjv, dite_eq_left h]
  exact h.choose_spec.2 x

theorem pn_thF (hC : CjEx) (n : ℕ) (v : PlF E) (x : GL (Fin n) (Af E)) :
    pn n v (thF E n x) = thetaGL n (cjv v) (pn n v x) :=
  GlobalTheory.ThetaPull.map_thetaGL _ _ _ (cjv_spec hC v) x

theorem pv_thP (hC : CjEx) (a b : ℕ) (v : PlF E) (x : Gf E a b) :
    pv a b v (thP E a b x) = thv a b v (pv a b v x) :=
  Prod.ext (pn_thF hC a v x.1) (pn_thF hC b v x.2)

theorem theta_mem_Kn (hC : CjEx) {v : PlF E} {k : GL (Fin n) (Av v)} (hk : k ∈ Kn n v) :
    thetaGL n (cjv v) k ∈ Kn n v := by
  obtain ⟨x, hx, rfl⟩ := exists_Kf_lift hk
  rw [← pn_thF hC]
  exact mem_Kf_iff.1 (GlobalTheory.EulerTwKU.thF_mem_Kglob x hx) v

theorem main : RestrV := fun hC E _ _ _ a b =>
  ⟨isRestrGroup a b, fun v x => pv_thP hC a b v x,
    fun v k hk => mem_Kv.2 ⟨theta_mem_Kn hC (mem_Kv.1 hk).1, theta_mem_Kn hC (mem_Kv.1 hk).2⟩,
    mem_prod_iff a b⟩

end GlobalTheory.CompanionTheory.EulerV

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteRestrictionVanishingStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_restriction_vanishing : PositivityTheory.Rg.BcB.G8.Fin.RestrV := by
  first | exact @GlobalTheory.CompanionTheory.EulerV.main | exact GlobalTheory.CompanionTheory.EulerV.main | (intros; apply GlobalTheory.CompanionTheory.EulerV.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordForm
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

abbrev Idx (n d : ℕ) : Type := Fin n ⊕ (Fin d × {p : Fin n × Fin n // p.1 < p.2})

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def hCo (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) {n : ℕ}
    (S : HermR R σ n) : Idx n d → R :=
  Sum.elim
    (fun i => algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i))
    (fun q => (Algebra.TensorProduct.basis R b).repr
      ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) q.2.1.1 q.2.1.2) q.1)

def coordForm (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) : Matrix (Idx n d) (Idx n d) F :=
  Matrix.fromBlocks 1 0 0
    (Matrix.blockDiagonal fun _ : {p : Fin n × Fin n // p.1 < p.2} =>
      Matrix.of fun k l : Fin d => Algebra.trace F E (b k * σ (b l)))

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
end
end
