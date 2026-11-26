module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramKernelSignNonsplitBaseChangeEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubledUnitaryChartSplitPlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
noncomputable section

namespace GlobalTheory.ThK.Inhab

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}
  {X : Chars F E}

theorem pairV {a a' : ℕ} {G : Geo σ a a'} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
  (Check.isPair_of_isTriple h).1

theorem pairV' {a a' : ℕ} {G : Geo σ a a'} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  (Check.isPair_of_isTriple h).2

theorem two_le_rank {a a' : ℕ} {G : Geo σ a a'} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
    2 ≤ a' ∧ a' < a := by
  have h1 := h.geo.aBig
  exact ⟨by omega, h.geo.lt⟩

theorem conj_conj (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])

end General

section Grid

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil
  GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.FunObj

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

end Grid

end GlobalTheory.ThK.Inhab

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.RegConst
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SqTower

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc}

abbrev TriG (G : GridData Lc sc) (i j : Fin D.R.m) :=
  Tri T (G.V (.grid (i + 1) (j + 1))) (G.V (.grid i j)) (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j)))

def TopGrid (W : G.Weil) (i j : Fin D.R.m) (X : TriG G i j) : Prop :=
  X.rA.Λ = G.Λ (.grid (i + 1) (j + 1)) ∧ X.rA'.Λ = G.Λ (.grid i j) ∧
    X.rW.Λ = GlobalTheory.Doubling.sumLat finSumFinEquiv (G.Λ (.grid i (j + 1))) (G.Λ (.grid (i + 1) j)) ∧
    X.rA.s = W.cart (.grid (i + 1) (j + 1)) ∧ X.rA'.s = W.cart (.grid i j) ∧
    ∀ (AV : Fr (G.V (.grid i (j + 1)))) (AV₁ : Fr (G.V (.grid (i + 1) j))), IsGridFr W _ AV → IsGridFr W _ AV₁ →
      X.rW.s = (frSum AV AV₁).cart

def RegConst (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (c : ℂ) : Prop :=
  ∀ M : Vol G, M.Is t → ∀ Θ Θ', IsMatched B t ρ i j Θ Θ' → ∀ g g₁, ∃ z, zdeg z ≠ 0 ∧ SquareConv W M Θ Θ' z g g₁ ∧
    zdeg z * ∫ u in M.fd _, kerBig W Θ g g₁ u ∂M.ν _ = c * ∫ u in M.fd _, translates z (kerSmall W Θ' g g₁) u ∂M.ν _

end GlobalTheory.SqTower

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal

namespace GlobalTheory.ResLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def col {n r : ℕ} (X : Matrix (Fin n) (Fin (r + 1)) E) : Matrix (Fin n) (Fin 1) E := X.submatrix id fun _ => 0

def Scales (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) (p : GAd σ J)
    (l : (AF F ⊗[F] E)ˣ) : Prop := (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x

def lineGrp (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) : Subgroup (GAd σ J) where
  carrier := {p | ∃ l, Scales σ J x p l}
  one_mem' := ⟨1, by simp [Scales]⟩
  mul_mem' := fun {a b} ⟨l, e⟩ ⟨l', e'⟩ => ⟨l * l', by
    unfold Scales at *
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, e', Matrix.mul_smul, e, smul_smul, Units.val_mul, mul_comm]⟩
  inv_mem' := fun {a} ⟨l, e⟩ => ⟨l⁻¹, by
    unfold Scales at *
    have := congrArg (fun Z => (l⁻¹).1 • ((matHom _ σ J a⁻¹).1 * Z)) e
    simp only [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul,
      Matrix.mul_smul, smul_smul, Units.inv_mul, one_smul] at this
    exact this.symm⟩

structure Data (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin (r + 1)) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) : Prop where
  cm : IsCMExt F E σ
  unr : Algebra.Unramified (𝓞 F) (𝓞 E)
  herm : IsHermND σ J
  witt : IsWittFrame σ J X Y
  adapted : GlobalTheory.EisLine.IsAdapted σ J X Y L a
  iwa : ∀ g, ∃ p l, Scales σ J (col X) p l ∧ ∃ k ∈ levelAll σ J L a, g = p * k
  ht : ∀ p l, Scales σ J (col X) p l → ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E l

def IsReps (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) (T : Set (ratPts σ J)) : Prop :=
  ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ l, Scales σ J x (γ * t⁻¹ : ratPts σ J).1 l

structure IsHt {G : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) (h : G → ℝ) : Prop where
  pos : ∀ g, 0 < h g
  cont : Continuous h
  one : ∀ k ∈ K, h k = 1
  iw : ∀ g, ∃ k ∈ K, ∀ x, h (g * x) = h g * h (k * x)

instance countable_inf {G : Type} [Group G] (Γ H : Subgroup G) [Countable Γ] : Countable (Γ ⊓ H : Subgroup G) :=
  (Subgroup.inclusion_injective inf_le_left).countable

structure SemiLat {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] (N M Λ : Subgroup G) (ν : Measure N)
    (π : Measure M) (𝓝 : Set N) (𝓜 : Set M) : Prop where
  closedN : IsClosed (N : Set G)
  closedM : IsClosed (M : Set G)
  norm : ∀ m ∈ M, ∀ u ∈ N, m * u * m⁻¹ ∈ N
  disj : ∀ g ∈ N, g ∈ M → g = 1
  dec : ∀ γ ∈ Λ, ∃ u ∈ N, ∃ m ∈ M, u ∈ Λ ∧ m ∈ Λ ∧ γ = u * m
  haarN : ν.IsHaarMeasure
  haarM : π.IsHaarMeasure
  domN : IsFundamentalDomain (Λ.subgroupOf N) 𝓝 ν
  domM : IsFundamentalDomain (Λ.subgroupOf M) 𝓜 π
  finN : ν 𝓝 ≠ ⊤
  finM : π 𝓜 ≠ ⊤
  count : Countable Λ := by infer_instance
  topGrp : IsTopologicalGroup G := by infer_instance
  borel : BorelSpace G := by infer_instance

namespace Inhab

open GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (conjUnit)

variable {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E}


theorem semiLat_ne_zero {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    {N M Λ : Subgroup G} {ν : Measure N} {π : Measure M} {𝓝 : Set N} {𝓜 : Set M}
    (H : SemiLat N M Λ ν π 𝓝 𝓜) : ν 𝓝 ≠ 0 := by
  haveI := H.haarN
  haveI := H.count
  haveI := H.topGrp
  haveI := H.borel
  haveI : Countable (Λ.subgroupOf N) := Function.Injective.countable
    (f := fun x : Λ.subgroupOf N => (⟨x.1.1, x.2⟩ : Λ)) fun a b h => Subtype.ext (Subtype.ext (congrArg (·.1) h))
  exact H.domN.measure_ne_zero (NeZero.ne ν)

theorem fd_one {H : Type} [Group H] [MeasurableSpace H] [MeasurableSingletonClass H] (Λ : Subgroup H) (hΛ : ∀ g, g ∈ Λ)
    (μ : Measure H) : IsFundamentalDomain Λ ({1} : Set H) μ :=
  IsFundamentalDomain.mk' (measurableSet_singleton _).nullMeasurableSet fun x =>
    ⟨⟨x⁻¹, hΛ _⟩, inv_mul_cancel x, fun _ hy => Subtype.ext (eq_inv_of_mul_eq_one_left hy)⟩

theorem haar_count {H : Type} [Group H] [Finite H] [TopologicalSpace H] [DiscreteTopology H] [MeasurableSpace H]
    [BorelSpace H] : (Measure.count : Measure H).IsHaarMeasure :=
  { toIsFiniteMeasureOnCompacts := inferInstance, toIsMulLeftInvariant := inferInstance,
    open_pos := fun U _ hU h => hU.ne_empty (Measure.count_eq_zero_iff.1 h) }

theorem semiLat_finite {G : Type} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G] [MeasurableSpace G]
    [BorelSpace G] (N M : Subgroup G) [hN : N.Normal] (hd : ∀ g ∈ N, g ∈ M → g = 1) (hs : ∀ g, ∃ u ∈ N, ∃ m ∈ M, g = u * m) :
    SemiLat N M ⊤ Measure.count Measure.count {1} {1} :=
  ⟨isClosed_discrete _, isClosed_discrete _, fun m _ u hu => hN.conj_mem u hu m, hd,
    fun γ _ => let ⟨u, hu, m, hm, e⟩ := hs γ; ⟨u, hu, m, hm, trivial, trivial, e⟩, haar_count, haar_count,
    fd_one _ (fun _ => Subgroup.mem_subgroupOf.2 (Subgroup.mem_top _)) _,
    fd_one _ (fun _ => Subgroup.mem_subgroupOf.2 (Subgroup.mem_top _)) _, by simp, by simp,
    inferInstance, inferInstance, inferInstance⟩

end Inhab

end GlobalTheory.ResLine

end
end
