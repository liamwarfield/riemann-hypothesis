module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStanding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesOverSplitPlaces
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPcRatFMem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
noncomputable section

namespace GlobalTheory.ArchSch

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

def ech (t : ℝ) : ℂ := Complex.exp (-(2 * Real.pi * Complex.I) * (t : ℂ))

def sch {Y : Type} [AddCommGroup Y] [Module ℝ Y] (β : LinearMap.BilinForm ℝ Y) (a b : Y) (f : Y → ℂ) : Y → ℂ :=
  fun x => ech (β x b + β a b / 2) * f (x + a)

variable (F : Type) [Field F] [NumberField F]

def arch {κ : Type} (v : κ → AF F) : κ → mixedEmbedding.mixedSpace F := fun i => evI F (v i)

def trP (κ : Type) [Fintype κ] : LinearMap.BilinForm ℝ (κ → mixedEmbedding.mixedSpace F) :=
  LinearMap.mk₂ ℝ (fun x y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i))
    (fun _ _ _ => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)])
    (fun _ _ _ => by simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, LinearMap.map_smul, smul_eq_mul])
    (fun _ _ _ => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)])
    (fun _ _ _ => by simp only [Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, LinearMap.map_smul, smul_eq_mul])

theorem mixedTracePairing_apply {κ : Type} [Fintype κ] (x y : κ → mixedEmbedding.mixedSpace F) :
    trP F κ x y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i) := rfl

def liftA (ξ : mixedEmbedding.mixedSpace F) : AF F :=
  LinearMap.inl F (Ainf F) (Af F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm ξ)

variable {F} {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d d₁ : ℕ} {X : Spc F E n}
  {W : Spc F E d} {W₁ : Spc F E d₁}

def lagSet (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) :
    Set ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :=
  {l | ∃ u ∈ iso0 (F := F) n H', At (evI F) u ∧ ∃ z : Matrix (Fin n) (Fin d₁) (AE F E), At (evI F) z ∧
    arch F (M₁.co.e z).1 = 0 ∧
    l = (arch F (M.co.e (u + incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)).1,
      arch F (M.co.e (u + incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)).2)}

end GlobalTheory.ArchSch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymp
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChange

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

def spAct {R : Type} [CommRing R] [Algebra F R] (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (w : (κ → R) × (κ → R)) :
    (κ → R) × (κ → R) :=
  (fun k => (G.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2) (Sum.inl k),
    fun k => (G.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2) (Sum.inr k))

def weylM : Matrix (κ ⊕ κ) (κ ⊕ κ) F := Matrix.fromBlocks 0 1 (-1) 0

def leviM (A : Matrix κ κ F) : Matrix (κ ⊕ κ) (κ ⊕ κ) F := Matrix.fromBlocks A 0 0 A⁻¹ᵀ

def unipM (S : Matrix κ κ F) : Matrix (κ ⊕ κ) (κ ⊕ κ) F := Matrix.fromBlocks 1 0 S 1

def IsSymp (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Prop := G.transpose * weylM * G = weylM

def gens : Set (Matrix (κ ⊕ κ) (κ ⊕ κ) F) :=
  {G | ∃ A : Matrix κ κ F, IsUnit A.det ∧ G = leviM A} ∪ {G | ∃ S : Matrix κ κ F, S.transpose = S ∧ G = unipM S} ∪ {weylM}

variable [NumberField F]

def indO (v : Pl (F := F)) : (κ → Fv F v) → ℂ := Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1

def HasOp (ψ : AddChar (AF F) ℂ) (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Prop :=
  ∃ (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    Function.Surjective ei ∧ (∀ Φ ∈ schA F κ, e Φ ∈ schA F κ) ∧
    (∀ w, ∀ Φ ∈ schA F κ, e (schr ψ w Φ) = schr ψ (spAct G w) (e Φ)) ∧
    (∀ v, (SB _).map (ev v) = SB _) ∧ (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ = 0 → φ = 0) ∧
    (∀ v w, ∀ φ ∈ SB (κ → Fv F v),
      ev v (schr (GlobalTheory.LatVac.psiAt ψ v) w φ) = schr (GlobalTheory.LatVac.psiAt ψ v) (spAct G w) (ev v φ)) ∧
    (∀ᶠ v in cofinite, ev v (indO v) = indO v) ∧
    ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = indO v) → e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v)

end GlobalTheory.SympChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzConjMem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzConjMem
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section
open scoped Classical

namespace GlobalTheory.ConjSch

def conjSchwartz {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) : SchwartzMap V ℂ where
  toFun x := starRingEnd ℂ (f x)
  smooth' := Complex.conjCLE.contDiff.comp f.smooth'
  decay' k n := by
    obtain ⟨C, hC⟩ := f.decay' k n
    refine ⟨C, fun x => ?_⟩
    have e : (fun x => starRingEnd ℂ (f x)) = (Complex.conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ) ∘ f := by
      funext y; simp
    rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    exact hC x

theorem conjSchwartz_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) (x : V) :
    conjSchwartz f x = starRingEnd ℂ (f x) := rfl

theorem conj_mem_schA : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ schA F κ, (fun x => starRingEnd ℂ (Φ x)) ∈ schA F κ := by
  intro F _ _ κ _ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Ψ hΨ =>
    obtain ⟨f, g, hg, rfl⟩ := hΨ
    apply Submodule.subset_span
    refine ⟨conjSchwartz f, fun y => starRingEnd ℂ (g y), ⟨hg.1.comp _, hg.2.comp_left (map_zero _)⟩, ?_⟩
    funext x
    simp [pureA, conjSchwartz_apply, map_mul]
  | zero =>
    convert (schA F κ).zero_mem using 1
    funext x; simp
  | add Ψ₁ Ψ₂ _ _ h₁ h₂ =>
    have := (schA F κ).add_mem h₁ h₂
    convert this using 1
    funext x; simp
  | smul c Ψ _ h =>
    have := (schA F κ).smul_mem (starRingEnd ℂ c) h
    convert this using 1
    funext x; simp

end GlobalTheory.ConjSch

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzConjMemStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_schwartz_conj_mem : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ schA F κ, (fun x => starRingEnd ℂ (Φ x)) ∈ schA F κ := by
  first | exact @GlobalTheory.ConjSch.conj_mem_schA | exact GlobalTheory.ConjSch.conj_mem_schA | (intros; apply GlobalTheory.ConjSch.conj_mem_schA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatInvariantUnderIntegralLattice
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.SBTransl

theorem exists_nhds_zero_invariant {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X]
    {β : Type} [Zero β] (g : X → β) (hg : IsLocallyConstant g) (hc : HasCompactSupport g) :
    ∃ V ∈ 𝓝 (0 : X), ∀ x, ∀ u ∈ V, g (x + u) = g x := by
  have hW : ∀ x : X, {u : X | g (x + u) = g x} ∈ 𝓝 (0 : X) := fun x => by
    have h1 : IsOpen {y : X | g y = g x} := hg.isOpen_fiber _
    have h2 : Continuous fun u : X => x + u := continuous_const.add continuous_id
    exact (h2.isOpen_preimage _ h1).mem_nhds (by simp)
  choose W' hW' hW'h using fun x => exists_nhds_zero_half (hW x)
  have hU : ∀ x ∈ tsupport g, {y : X | y - x ∈ W' x} ∈ 𝓝 x := fun x _ => by
    have h2 : Continuous fun y : X => y - x := continuous_id.sub continuous_const
    exact h2.continuousAt.preimage_mem_nhds (by simpa using hW' x)
  obtain ⟨t, -, ht⟩ := hc.isCompact.elim_nhds_subcover _ hU
  set V0 : Set X := ⋂ x ∈ t, W' x
  have hV0 : V0 ∈ 𝓝 (0 : X) := (Filter.biInter_finset_mem t).2 fun x _ => hW' x
  have key : ∀ y ∈ tsupport g, ∀ u ∈ V0, g (y + u) = g y := fun y hy u hu => by
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hy)
    have hux : u ∈ W' x := Set.mem_iInter₂.1 hu x hx
    have e1 : g (x + ((y - x) + u)) = g x := hW'h x _ hyx _ hux
    have e2 : g (x + ((y - x) + 0)) = g x := hW'h x _ hyx _ (mem_of_mem_nhds (hW' x))
    rw [show x + ((y - x) + u) = y + u by abel] at e1
    rw [show x + ((y - x) + 0) = y by abel] at e2
    rw [e1, e2]
  refine ⟨V0 ∩ Neg.neg ⁻¹' V0, Filter.inter_mem hV0 (neg_mem_nhds_zero X hV0), fun x u hu => ?_⟩
  by_cases hx : x ∈ tsupport g
  · exact key x hx u hu.1
  by_cases hxu : x + u ∈ tsupport g
  · have := key (x + u) hxu (-u) hu.2
    rw [add_neg_cancel_right] at this
    exact this.symm
  rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxu]

end GlobalTheory.SBTransl

namespace GlobalTheory.SBTransl

theorem norm_absNorm_lt_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖ < 1 := by
  have := (NumberField.FinitePlace.norm_lt_one_iff_mem F v _).2 (Ideal.absNorm_mem v.asIdeal)
  simpa using this

theorem exists_nat_subset_nhds {F : Type} [Field F] [NumberField F] (V : Set (FiniteAdeleRing (𝓞 F) F))
    (hV : V ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F)) :
    ∃ m : ℕ, 0 < m ∧ ∀ z : FiniteAdeleRing (𝓞 F) F,
      (∀ v, ‖Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v z‖ ≤ ‖(m : Fv F v)‖) → z ∈ V := by
  classical
  have hopen : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) := fun v => Valued.isOpen_integer _
  let f : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) → FiniteAdeleRing (𝓞 F) F :=
    RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
  have hf : IsOpenEmbedding f := RestrictedProduct.isOpenEmbedding_structureMap hopen
  have hV' : f ⁻¹' V ∈ 𝓝 (0 : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) := by
    rw [← Filter.mem_map, hf.map_nhds_eq]
    exact hV
  rw [nhds_pi, Filter.mem_pi] at hV'
  obtain ⟨I, hI, t, ht, hsub⟩ := hV'
  have hk : ∀ v, ∃ k : ℕ, ∀ y : v.adicCompletionIntegers F,
      ‖(y : v.adicCompletion F)‖ ≤ ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖ ^ k → y ∈ t v := fun v => by
    have h1 := ht v
    rw [nhds_subtype, Filter.mem_comap] at h1
    obtain ⟨s, hs, hss⟩ := h1
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hs
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (norm_absNorm_lt_one v)
    refine ⟨k, fun y hy => hss (hball ?_)⟩
    rw [Metric.mem_ball, show ((0 : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) v : v.adicCompletion F) = 0 from rfl,
      dist_zero_right]
    exact lt_of_le_of_lt hy hk
  choose k hk using hk
  refine ⟨∏ v ∈ hI.toFinset, Ideal.absNorm v.asIdeal ^ k v, Finset.prod_pos fun v _ =>
    pow_pos (lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)) _, fun z hz => ?_⟩
  have hint : ∀ v, z v ∈ v.adicCompletionIntegers F := fun v =>
    Valued.toNormedField.norm_le_one_iff.1 ((hz v).trans (GlobalTheory.SmoothForms.denom_norm_natCast_le_one v _))
  have hz' : z = f (fun v => ⟨z v, hint v⟩) := by
    ext v; rfl
  rw [hz']
  refine hsub (fun v hv => hk v _ ?_)
  have hvI : v ∈ hI.toFinset := hI.mem_toFinset.2 hv
  refine (hz v).trans ?_
  rw [← Finset.mul_prod_erase _ _ hvI, Nat.cast_mul, norm_mul, Nat.cast_pow, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (GlobalTheory.SmoothForms.denom_norm_natCast_le_one v _)

end GlobalTheory.SBTransl

namespace GlobalTheory.SBTransl

theorem exists_mulInt_invariant {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ m : ℕ, 0 < m ∧ ∀ a : κ → AF F, IsMulInt F m a → ∀ x : κ → FiniteAdeleRing (𝓞 F) F,
      g (x + fun i => (a i).2) = g x := by
  obtain ⟨hlc, hcs⟩ := hg
  obtain ⟨V, hV, hinv⟩ := exists_nhds_zero_invariant g hlc hcs
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, -, t, ht, hsub⟩ := hV
  obtain ⟨m, hm, hmV⟩ := exists_nat_subset_nhds (⋂ i, t i) (Filter.iInter_mem.2 ht)
  refine ⟨m, hm, fun a ha x => hinv x _ (hsub fun i _ => ?_)⟩
  exact Set.mem_iInter.1 (hmV _ fun v => ha.2 v i) i

theorem transInv : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
    g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) → ∃ m : ℕ, 0 < m ∧ ∀ a : κ → AF F, IsMulInt F m a →
      ∀ x : κ → FiniteAdeleRing (𝓞 F) F, g (x + fun i => (a i).2) = g x :=
  fun g hg => exists_mulInt_invariant g hg

end GlobalTheory.SBTransl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCongruentOneDetSubOneMemIdealMulConj
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCongruentOneDetSubOneMemIdealMulConj
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.StdDatum.DetCong

variable {D : D7}

theorem inc_mul_mem_hatId {I J : Ideal (𝓞 D.host.E)} {b : 𝓞 D.host.E} (hb : b ∈ I) {y : AE D}
    (hy : y ∈ hatId D J) : inc D (b : D.host.E) * y ∈ hatId D (I * J) := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, s, hs, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨b * c, Ideal.mul_mem_mul hb hc, s, hs, ?_⟩
    rw [← mul_assoc, ← map_mul]; rfl
  | zero => rw [mul_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg _ _ h => rw [mul_neg]; exact neg_mem h

theorem sgA_mem_hatId {𝔪 : Ideal (𝓞 D.host.E)} {y : AE D} (hy : y ∈ hatId D 𝔪) :
    sgA D y ∈ hatId D (D.host.conj • 𝔪) := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, s, hs, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨D.host.conj • c, Ideal.smul_mem_pointwise_smul _ _ _ hc, sgA D s,
      VacMove.sgA_mem D hs, ?_⟩
    rw [map_mul, GlobalTheory.NormSum.PtsMem.sgA_inc]; rfl
  | zero => rw [map_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | neg _ _ h => rw [map_neg]; exact neg_mem h

theorem prod_sub_prod_mem {𝔪 : Ideal (𝓞 D.host.E)} {ι : Type*} (s : Finset ι) (f g : ι → AE D)
    (hf : ∀ i ∈ s, f i ∈ OhE D) (hg : ∀ i ∈ s, g i ∈ OhE D) (h : ∀ i ∈ s, f i - g i ∈ hatId D 𝔪) :
    (∏ i ∈ s, f i) - ∏ i ∈ s, g i ∈ hatId D 𝔪 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, sub_self]; exact zero_mem _
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have e : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i =
        f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i := by ring
    rw [e]
    refine add_mem (mul_mem_hatId (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) (fun i hi => hg i (Finset.mem_insert_of_mem hi))
        (fun i hi => h i (Finset.mem_insert_of_mem hi))))
      (mem_hatId_mul (prod_mem fun i hi => hg i (Finset.mem_insert_of_mem hi)) (h a (Finset.mem_insert_self a s)))

theorem det_sub_one_mem_hatId_of {𝔪 : Ideal (𝓞 D.host.E)} {a : ℕ} (M : Matrix (Fin a) (Fin a) (AE D))
    (hM : ∀ i j, M i j ∈ OhE D) (hC : ∀ i j, (M - 1) i j ∈ hatId D 𝔪) : M.det - 1 ∈ hatId D 𝔪 := by
  have h1 : ∀ i j, (1 : Matrix (Fin a) (Fin a) (AE D)) i j ∈ OhE D := fun i j => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  rw [← Matrix.det_one (R := AE D) (n := Fin a), Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
  refine sum_mem fun σ _ => ?_
  rw [← smul_sub]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]
  · rw [one_smul]
    exact prod_sub_prod_mem _ _ _ (fun i _ => hM _ _) (fun i _ => h1 _ _) (fun i _ => hC _ _)
  · rw [Units.neg_smul, one_smul]
    exact neg_mem (prod_sub_prod_mem _ _ _ (fun i _ => hM _ _) (fun i _ => h1 _ _) (fun i _ => hC _ _))

theorem det_sub_one_mem : ∀ (D : D7) {a : ℕ} (𝔪 : Ideal (𝓞 D.host.E)), IsCoprime 𝔪 (D.host.conj • 𝔪) →
    ∀ k : GA D a, k ∈ intG D a → CongOne D 𝔪 k →
      ((Matrix.GeneralLinearGroup.det (k : GL (Fin a) (AE D)) : (AE D)ˣ) : AE D) - 1 ∈
        hatId D (𝔪 * D.host.conj • 𝔪) := by
  intro D a 𝔪 hco k hk hc
  set u : AE D := ((Matrix.GeneralLinearGroup.det (k : GL (Fin a) (AE D)) : (AE D)ˣ) : AE D) with hu
  have hint := (mem_intG k).1 hk
  have huO : u ∈ OhE D := VacMove.det_int D _ hint
  have h1 : u - 1 ∈ hatId D 𝔪 := by
    rw [hu, Matrix.GeneralLinearGroup.val_det_apply]
    exact det_sub_one_mem_hatId_of _ (fun i j => (hint i j).1) hc
  have hn : u * sgA D u = 1 := VacMove.det_norm D k
  have h2 : u - 1 ∈ hatId D (D.host.conj • 𝔪) := by
    have e : u - 1 = -(u * sgA D (u - 1)) := by
      rw [map_sub, map_one, mul_sub, hn]; ring
    rw [e]
    exact neg_mem (mul_mem_hatId huO (sgA_mem_hatId h1))
  have hsup : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ := by
    rw [← Ideal.add_eq_sup, Ideal.isCoprime_iff_add.1 hco, Ideal.one_eq_top]
  have h1m : (1 : 𝓞 D.host.E) ∈ 𝔪 ⊔ D.host.conj • 𝔪 := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 h1m
  have e : u - 1 = inc D (s : D.host.E) * (u - 1) + inc D (t : D.host.E) * (u - 1) := by
    rw [← add_mul, ← map_add (f := _), show (s : D.host.E) + t = ((s + t : 𝓞 D.host.E) : D.host.E) from rfl, hst]; simp
  rw [e]
  refine add_mem (inc_mul_mem_hatId hs h2) ?_
  rw [mul_comm 𝔪]
  exact inc_mul_mem_hatId ht h1

end GlobalTheory.FunObj.StdDatum.DetCong

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCongruentOneDetSubOneMemIdealMulConjStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_congruent_one_det_sub_one_mem_ideal_mul_conj : ∀ (D : D7) {a : ℕ} (𝔪 : Ideal (𝓞 D.host.E)), IsCoprime 𝔪 (D.host.conj • 𝔪) → ∀ k : GA D a, k ∈ intG D a → CongOne D 𝔪 k → ((Matrix.GeneralLinearGroup.det (k : GL (Fin a) (AE D)) : (AE D)ˣ) : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) := by
  first | exact @GlobalTheory.FunObj.StdDatum.DetCong.det_sub_one_mem | exact GlobalTheory.FunObj.StdDatum.DetCong.det_sub_one_mem | (intros; apply GlobalTheory.FunObj.StdDatum.DetCong.det_sub_one_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericGlLocalComponentExponentLeOne
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ThK.DetProd

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Local

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_isGeneric_of_isLocComp {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}
    {τ : GlobalTheory.CuspRep.CuspSub E n} {w : HeightOneSpectrum (𝓞 E)}
    {ρ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) (w.adicCompletion E))} (h : τ.IsLocComp w ρ) :
    ∃ ψ : AddChar (w.adicCompletion E) Circle, Continuous ψ ∧ ψ ≠ 1 ∧ GlobalTheory.Whittaker.IsGeneric ψ ρ.ρ := by
  obtain ⟨f, hf0, hf⟩ := h
  let S : Subrepresentation (τ.locRep w) := ⟨LinearMap.range f, by
    rintro g _ ⟨v, rfl⟩
    exact ⟨ρ.ρ g v, hf g v⟩⟩
  have hS : S.toSubmodule ≠ ⊥ := fun h => hf0 (LinearMap.range_eq_bot.1 h)
  obtain ⟨ψ, hc, h1, hg⟩ := GlobalTheory.CuspDetBlocks.exists_isGeneric_subrep τ w S hS
  exact ⟨ψ, hc, h1, hg.of_surjective (σ := S.toRepresentation) ⟨f.rangeRestrict, fun g => LinearMap.ext fun v => by exact Subtype.ext (hf g v)⟩
    (LinearMap.surjective_rangeRestrict _)⟩

end GlobalTheory.ThK.DetProd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCharacterTrivialOnSmallIdeles
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.PsiTriv

theorem exists_nat_trivial {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) :
    ∃ m : ℕ, 0 < m ∧ ∀ t : AF F, t.1 = 0 → (∀ v, ‖evFin F v t‖ ≤ ‖(m : Fv F v)‖) → ψ t = 1 := by
  classical
  let f : FiniteAdeleRing (𝓞 F) F → AF F := fun y => (0, y)
  have hf : Continuous f := continuous_const.prodMk continuous_id
  have hW : (fun y => ψ (f y)) ⁻¹' {z : ℂ | ‖z - 1‖ < 1 / 2} ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := by
    refine ((isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const))
      continuous_const).preimage (hψ.comp hf)).mem_nhds ?_
    show ‖ψ (0 : AF F) - 1‖ < 1 / 2
    rw [AddChar.map_zero_eq_one]; norm_num
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW
  set D : FiniteAdeleRing (𝓞 F) F := algebraMap F _ (algebraMap (𝓞 F) F d) with hD
  have htriv : ∀ y ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F, ψ (f (D * y)) = 1 := by
    intro y hy
    refine GroundTheory.Global.eq_one_of_sq_mem
      (s := {z | ∃ y ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F, ψ (f (D * y)) = z}) ?_ ?_ ⟨y, hy, rfl⟩
    · rintro _ ⟨a, ha, rfl⟩
      refine ⟨a + a, add_mem ha ha, ?_⟩
      rw [sq, ← AddChar.map_add_eq_mul]
      congr 1
      show ((0 : InfiniteAdeleRing F), D * (a + a)) = ((0 : InfiniteAdeleRing F) + 0, D * a + D * a)
      rw [mul_add, add_zero]
    · rintro _ ⟨a, ha, rfl⟩
      exact hd a ha
  have hm0 : Ideal.absNorm (Ideal.span {d}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hd0
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
  refine ⟨Ideal.absNorm (Ideal.span {d}), Nat.pos_of_ne_zero hm0, fun t ht0 ht => ?_⟩
  have hdF : algebraMap (𝓞 F) F d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hd0
  let y : FiniteAdeleRing (𝓞 F) F := algebraMap F _ (algebraMap (𝓞 F) F d)⁻¹ * t.2
  have hty : t = f (D * y) := by
    refine Prod.ext ht0 ?_
    show t.2 = algebraMap F _ (algebraMap (𝓞 F) F d) * (algebraMap F _ (algebraMap (𝓞 F) F d)⁻¹ * t.2)
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hdF, map_one, one_mul]
  rw [hty]
  refine htriv y fun v => ?_
  have hv : ‖t.2 v‖ ≤ _ := ht v
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff]
  have hy : y v = algebraMap F (Fv F v) (algebraMap (𝓞 F) F d)⁻¹ * t.2 v := rfl
  have hm : ((Ideal.absNorm (Ideal.span {d}) : ℕ) : Fv F v) =
      algebraMap F (Fv F v) (algebraMap (𝓞 F) F e) * algebraMap F (Fv F v) (algebraMap (𝓞 F) F d) := by
    rw [← map_mul, ← map_mul, he, map_natCast, map_natCast]
  have hdv : algebraMap F (Fv F v) (algebraMap (𝓞 F) F d) ≠ 0 := (map_ne_zero _).2 hdF
  have he1 : ‖algebraMap F (Fv F v) (algebraMap (𝓞 F) F e)‖ ≤ 1 := FinitePlace.norm_le_one F v e
  rw [hy, map_inv₀, norm_mul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.2 hdv)]
  rw [hm, norm_mul] at hv
  nlinarith [norm_nonneg (algebraMap F (Fv F v) (algebraMap (𝓞 F) F d)), norm_nonneg (t.2 v)]

end GlobalTheory.PsiTriv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterUnramifiedMu
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterUnramifiedMu
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotTripleUnr

theorem unramAt_mul {D : D7} {ε : AF D.host.F} {χ₁ χ₂ : (AE D)ˣ →* Circle}
    (h₁ : GlobalTheory.WeilParts.UnramAt ε χ₁) (h₂ : GlobalTheory.WeilParts.UnramAt ε χ₂) : GlobalTheory.WeilParts.UnramAt ε (χ₁ * χ₂) := by
  intro x hx h1 h2
  rw [MonoidHom.mul_apply, h₁ x hx h1 h2, h₂ x hx h1 h2, one_mul]

theorem under_eq_of_isConjPl {D : D7} {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl P P') :
    P.under (𝓞 D.host.F) = P'.under (𝓞 D.host.F) := by
  refine HeightOneSpectrum.ext ((P.under (𝓞 D.host.F)).isMaximal.eq_of_le (P'.under (𝓞 D.host.F)).isPrime.ne_top
    fun a ha => ?_)
  obtain ⟨c', h1, h2⟩ := h (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) ha
  have hfix : star (algebraMap D.host.F D.host.E (a : D.host.F)) = algebraMap D.host.F D.host.E (a : D.host.F) :=
    (D.sp.cm.fixed _).2 ⟨_, rfl⟩
  have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a = c' := RingOfIntegers.ext (h2.trans hfix).symm
  change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ P'.asIdeal
  rwa [e]

theorem unramAt_mu : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∉ G.pl.S0 → (∀ PP ∈ Lc.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) → ∀ j : Fin D.R.m, GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1)) := by
  intro D T Lc sc G μ₀ hL t v e he hv hQ j
  have hmu : Lc.mu t (j + 1) = Lc.mu0 ((j : ℕ) + 1) * Lc.xi t := rfl
  rw [hmu]
  refine unramAt_mul ?_ ?_
  · refine GlobalTheory.UnramOver.unramAt_of_unrAt D _ (Lc.C.mu0 j) (hL.mu0 j) v e he fun P hP => ?_
    refine (Lc.C.isMu0 j).unr P fun k hk => hv ?_
    have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
      rw [← hP]
      change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ P.asIdeal
      rw [map_natCast]
      exact hk
    refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
    fin_cases k
    · exact Or.inl hk'
    · exact Or.inr (Or.inl hk')
  · refine GlobalTheory.UnramOver.unramAt_of_unrAt D _ (Lc.xiH t) (hL.xi t) v e he fun P hP => ?_
    by_contra hn
    rcases (hL.Q_ram t P).1 hn with hq | ⟨P', hq, hc⟩
    · exact hQ P hq hP
    · exact hQ P' hq ((under_eq_of_isConjPl hc).trans hP)

end GlobalTheory.BotTripleUnr

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterUnramifiedMuStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_character_unramified_mu : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∉ G.pl.S0 → (∀ PP ∈ Lc.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) → ∀ j : Fin D.R.m, GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1)) := by
  first | exact @GlobalTheory.BotTripleUnr.unramAt_mu | exact GlobalTheory.BotTripleUnr.unramAt_mu | (intros; apply GlobalTheory.BotTripleUnr.unramAt_mu <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLevelConductorCompatible
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

noncomputable section
namespace GlobalTheory.PureFix

theorem pureA_fixed : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (m₁ M m₃ : ℕ), 0 < m₁ → 0 < M → 0 < m₃ → (∀ a : κ → AF F, IsMulInt F m₁ a → ∀ x : κ → FiniteAdeleRing (𝓞 F) F, g (x + fun i => (a i).2) = g x) → (∀ x : κ → AF F, g (fun i => (x i).2) ≠ 0 → ∀ i v, ‖(M : Fv F v) * evFin F v (x i)‖ ≤ 1) → (∀ t : AF F, t.1 = 0 → (∀ v, ‖evFin F v t‖ ≤ ‖(m₃ : Fv F v)‖) → ψ t = 1) → ∀ f : (κ → mixedEmbedding.mixedSpace F) → ℂ, ∀ a b : κ → AF F, IsMulInt F (2 * m₁ * M * m₃) a → IsMulInt F (2 * m₁ * M * m₃) b → schr ψ (a, b) (pureA F f g) = pureA F f g := by
  intro F _ _ κ _ ψ g m₁ M m₃ hm₁ hM hm₃ hg hx hψ f a b ha hb
  funext x
  have ha' : IsMulInt F m₁ a := by
    have e : 2 * m₁ * M * m₃ = (2 * M * m₃) * m₁ := by ring
    rw [e] at ha; exact ha.mono
  have e1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + a) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 := by
    funext i; congr 1; show (x i).1 + (a i).1 = (x i).1; rw [ha.1 i, add_zero]
  have e2 : (fun i => ((x + a) i).2) = (fun i => (x i).2) + fun i => (a i).2 := rfl
  simp only [schr, pureA]
  rw [e1, e2, hg a ha' (fun i => (x i).2)]
  by_cases h0 : g (fun i => (x i).2) = 0
  · simp [h0]
  · have hs : ∀ (c d : κ → AF F), (∀ i, (d i).1 = 0) → (c ⬝ᵥ d).1 = 0 := by
      intro c d hd
      change fstA F (∑ i, c i * d i) = 0
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]; refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_mul]; change (c i).1 * (d i).1 = 0; rw [hd i, mul_zero]
    have hnat : ∀ (v : HeightOneSpectrum (𝓞 F)) (n : ℕ), ‖(n : Fv F v)‖ ≤ 1 :=
      fun v n => GlobalTheory.SmoothForms.denom_norm_natCast_le_one v n
    rw [hψ _ ?_ ?_, one_mul]
    · change (x ⬝ᵥ b).1 + (⅟2 : AF F).1 * (a ⬝ᵥ b).1 = 0
      rw [hs x b hb.1, hs a b hb.1, mul_zero, add_zero]
    · intro v
      have hb' : ∀ i, ‖evFin F v (b i)‖ ≤ ‖(2 * m₁ : Fv F v)‖ * ‖(M : Fv F v)‖ * ‖(m₃ : Fv F v)‖ := by
        intro i; have := hb.2 v i; push_cast at this; simpa [norm_mul, mul_assoc] using this
      have h2 : ‖evFin F v (⅟2 : AF F)‖ * ‖(2 : Fv F v)‖ = 1 := by
        rw [← norm_mul, show (2 : Fv F v) = evFin F v (2 : AF F) from (map_ofNat _ 2).symm, ← map_mul,
          invOf_mul_self, map_one, norm_one]
      have ha2 : ∀ i, ‖evFin F v (⅟2 * a i)‖ ≤ 1 := by
        intro i
        have := ha.2 v i
        push_cast at this
        rw [map_mul, norm_mul]
        calc ‖evFin F v (⅟2 : AF F)‖ * ‖evFin F v (a i)‖
            ≤ ‖evFin F v (⅟2 : AF F)‖ * ‖(2 * m₁ * M * m₃ : Fv F v)‖ := by gcongr
          _ = (‖evFin F v (⅟2 : AF F)‖ * ‖(2 : Fv F v)‖) * ‖((m₁ * M * m₃ : ℕ) : Fv F v)‖ := by
              push_cast; simp only [norm_mul]; ring
          _ ≤ 1 := by rw [h2, one_mul]; exact hnat v _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_add (f := _), dotProduct, dotProduct, Finset.mul_sum, map_sum, map_sum]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
        rw [map_mul, norm_mul]
        calc ‖evFin F v (x i)‖ * ‖evFin F v (b i)‖
            ≤ ‖evFin F v (x i)‖ * (‖(2 * m₁ : Fv F v)‖ * ‖(M : Fv F v)‖ * ‖(m₃ : Fv F v)‖) := by
              gcongr; exact hb' i
          _ = ‖(M : Fv F v) * evFin F v (x i)‖ * ‖((2 * m₁ : ℕ) : Fv F v)‖ * ‖(m₃ : Fv F v)‖ := by
              push_cast; simp only [norm_mul]; ring
          _ ≤ 1 * 1 * ‖(m₃ : Fv F v)‖ := by
              gcongr
              · exact hx x h0 i v
              · exact hnat v _
          _ = ‖(m₃ : Fv F v)‖ := by ring
      · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
        rw [← mul_assoc, map_mul, norm_mul]
        calc ‖evFin F v (⅟2 * a i)‖ * ‖evFin F v (b i)‖
            ≤ 1 * (‖(2 * m₁ : Fv F v)‖ * ‖(M : Fv F v)‖ * ‖(m₃ : Fv F v)‖) := by
              gcongr
              · exact ha2 i
              · exact hb' i
          _ = ‖((2 * m₁ * M : ℕ) : Fv F v)‖ * ‖(m₃ : Fv F v)‖ := by push_cast; simp only [norm_mul]; ring
          _ ≤ 1 * ‖(m₃ : Fv F v)‖ := by gcongr; exact hnat v _
          _ = ‖(m₃ : Fv F v)‖ := one_mul _

end GlobalTheory.PureFix

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorTorusAction
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.MinorWeight

open GlobalTheory.JointHarm

theorem detPlus_diagonal {m : ℕ} (ε : Fin m → Bool) (d : Fin m → ℂ) :
    detP ε (diagonal d) = ∏ a, if ε a then d a else 1 := by
  have e : (1 / 2 : ℂ) • (1 + Formalism.REAL.Jm ε) * diagonal d + (1 / 2 : ℂ) • (1 - Formalism.REAL.Jm ε) =
      diagonal fun a => if ε a then d a else 1 := by
    ext a b
    by_cases h : a = b
    · subst h
      cases e : ε a <;> simp [Formalism.REAL.Jm, e] <;> ring
    · simp [Formalism.REAL.Jm, h]
  rw [detP, e, det_diagonal]

theorem detM_diagonal {m : ℕ} (ε : Fin m → Bool) (d : Fin m → ℂ) :
    detM ε (diagonal d) = ∏ a, if ε a then 1 else d a := by
  have e : (1 / 2 : ℂ) • (1 - Formalism.REAL.Jm ε) * diagonal d + (1 / 2 : ℂ) • (1 + Formalism.REAL.Jm ε) =
      diagonal fun a => if ε a then 1 else d a := by
    ext a b
    by_cases h : a = b
    · subst h
      cases e : ε a <;> simp [Formalism.REAL.Jm, e] <;> ring
    · simp [Formalism.REAL.Jm, h]
  rw [detM, e, det_diagonal]

theorem fact_diagonal {D : D7} {m n : ℕ} (ε : D.what₂.Tau → Fin m → Bool) (p q : D.what₂.Tau → ℕ)
    (ap am : D.what₂.Tau → ℕ → ℕ) (x₁ x₂ x₃ : D.what₂.Tau → ℤ) (hmn : m ≤ n) (hpq : ∀ τ, p τ + q τ = m)
    (hε : ∀ τ a, ε τ a = decide ((a : ℕ) < p τ)) (hap : ∀ τ a b, a ≤ b → b < p τ → ap τ b ≤ ap τ a)
    (ham : ∀ τ a b, a ≤ b → b < q τ → am τ b ≤ am τ a) (d : D.what₂.Tau → Fin m → ℂ) (hd : ∀ τ a, d τ a ≠ 0) :
    fact ε x₁ x₂ x₃ (fun τ => diagonal (d τ)) (fun _ => 1) (delta p q ap am : PolF D m n) =
      (∏ τ, ∏ a, d τ a ^ (if (a : ℕ) < p τ then (ap τ a : ℤ) + x₁ τ else -(am τ (a - p τ) : ℤ) + x₂ τ)) •
        (delta p q ap am : PolF D m n) := by
  have h := DeltaEig.fsub_delta D m n ε p q ap am hmn hpq hε hap ham (fun τ => diagonal (d τ)) (fun _ => 1)
    (fun τ => ⟨by
      rw [Matrix.isUnit_iff_isUnit_det, det_diagonal]
      exact (Finset.prod_ne_zero_iff.2 fun a _ => hd τ a).isUnit, by
      simp [Formalism.REAL.Jm, diagonal_mul_diagonal, mul_comm]⟩)
    (fun τ a b h => by
      obtain rfl : a = b := by
        by_contra e
        exact h (diagonal_apply_ne _ e)
      exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩)
    (fun τ => ⟨isUnit_one, fun a b h => Matrix.one_apply_ne h.ne⟩)
  rw [fact, LinearMap.smul_apply, AlgHom.toLinearMap_apply, h, smul_smul, fchar, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp only [detPlus_diagonal, detM_diagonal, det_one, _root_.one_zpow, mul_one, Matrix.one_apply_eq, Finset.prod_const_one,
    diagonal_apply_eq, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [hε]
  by_cases ha : (a : ℕ) < p τ <;> simp [ha, zpow_add₀ (hd τ a), mul_comm]

theorem pure_one {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (f : X → ℂ) : pureTensorL A f 1 = f := by
  have e : (1 : MvPolynomial ι ℂ) = MvPolynomial.basisMonomials ι ℂ 0 := by
    rw [MvPolynomial.coe_basisMonomials]; rfl
  rw [e]
  unfold pureTensorL
  rw [Module.Basis.constr_basis]
  simp [opPow]

theorem conj_mem {D : D7} {T : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel T S) (τ : D.what₂.Tau)
    {k : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hk : k ∈ Formalism.REAL.Kset (M.ε τ)) :
    (M.fr τ)⁻¹ * k * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D T τ) := by
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ))
  have hk' : kᴴ * Formalism.REAL.Jm (M.ε τ) * k = Formalism.REAL.Jm (M.ε τ) := kset_uj hk
  have h3 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  show _ᴴ * _ * _ = _
  rw [← M.fr_gram τ]
  calc _ = (M.fr τ)ᴴ * (kᴴ * (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * k) *
        M.fr τ := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1, h3, Matrix.mul_one, Matrix.mul_one, hk']

end GlobalTheory.AdTh.MinorWeight
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatSupportBoundedDenominators
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix
namespace GlobalTheory.SuppDen

variable {F : Type} [Field F] [NumberField F]

theorem norm_le_one_iff_mem (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) :
    ‖y‖ ≤ 1 ↔ y ∈ v.adicCompletionIntegers F := by
  rw [Valued.toNormedField.norm_le_one_iff, HeightOneSpectrum.mem_adicCompletionIntegers]

theorem isOpen_integral :
    IsOpen {a : FiniteAdeleRing (𝓞 F) F |
      ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun _ => Valued.isOpen_valuationSubring _)

def denSet (κ : Type) (m : ℕ) : Set (κ → FiniteAdeleRing (𝓞 F) F) :=
  {y | ∀ i (v : HeightOneSpectrum (𝓞 F)), ‖(m : v.adicCompletion F) * y i v‖ ≤ 1}

theorem natCast_mul_apply (m : ℕ) (a : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    ((m : FiniteAdeleRing (𝓞 F) F) * a) v = (m : v.adicCompletion F) * a v := by
  have hm : (m : FiniteAdeleRing (𝓞 F) F) v = (m : v.adicCompletion F) := by
    induction m with
    | zero => rfl
    | succ n ih =>
      rw [Nat.cast_succ, Nat.cast_succ]
      change (n : FiniteAdeleRing (𝓞 F) F) v + 1 = _
      rw [ih]
  simp [hm]

theorem isOpen_denSet (κ : Type) [Finite κ] (m : ℕ) : IsOpen (denSet (F := F) κ m) := by
  have h : denSet (F := F) κ m = ⋂ i, (fun y : κ → FiniteAdeleRing (𝓞 F) F =>
      (m : FiniteAdeleRing (𝓞 F) F) * y i) ⁻¹'
      {a : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F} := by
    ext y
    simp only [denSet, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, natCast_mul_apply,
      norm_le_one_iff_mem]
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_integral.preimage ((continuous_const_mul _).comp (continuous_apply i))

theorem norm_mul_le_one_of_dvd {v : HeightOneSpectrum (𝓞 F)} {m m' : ℕ} (hd : m ∣ m')
    {z : v.adicCompletion F} (hz : ‖(m : v.adicCompletion F) * z‖ ≤ 1) :
    ‖(m' : v.adicCompletion F) * z‖ ≤ 1 := by
  obtain ⟨k, rfl⟩ := hd
  rw [Nat.cast_mul, mul_comm (m : v.adicCompletion F), mul_assoc, norm_mul]
  exact mul_le_one₀ (GlobalTheory.SmoothForms.denom_norm_natCast_le_one v k) (norm_nonneg _) hz

theorem denSet_mono (κ : Type) {m m' : ℕ} (hd : m ∣ m') :
    denSet (F := F) κ m ⊆ denSet κ m' :=
  fun _ hy i v => norm_mul_le_one_of_dvd hd (hy i v)

theorem exists_denom (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ d : ℕ, 0 < d ∧ ∀ v : HeightOneSpectrum (𝓞 F), ‖(d : v.adicCompletion F) * a v‖ ≤ 1 := by
  have hf : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => max 1 ‖a v‖₊).Finite := by
    apply (Filter.eventually_cofinite.1 a.2).subset
    intro v hv
    simp only [Function.mem_mulSupport] at hv
    intro hmem
    apply hv
    have : ‖a v‖ ≤ 1 := (norm_le_one_iff_mem v _).2 hmem
    exact max_eq_left (by exact_mod_cast this)
  obtain ⟨d, hd, -, h⟩ := GlobalTheory.SmoothForms.denom_global (F := F)
    (fun v => max 1 ‖a v‖₊) (fun v => le_max_left _ _) hf
  exact ⟨d, hd, fun v => h v _ (le_max_right _ _)⟩

theorem exists_mem_denSet (κ : Type) [Fintype κ] (y : κ → FiniteAdeleRing (𝓞 F) F) :
    ∃ m : ℕ, 0 < m ∧ y ∈ denSet κ m := by
  classical
  choose d hd h using fun i => exists_denom (y i)
  exact ⟨∏ i, d i, Finset.prod_pos fun i _ => hd i, fun i v =>
    norm_mul_le_one_of_dvd (Finset.dvd_prod_of_mem d (Finset.mem_univ i)) (h i v)⟩

theorem support_bounded_denominators {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ M : ℕ, 0 < M ∧ ∀ x : κ → AF F, g (fun i => (x i).2) ≠ 0 →
      ∀ i v, ‖(M : Fv F v) * evFin F v (x i)‖ ≤ 1 := by
  classical
  have hK : IsCompact (tsupport g) := hg.2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun n : ℕ => denSet (F := F) κ (n + 1))
    (fun n => isOpen_denSet κ _) (fun y _ => by
      obtain ⟨m, hm, hy⟩ := exists_mem_denSet κ y
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hm
      exact Set.mem_iUnion.2 ⟨n, by simpa using hy⟩)
  refine ⟨∏ n ∈ t, (n + 1), Finset.prod_pos fun n _ => n.succ_pos, fun x hx i v => ?_⟩
  have hy : (fun i => (x i).2) ∈ tsupport g := subset_tsupport _ hx
  obtain ⟨n, hn, hyn⟩ := Set.mem_iUnion₂.1 (ht hy)
  exact denSet_mono κ (Finset.dvd_prod_of_mem (fun n : ℕ => n + 1) hn) hyn i v

end GlobalTheory.SuppDen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineContinuous
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped ContDiff

namespace GlobalTheory.RealLineCont

theorem continuous_of_isRealLine : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (γ : ℝ → GAd σ J), IsRealLine σ J γ → Continuous γ := by
  intro F E _ _ _ _ _ σ h n J γ ⟨w, τ, Z, _, hy⟩
  choose y hγ hy using hy
  have hc : Continuous y := by
    rw [(GlobalTheory.Orb.isEmbedding_archMat J h τ).continuous_iff]
    have e : (GlobalTheory.Orb.matCoord (GlobalTheory.Orb.archMat σ J τ) ∘ y) = fun t i j => NormedSpace.exp (t • Z) i j := by
      funext t i j; simp only [Function.comp_apply, GlobalTheory.Orb.matCoord, hy t]
    rw [e]
    have hexp : Continuous fun t : ℝ => NormedSpace.exp (t • Z) := by
      letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
      letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
      letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
      exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
    exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp ((continuous_apply i).comp hexp)
  have : γ = fun t => embArch σ J w (y t) := funext hγ
  rw [this]
  exact (continuous_embArch σ J w).comp hc

end GlobalTheory.RealLineCont
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementInfinitePoints
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

noncomputable section
namespace GlobalTheory.LeviArch
open GlobalTheory.LeviPlane
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.LeviArch
end
end
