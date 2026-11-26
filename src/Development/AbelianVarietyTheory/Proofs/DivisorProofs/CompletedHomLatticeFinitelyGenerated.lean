module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleTwist
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VacuumCharacterDeterminant
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeFinitelyGenerated
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeFinitelyGenerated
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatFinGen

open GlobalTheory.LatVac GlobalTheory.LatFinMod

theorem pair_smul_tmul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (α : Af F) (x : E) :
    algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 α) * (pairA F 0 1 ⊗ₜ[F] x) = pairA F 0 α ⊗ₜ[F] x := by
  have hp : pairA F 0 α * pairA F 0 1 = pairA F 0 α := Prod.ext (mul_zero _) (mul_one _)
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  exact congrArg (· ⊗ₜ[F] x) hp

theorem smul_finTens_one {D : D7} {m n : ℕ} (α : Af D.host.F) (M : Matrix (Fin m) (Fin n) D.host.E) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • finTens 1 M = finTens α M :=
  Matrix.ext fun i j => pair_smul_tmul α (M i j)

theorem latO_finitely_generated : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∃ G : Set (WO S T), G.Finite ∧ (∀ u ∈ G, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ U : AddSubgroup (WO S T), (∀ α ∈ intAf D.host.F, ∀ u ∈ G, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u ∈ U) → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u ∈ U := by
  intro D S T ΛS ΛT hS hT
  obtain ⟨A, hA, hA1, hA2⟩ := exists_int_gen (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl _)
  obtain ⟨B, hB, hB1, hB2⟩ := exists_int_gen ΛS hS.1.fg
  obtain ⟨C, hC, hC1, hC2⟩ := exists_int_gen ΛT hT.1.fg
  refine ⟨finTens 1 '' ((fun p : _ × _ × _ => genMap S T p.1 p.2.1 p.2.2) '' (A ×ˢ B ×ˢ C)),
    ((hA.prod (hB.prod hC)).image _).image _, ?_, fun U hU u hu => ?_⟩
  · rintro _ ⟨_, ⟨⟨a, s, t⟩, ⟨ha, hs, ht⟩, rfl⟩, rfl⟩
    refine AddSubgroup.subset_closure ⟨1, fun v => ?_, fun v hv => absurd trivial hv,
      a, hA1 ha, s, hB1 hs, t, hC1 ht, rfl⟩
    rw [map_one]; exact one_mem _
  · refine (AddSubgroup.closure_le U).2 ?_ hu
    rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
    let φ : Matrix (Fin T.rank) (Fin S.rank) D.host.E →ₗ[ℤ] WO S T :=
      (AddMonoidHom.mk' (finTens α) (finTens_add α)).toIntLinearMap
    have hle : Submodule.span ℤ ((fun p : _ × _ × _ => genMap S T p.1 p.2.1 p.2.2) '' (A ×ˢ B ×ˢ C)) ≤
        U.toIntSubmodule.comap φ := by
      refine Submodule.span_le.2 fun M hM => ?_
      have := hU α hα _ ⟨M, hM, rfl⟩
      rw [smul_finTens_one] at this
      exact this
    exact hle (genMap_mem_span S T (hA2 _ ha) (hB2 _ hs) (hC2 _ ht))

end GlobalTheory.LatFinGen

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeFinitelyGeneratedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedHomLattice_finitelyGenerated : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∃ G : Set (WO S T), G.Finite ∧ (∀ u ∈ G, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ U : AddSubgroup (WO S T), (∀ α ∈ intAf D.host.F, ∀ u ∈ G, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u ∈ U) → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u ∈ U := by
  first | exact @GlobalTheory.LatFinGen.latO_finitely_generated | exact GlobalTheory.LatFinGen.latO_finitely_generated | (intros; apply GlobalTheory.LatFinGen.latO_finitely_generated <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeMultipleMemOpenLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeMultipleMemOpenLevel
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatLevel

open GlobalTheory.SplitScalar

variable {D : D7}

theorem exists_nsmul_smul_mem {m n : ℕ} (U : AddSubgroup (Mx D m n)) (hU : IsOpen (U : Set (Mx D m n)))
    (y : Mx D m n) : ∃ N : ℕ, 0 < N ∧ ∀ α ∈ intAf D.host.F,
      N • (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • y) ∈ U := by
  let φ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F → Mx D m n := fun α => Matrix.of fun i j => pairA D.host.F 0 α • y i j
  have hp : Continuous fun α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F => pairA D.host.F 0 α :=
    continuous_const.prodMk continuous_id
  have hφ : Continuous φ := continuous_pi fun i => continuous_pi fun j => hp.smul continuous_const
  have h0 : φ 0 = 0 := Matrix.ext fun i j => zero_smul (AF D.host.F) (y i j)
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele D.host.F (φ ⁻¹' U)
    (hφ.continuousAt.preimage_mem_nhds (hU.mem_nhds (h0 ▸ U.zero_mem)))
  refine ⟨N, hN, fun α hα => ?_⟩
  have h1 : φ (N • α) ∈ U := h α hα
  have h2 : φ (N • α) = N • (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • y) := by
    refine Matrix.ext fun i j => ?_
    have e1 : pairA D.host.F 0 (N • α) = N • pairA D.host.F 0 α :=
      Prod.ext (show (0 : Ainf D.host.F) = N • 0 by rw [smul_zero]) rfl
    show pairA D.host.F 0 (N • α) • y i j = N • (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * y i j)
    rw [e1, smul_assoc, Algebra.smul_def (pairA D.host.F 0 α)]
  rwa [h2] at h1

def actHom (S T : HSp D) (g : GA D S) (h : GA D T) : WO S T →+ WO S T :=
  AddMonoidHom.mk' (actO S T g h) fun x y => by
    unfold actO
    rw [Matrix.mul_add, Matrix.add_mul]

theorem continuous_actO (S T : HSp D) (g : GA D S) (h : GA D T) : Continuous (actO S T g h) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [actO, Matrix.mul_apply]
  refine continuous_finsetSum _ fun k _ => Continuous.mul (continuous_finsetSum _ fun l _ =>
    continuous_const.mul ?_) continuous_const
  exact (continuous_apply k).comp (continuous_apply l)

theorem actO_map_inf (S T : HSp D) (g : GA D S) (h : GA D T) {u : WO S T} (hu : u.map (infPart D) = 0) :
    (actO S T g h u).map (infPart D) = 0 := by
  unfold actO
  rw [Matrix.map_mul, Matrix.map_mul, hu, Matrix.mul_zero, Matrix.zero_mul]

def finSat {m n : ℕ} (L : AddSubgroup (Mx D m n)) : AddSubgroup (Mx D m n) :=
  (L.map (finPart D).toAddMonoidHom.mapMatrix).comap (finPart D).toAddMonoidHom.mapMatrix

theorem mem_finSat {m n : ℕ} (L : AddSubgroup (Mx D m n)) (x : Mx D m n) :
    x ∈ finSat L ↔ ∃ l ∈ L, Matrix.map (x - (1 : ℕ) • l) (finPart D) = 0 := by
  have key : ∀ l : Mx D m n, Matrix.map (x - (1 : ℕ) • l) (finPart D) = 0 ↔
      (finPart D).toAddMonoidHom.mapMatrix l = (finPart D).toAddMonoidHom.mapMatrix x := by
    intro l
    rw [one_smul, eq_comm (b := (finPart D).toAddMonoidHom.mapMatrix x), ← sub_eq_zero (a := (finPart D).toAddMonoidHom.mapMatrix x), ← map_sub]
    rfl
  simp only [key]
  rfl

theorem level_of_generators : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ G : Set (WO S T), G.Finite ∧ (∀ u ∈ G, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ U : AddSubgroup (WO S T), (∀ α ∈ intAf D.host.F, ∀ u ∈ G, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u ∈ U) → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u ∈ U) → (∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), N • u ∈ U) ∧ ∀ (g : GA D S) (h : GA D T), ∃ N : ℕ, 0 < N ∧ ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), N • actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  intro D S T ΛS ΛT hS hT ⟨G, hG, _, hgen⟩
  have h1 : ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ N : ℕ, 0 < N ∧
      ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        N • u ∈ U := by
    intro U hU
    choose M hM hMU using fun y : WO S T => exists_nsmul_smul_mem U hU y
    refine ⟨∏ y ∈ hG.toFinset, M y, Finset.prod_pos fun y _ => hM y, ?_⟩
    refine hgen (U.comap (nsmulAddMonoidHom (∏ y ∈ hG.toFinset, M y))) fun α hα u hu => ?_
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem M (hG.mem_toFinset.2 hu)
    show (∏ y ∈ hG.toFinset, M y) • _ ∈ U
    rw [hc, mul_comm, mul_smul]
    exact U.nsmul_mem (hMU u α hα) c
  refine ⟨h1, fun g h => ?_⟩
  have hop : IsOpen (finSat (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) : Set (WO S T)) := by
    convert GlobalTheory.LatOpen.isOpen_nsmul_latO D S T ΛS ΛT hS hT 1 one_pos using 1
    exact Set.ext fun x => mem_finSat _ x
  obtain ⟨N, hN, hNU⟩ := h1 ((finSat _).comap (actHom S T g h)) (hop.preimage (continuous_actO S T g h))
  refine ⟨N, hN, fun u hu => ?_⟩
  have h2 : actHom S T g h (N • u) ∈ finSat _ := hNU u hu
  obtain ⟨l, hl, hl0⟩ := (mem_finSat _ _).1 h2
  have h3 : (actHom S T g h (N • u)).map (infPart D) = 0 :=
    actO_map_inf S T g h (latO_fin (AddSubgroup.nsmul_mem _ hu N))
  have h4 := latO_fin hl
  have h5 : actHom S T g h (N • u) = l := by
    refine Matrix.ext fun i j => adele_ext ?_ ?_
    · exact (congrFun (congrFun h3 i) j).trans (congrFun (congrFun h4 i) j).symm
    · have h6 : finPart D (actHom S T g h (N • u) i j - (1 : ℕ) • l i j) = 0 := congrFun (congrFun hl0 i) j
      rwa [one_smul, RingHom.map_sub, sub_eq_zero] at h6
  rw [map_nsmul] at h5
  exact h5 ▸ hl

end GlobalTheory.LatLevel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeMultipleMemOpenLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedHomLattice_multiple_mem_open_level : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ G : Set (WO S T), G.Finite ∧ (∀ u ∈ G, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ U : AddSubgroup (WO S T), (∀ α ∈ intAf D.host.F, ∀ u ∈ G, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u ∈ U) → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u ∈ U) → (∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), N • u ∈ U) ∧ ∀ (g : GA D S) (h : GA D T), ∃ N : ℕ, 0 < N ∧ ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), N • actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  first | exact @GlobalTheory.LatLevel.level_of_generators | exact GlobalTheory.LatLevel.level_of_generators | (intros; apply GlobalTheory.LatLevel.level_of_generators <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairAction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SymplOInv

theorem sum_four_eq_trace {A : Type} [CommRing A] {m n : ℕ} (σ : A →+* A) (P : Matrix (Fin n) (Fin n) A)
    (Q : Matrix (Fin m) (Fin m) A) (x y : Matrix (Fin m) (Fin n) A) :
    ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ (y c b) * Q c d * x d a = (P * (y.map σ)ᵀ * Q * x).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Eq.symm ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]

theorem sum_unitary {A : Type} [CommRing A] {m n : ℕ} (σ : A →+* A) (Q g : Matrix (Fin m) (Fin m) A)
    (P P' k : Matrix (Fin n) (Fin n) A) (hP : P * P' = 1) (hg : (g.map σ)ᵀ * Q * g = Q)
    (hk : (k.map σ)ᵀ * P' * k = P') (x y : Matrix (Fin m) (Fin n) A) :
    ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ ((g * y * k) c b) * Q c d * (g * x * k) d a =
      ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ (y c b) * Q c d * x d a := by
  have h1 : (P * (k.map σ)ᵀ * P') * k = 1 := by
    rw [Matrix.mul_assoc P, Matrix.mul_assoc P, hk, hP]
  have h2 : k * (P * (k.map σ)ᵀ * P') = 1 := mul_eq_one_comm.1 h1
  have hP' : P' * P = 1 := mul_eq_one_comm.1 hP
  have hk' : k * P * (k.map σ)ᵀ = P := by
    calc k * P * (k.map σ)ᵀ = k * P * (k.map σ)ᵀ * (P' * P) := by rw [hP', Matrix.mul_one]
      _ = (k * (P * (k.map σ)ᵀ * P')) * P := by simp only [Matrix.mul_assoc]
      _ = P := by rw [h2, Matrix.one_mul]
  have e : P * ((g * y * k).map σ)ᵀ * Q * (g * x * k) =
      (P * (k.map σ)ᵀ * ((y.map σ)ᵀ * ((g.map σ)ᵀ * Q * g) * x)) * k := by
    simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [sum_four_eq_trace, sum_four_eq_trace, e, hg, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc k, hk']
  simp only [Matrix.mul_assoc]

theorem hO_actO {D : D7} (S T : HSp D) (g : GA D S) (h : GA D T) (x y : WO S T) :
    hO S T (actO S T g h x) (actO S T g h y) = hO S T x y := by
  have h1 : S.gram⁻¹.map (incA D) * S.gram.map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S)]
    exact Matrix.map_one _ (incA D).map_zero (incA D).map_one
  exact sum_unitary (cA D) (T.gram.map (incA D)) (mt T h) (S.gram⁻¹.map (incA D)) (S.gram.map (incA D)) (mt S g⁻¹)
    h1 h.2 (g⁻¹).2 x y

theorem symplO_actO : ∀ (D : D7) (S T : HSp D) (g : GA D S) (h : GA D T) (x y : WO S T), symplO S T (actO S T g h x) (actO S T g h y) = symplO S T x y := by
  intro D S T g h x y
  unfold symplO
  rw [hO_actO]

end GlobalTheory.SymplOInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairActionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticForm_unitaryPairAction : ∀ (D : D7) (S T : HSp D) (g : GA D S) (h : GA D T) (x y : WO S T), symplO S T (actO S T g h x) (actO S T g h y) = symplO S T x y := by
  first | exact @GlobalTheory.SymplOInv.symplO_actO | exact GlobalTheory.SymplOInv.symplO_actO | (intros; apply GlobalTheory.SymplOInv.symplO_actO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryGroupCharacterOfHeckeChar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryGroupCharacterOfHeckeChar
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDetCharacter

def cut {R : Type} [CommRing R] (ε : R) (h : ε * ε = ε) : R →* R where
  toFun u := (1 - ε) + ε * u
  map_one' := by ring
  map_mul' u v := by linear_combination (-(1 - u - v + u * v)) * h

theorem mul_det_sub_one {R : Type} [CommRing R] {n : ℕ} (a : R) (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, a * (M - 1) i j = 0) : a * (M.det - 1) = 0 := by
  let I : Ideal R := LinearMap.ker (LinearMap.mul R R a)
  have h1 : (Ideal.Quotient.mk I).mapMatrix M = (Ideal.Quotient.mk I).mapMatrix 1 := by
    ext i j
    exact Ideal.Quotient.eq.2 (h i j)
  have h2 := congrArg Matrix.det h1
  rw [← RingHom.map_det, ← RingHom.map_det, Matrix.det_one] at h2
  exact Ideal.Quotient.eq.1 h2

theorem cut_eq {R : Type} [CommRing R] {ε e f d : R} (a1 : ε * e = e)
    (a2 : ε * f = 0) (hd : (1 - (e + f)) * (d - 1) = 0) : (1 - ε) + ε * d = e * d + (1 - e) := by
  linear_combination ε * hd + (d - 1) * (a1 + a2)

theorem cut_mul {R : Type} [CommRing R] {ε e f d d' : R} (e2 : f * f = f) (a1 : ε * e = 0)
    (a2 : ε * f = f) (hd : (1 - (e + f)) * (d - 1) = 0) (e3 : d * d' = 1) :
    ((1 - ε) + ε * d) * (f * d' + (1 - f)) = 1 := by
  have e4 : ε * (d - 1) = f * (d - 1) := by
    linear_combination ε * hd + (d - 1) * (a1 + a2)
  linear_combination (1 + f * (d' - 1)) * e4 + (d - 1) * (d' - 1) * e2 + f * e3

variable {D : D7}

theorem det_mul_conj (V : HSp D) (g : GA D V) :
    (Formalism.L2.Theta.mt V g).det * cA D (Formalism.L2.Theta.mt V g).det = 1 := by
  have h : ((Formalism.L2.Theta.mt V g).map (cA D))ᵀ * V.gram.map (incA D) * Formalism.L2.Theta.mt V g = V.gram.map (incA D) := g.2
  have hu := (GlobalTheory.LatVac.gram_det_isUnit V).map (incA D)
  rw [RingHom.map_det, RingHom.mapMatrix_apply] at hu
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply (cA D), ← RingHom.map_det] at h2
  refine hu.mul_left_cancel ?_
  linear_combination h2

theorem algebraMap_norm (z : AE D) :
    algebraMap (AF D.host.F) (AE D) (Algebra.norm (AF D.host.F) z) = z * cA D z := by
  have hx : ∃ x, D.sp.cm.sig x ≠ x := by
    by_contra h
    push Not at h
    have hs : Function.Surjective (algebraMap D.host.F D.host.E) := fun x => (D.sp.cm.fixed x).1 (h x)
    have h1 : Module.finrank D.host.F D.host.E = 1 := by
      rw [← (LinearEquiv.ofBijective (Algebra.linearMap D.host.F D.host.E)
        ⟨(algebraMap D.host.F D.host.E).injective, hs⟩).finrank_eq, Module.finrank_self]
    have h2 := D.sp.cm.deg2
    omega
  obtain ⟨δ, -, h⟩ := GlobalTheory.QuadNormBase.norm_form D.host.F D.host.E D.sp.cm.sig D.sp.cm.deg2 (fun x => star_star x) hx
  obtain ⟨x, y, e1, e2⟩ := (h (AF D.host.F)).1 z
  rw [e1, e2]

theorem char_norm {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (x x' : (AE D)ˣ)
    (hx : (x' : AE D) = cA D x) : χ x * χ x' = 1 := by
  obtain ⟨⟨η, hη⟩, h1⟩ := h
  have e : x * x' = idF D (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) x) := by
    refine Units.ext ?_
    rw [Units.val_mul, hx]
    exact (algebraMap_norm (x : AE D)).symm
  rw [← map_mul, e, h1 η hη, hη.2.2.1 x, one_pow]

theorem char_eq_of_mul_conj {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (y x : (AE D)ˣ)
    (hy : (y : AE D) * cA D x = 1) : χ y = χ x := by
  obtain ⟨x', hx'⟩ : IsUnit (cA D x) := x.isUnit.map (cA D)
  have hc := char_norm h x x' hx'
  have h1 : y * x' = 1 := Units.ext (by rw [Units.val_mul, hx', hy, Units.val_one])
  have h2 := congrArg χ h1
  rw [map_mul, map_one, ← hc] at h2
  exact mul_right_cancel h2

def cutDet (ε : AE D) (h : ε * ε = ε) (V : HSp D) : GA D V →* (AE D)ˣ :=
  (Units.map (cut ε h)).comp ((Matrix.GeneralLinearGroup.det (n := Fin V.rank) (R := AE D)).comp (matHom V))

theorem cutDet_val (ε : AE D) (h : ε * ε = ε) (V : HSp D) (g : GA D V) :
    (cutDet ε h V g : AE D) = (1 - ε) + ε * (Formalism.L2.Theta.mt V g).det := rfl

theorem cutDet_eq_one (ε : AE D) (h : ε * ε = ε) (V : HSp D) (g : GA D V)
    (hg : ∀ i j, ε * (Formalism.L2.Theta.mt V g - 1) i j = 0) : cutDet ε h V g = 1 := by
  refine Units.ext ?_
  rw [cutDet_val, Units.val_one]
  linear_combination mul_det_sub_one ε _ hg

theorem continuous_cutDet (ε : AE D) (h : ε * ε = ε) (V : HSp D) : Continuous (cutDet ε h V) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have h0 : Continuous fun g : GA D V => matHom V g := continuous_subtype_val
  have h1 : Continuous (Formalism.L2.Theta.mt V) := Units.continuous_val.comp h0
  have h2 : Continuous fun g : GA D V => Formalism.L2.Theta.mt V g⁻¹ := by
    have e : (fun g : GA D V => Formalism.L2.Theta.mt V g⁻¹) = fun g => ((matHom V g)⁻¹).1 := by
      funext g
      unfold Formalism.L2.Theta.mt
      rw [map_inv]
    rw [e]
    exact Units.continuous_coe_inv.comp h0
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_const.add (continuous_const.mul h1.matrix_det)
  · simp only [← map_inv, cutDet_val]
    exact continuous_const.add (continuous_const.mul h2.matrix_det)

theorem cutDet_real (ε : AE D) (h1 : ε * ε = ε) (h3 : infPart D ε = 0) (V : HSp D) (g : GA D V) (hg : g ∈ GinfC V) :
    cutDet ε h1 V g = 1 := by
  refine cutDet_eq_one ε h1 V g fun i j => ?_
  have hm : (Formalism.L2.Theta.mt V g).map (finPart D) = 1 := congrArg Units.val (show finHom V g = 1 from hg)
  have hf : finPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
    have e1 : finPart D (Formalism.L2.Theta.mt V g i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j :=
      congrFun (congrFun hm i) j
    rw [Matrix.sub_apply, RingHom.map_sub, e1, sub_eq_zero]
    by_cases e : i = j
    · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]
  exact GlobalTheory.SplitScalar.adele_ext (by rw [RingHom.map_mul, h3, zero_mul, RingHom.map_zero])
    (by rw [RingHom.map_mul, hf, mul_zero, RingHom.map_zero])

theorem det_supp {e : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt e V g) :
    (1 - (e + cA D e)) * ((Formalism.L2.Theta.mt V g).det - 1) = 0 :=
  mul_det_sub_one _ _ fun i j => by rw [sub_mul, one_mul, hg i j, sub_self]

set_option maxHeartbeats 1000000 in
theorem cutDet_same (ε : AE D) (h1 : ε * ε = ε) {e : AE D} (a1 : ε * e = e) (a2 : ε * cA D e = 0) {V : HSp D} {g : GA D V}
    {x : (AE D)ˣ} (hg : SuppAt e V g) (hx : IsDetAt e V g x) : cutDet ε h1 V g = x := by
  have hx' : (x : AE D) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) := hx
  refine Units.ext ?_
  rw [cutDet_val, hx']
  exact cut_eq a1 a2 (det_supp hg)

set_option maxHeartbeats 1000000 in
theorem cutDet_conj (ε : AE D) (h1 : ε * ε = ε) {e : AE D} (he : e * e = e) (a1 : ε * e = 0) (a2 : ε * cA D e = cA D e)
    {V : HSp D} {g : GA D V} {x : (AE D)ˣ} (hg : SuppAt e V g) (hx : IsDetAt e V g x) :
    (cutDet ε h1 V g : AE D) * cA D x = 1 := by
  have hx' : (x : AE D) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) := hx
  have e2 : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have e5 : cA D x = cA D e * cA D (Formalism.L2.Theta.mt V g).det + (1 - cA D e) := by
    rw [hx', RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_sub, RingHom.map_one]
  rw [cutDet_val, e5]
  exact cut_mul e2 a1 a2 (det_supp hg) (det_mul_conj V g)


set_option maxHeartbeats 1000000 in
theorem exists_character : ∀ (D : D7) (ε : AE D), (ε * ε = ε ∧ ε * cA D ε = 0 ∧ infPart D ε = 0 ∧ (∀ e, IsSplitIdem D e → (ε * e = e ∧ ε * cA D e = 0) ∨ (ε * e = 0 ∧ ε * cA D e = cA D e)) ∧ ∀ v η, NonSplitAt D v η → algebraMap (AF D.host.F) (AE D) η * ε = 0) → ∀ (V : HSp D) (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → ResEta D χ n → ∃ c : GA D V →* Circle, Continuous c ∧ (∀ g ∈ GinfC V, c g = 1) ∧ (∀ v η, NonSplitAt D v η → ∀ g, SuppPl η V g → c g = 1) ∧ ∀ e, IsSplitIdem D e → ∀ g x, SuppAt e V g → IsDetAt e V g x → c g = χ x := by
  rintro D ε ⟨h1, -, h3, h4, h5⟩ V χ n hχ hres
  refine ⟨χ.comp (cutDet ε h1 V), hχ.1.comp (continuous_cutDet ε h1 V), fun g hg => ?_, fun v η hv g hg => ?_,
    fun e he g x hg hx => ?_⟩
  · rw [MonoidHom.comp_apply, cutDet_real ε h1 h3 V g hg, map_one]
  · rw [MonoidHom.comp_apply, cutDet_eq_one ε h1 V g fun i j => ?_, map_one]
    rw [← hg i j, ← mul_assoc, mul_comm ε, h5 v η hv, zero_mul]
  · rw [MonoidHom.comp_apply]
    rcases h4 e he with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · rw [cutDet_same ε h1 a1 a2 hg hx]
    · exact char_eq_of_mul_conj hres _ x (cutDet_conj ε h1 he.1 a1 a2 hg hx)

end GlobalTheory.SplitDetCharacter
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryGroupCharacterOfHeckeCharStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryGroup_character_of_heckeChar : ∀ (D : D7) (ε : AE D), (ε * ε = ε ∧ ε * cA D ε = 0 ∧ infPart D ε = 0 ∧ (∀ e, IsSplitIdem D e → (ε * e = e ∧ ε * cA D e = 0) ∨ (ε * e = 0 ∧ ε * cA D e = cA D e)) ∧ ∀ v η, NonSplitAt D v η → algebraMap (AF D.host.F) (AE D) η * ε = 0) → ∀ (V : HSp D) (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → ResEta D χ n → ∃ c : GA D V →* Circle, Continuous c ∧ (∀ g ∈ GinfC V, c g = 1) ∧ (∀ v η, NonSplitAt D v η → ∀ g, SuppPl η V g → c g = 1) ∧ ∀ e, IsSplitIdem D e → ∀ g x, SuppAt e V g → IsDetAt e V g x → c g = χ x := by
  first | exact @GlobalTheory.SplitDetCharacter.exists_character | exact GlobalTheory.SplitDetCharacter.exists_character | (intros; apply GlobalTheory.SplitDetCharacter.exists_character <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyScaledInverse
open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial

namespace GlobalTheory

theorem charpoly_smul_inv_of_charpoly_eq_prod (n : ℕ) (M : GL (Fin n) ℂ) (t : ℂ) (s : Multiset ℂ)
    (h : (M : Matrix (Fin n) (Fin n) ℂ).charpoly = (s.map fun a => X - C a).prod) :
    (t • ((M⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)).charpoly
      = (s.map fun a => X - C (t * a⁻¹)).prod := by
  set A : Matrix (Fin n) (Fin n) ℂ := (M : Matrix (Fin n) (Fin n) ℂ) with hA
  set B : Matrix (Fin n) (Fin n) ℂ := ((M⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) with hB
  have hAB : A * B = 1 := by simp [hA, hB]
  have hcard : Multiset.card s = n := by
    have h1 := Matrix.charpoly_natDegree_eq_dim A
    rw [h, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card] at h1
    simpa using h1
  have hev : ∀ y : ℂ, (Matrix.scalar (Fin n) y - A).det = (s.map fun a => y - a).prod := by
    intro y
    rw [← Matrix.eval_charpoly, h, Polynomial.eval_multiset_prod, Multiset.map_map]
    simp
  have hdet : A.det * B.det = 1 := by rw [← Matrix.det_mul, hAB, Matrix.det_one]
  have hneg : (-A).det = (s.map fun a => -a).prod := by simpa using hev 0
  have hne : (-A).det ≠ 0 := by
    rw [Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (left_ne_zero_of_mul_eq_one hdet)
  have hs : ∀ a ∈ s, a ≠ 0 := by
    intro a ha h0
    apply hne
    rw [hneg]
    exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨a, ha, by simp [h0]⟩)
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (s := ({0} : Set ℂ)ᶜ) ?_ (Set.finite_singleton _).infinite_compl
  intro x hx
  have hx0 : x ≠ 0 := hx
  simp only [Set.mem_setOf_eq]
  rw [Matrix.eval_charpoly, Polynomial.eval_multiset_prod, Multiset.map_map]
  apply mul_left_cancel₀ hne
  have key : (-A) * (Matrix.scalar (Fin n) x - t • B)
      = x • (Matrix.scalar (Fin n) (t / x) - A) := by
    rw [Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
      ← Matrix.smul_one_eq_diagonal, mul_sub, Matrix.mul_smul, Matrix.mul_smul, neg_mul, neg_mul, hAB, mul_one,
      smul_sub, smul_smul, mul_div_cancel₀ _ hx0, smul_neg, smul_neg]
    abel
  rw [← Matrix.det_mul, key, Matrix.det_smul, hev, hneg, ← Multiset.prod_map_mul, Fintype.card_fin,
    ← hcard, ← Multiset.prod_replicate, ← Multiset.map_const', ← Multiset.prod_map_mul]
  congr 1
  apply Multiset.map_congr rfl
  intro a ha
  have := hs a ha
  simp only [Function.comp, eval_sub, eval_X, eval_C]
  field_simp
  ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHeckeOpFullDualLab
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLeftCosetsDoubleCosetInvEq
open MeasureTheory

namespace GlobalTheory

theorem card_leftCosets_doubleCoset_inv_eq : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (ν : Measure G) [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] (J : Subgroup G) (α : G) (R R' : Finset G), MeasurableSet (J : Set G) → ν J ≠ 0 → ν J ≠ ⊤ → (∀ γ ∈ R, ∃ k₁ ∈ J, ∃ k₂ ∈ J, γ = k₁ * α * k₂) → (∀ x : G, (∃ k₁ ∈ J, ∃ k₂ ∈ J, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ J) → (∀ γ ∈ R', ∃ k₁ ∈ J, ∃ k₂ ∈ J, γ = k₁ * α⁻¹ * k₂) → (∀ x : G, (∃ k₁ ∈ J, ∃ k₂ ∈ J, x = k₁ * α⁻¹ * k₂) → ∃! γ, γ ∈ R' ∧ γ⁻¹ * x ∈ J) → R.card = R'.card := by
  intro G _ _ _ ν _ _ J α R R' hJ h0 htop hR hRu hR' hR'u
  set S : Set G := {x | ∃ k₁ ∈ J, ∃ k₂ ∈ J, x = k₁ * α * k₂} with hS
  have hA : ∀ γ ∈ R, ∀ x, γ⁻¹ * x ∈ J → x ∈ S := by
    intro γ hγ x hx
    obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := hR γ hγ
    exact ⟨k₁, h₁, k₂ * ((k₁ * α * k₂)⁻¹ * x), J.mul_mem h₂ hx, by group⟩
  have hB : ∀ γ ∈ R', ∀ x, x * γ ∈ J → x ∈ S := by
    intro γ hγ x hx
    obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := hR' γ hγ
    exact ⟨x * (k₁ * α⁻¹ * k₂) * k₂⁻¹, J.mul_mem hx (J.inv_mem h₂), k₁⁻¹, J.inv_mem h₁, by group⟩
  have hBu : ∀ x ∈ S, ∃! γ, γ ∈ R' ∧ x * γ ∈ J := by
    rintro x ⟨k₁, h₁, k₂, h₂, hx⟩
    have := hR'u x⁻¹ ⟨k₂⁻¹, J.inv_mem h₂, k₁⁻¹, J.inv_mem h₁, by rw [hx]; group⟩
    simpa only [← mul_inv_rev, J.inv_mem_iff] using this
  have e1 : S = ⋃ γ ∈ R, (fun x => γ⁻¹ * x) ⁻¹' (J : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop]
    exact ⟨fun hx => (hRu x hx).exists, fun ⟨γ, h, h'⟩ => hA γ h x h'⟩
  have e2 : S = ⋃ γ ∈ R', (fun x => x * γ) ⁻¹' (J : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop]
    exact ⟨fun hx => (hBu x hx).exists, fun ⟨γ, h, h'⟩ => hB γ h x h'⟩
  have m1 : ν S = R.card * ν J := by
    rw [e1, measure_biUnion_finset]
    · simp only [measure_preimage_mul, Finset.sum_const, nsmul_eq_mul]
    · intro a ha b hb hab
      rw [Function.onFun, Set.disjoint_left]
      intro x hxa hxb
      exact hab ((hRu x (hA a ha x hxa)).unique ⟨ha, hxa⟩ ⟨hb, hxb⟩)
    · intro b _
      exact measurable_const_mul _ hJ
  have m2 : ν S = R'.card * ν J := by
    rw [e2, measure_biUnion_finset]
    · simp only [measure_preimage_mul_right, Finset.sum_const, nsmul_eq_mul]
    · intro a ha b hb hab
      rw [Function.onFun, Set.disjoint_left]
      intro x hxa hxb
      exact hab ((hBu x (hB a ha x hxa)).unique ⟨ha, hxa⟩ ⟨hb, hxb⟩)
    · intro b _
      exact measurable_mul_const _ hJ
  have := (ENNReal.mul_left_inj h0 htop).1 (m1.symm.trans m2)
  exact_mod_cast this

end GlobalTheory
end

namespace GlobalTheory.HeckeDual

section Group

open MeasureTheory

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

theorem exists_rep (K : Subgroup H) (ho : IsOpen (K : Set H)) (hc : IsCompact (K : Set H)) (b : H) :
    ∃ R : Finset H, (∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * b * k₂) ∧
      ∀ x : H, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * b * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ K := by
  classical
  haveI : DiscreteTopology (H ⧸ K) := QuotientGroup.discreteTopology ho
  have hf : ((fun k : H => ((k * b : H) : H ⧸ K)) '' (K : Set H)).Finite :=
    (hc.image (QuotientGroup.continuous_mk.comp (continuous_mul_const b))).finite_of_discrete
  refine ⟨hf.toFinset.image Quotient.out, fun γ hγ => ?_, ?_⟩
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hγ
    obtain ⟨k, hk, rfl⟩ := hf.mem_toFinset.1 hq
    obtain ⟨k', hk'⟩ := QuotientGroup.mk_out_eq_mul K (k * b)
    exact ⟨k, hk, k', k'.2, hk'⟩
  · rintro x ⟨k₁, h₁, k₂, h₂, rfl⟩
    have e : ((k₁ * b : H) : H ⧸ K) = ((k₁ * b * k₂ : H) : H ⧸ K) := (QuotientGroup.mk_mul_of_mem _ h₂).symm
    refine ⟨((k₁ * b : H) : H ⧸ K).out, ⟨Finset.mem_image_of_mem _ (hf.mem_toFinset.2 ⟨k₁, h₁, rfl⟩), ?_⟩, ?_⟩
    · rw [← QuotientGroup.eq, QuotientGroup.out_eq', e]
    · rintro γ ⟨hγ, h⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hγ
      rw [← QuotientGroup.eq, QuotientGroup.out_eq'] at h
      rw [h, e]

theorem exists_rep_inv [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (hmod : ∀ h : H, Measure.modularCharacter h = 1) {G : Type} [Group G] (ι : H →* G) (hι : Function.Injective ι)
    (K : Subgroup H) (ho : IsOpen (K : Set H)) (hc : IsCompact (K : Set H)) (KS : Set G)
    (hK : ∀ g, g ∈ KS ↔ ∃ k ∈ K, ι k = g) (a : H) (R : Finset G)
    (h1 : ∀ γ ∈ R, ∃ k₁ ∈ KS, ∃ k₂ ∈ KS, γ = k₁ * ι a * k₂)
    (h2 : ∀ x : G, (∃ k₁ ∈ KS, ∃ k₂ ∈ KS, x = k₁ * ι a * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ KS) :
    ∃ R' : Finset G, (∀ γ ∈ R', γ ∈ ι.range ∧ ∃ k₁ ∈ KS, ∃ k₂ ∈ KS, γ = k₁ * (ι a)⁻¹ * k₂) ∧
      (∀ x : G, (∃ k₁ ∈ KS, ∃ k₂ ∈ KS, x = k₁ * (ι a)⁻¹ * k₂) → ∃! γ, γ ∈ R' ∧ γ⁻¹ * x ∈ KS) ∧
      R'.card = R.card := by
  classical
  have hK' : ∀ k, ι k ∈ KS ↔ k ∈ K := fun k =>
    (hK _).trans ⟨fun ⟨k', h, e⟩ => hι e ▸ h, fun h => ⟨k, h, rfl⟩⟩
  have hdc : ∀ (b : H) (x : G), (∃ k₁ ∈ KS, ∃ k₂ ∈ KS, x = k₁ * ι b * k₂) ↔
      ∃ y, ι y = x ∧ ∃ k₁ ∈ K, ∃ k₂ ∈ K, y = k₁ * b * k₂ := fun b x => by
    constructor
    · rintro ⟨k₁, h₁, k₂, h₂, rfl⟩
      obtain ⟨l₁, g₁, rfl⟩ := (hK _).1 h₁
      obtain ⟨l₂, g₂, rfl⟩ := (hK _).1 h₂
      exact ⟨_, by rw [map_mul, map_mul], l₁, g₁, l₂, g₂, rfl⟩
    · rintro ⟨_, rfl, k₁, h₁, k₂, h₂, rfl⟩
      exact ⟨_, (hK' _).2 h₁, _, (hK' _).2 h₂, by rw [map_mul, map_mul]⟩
  obtain ⟨R', h3, h4⟩ := exists_rep K ho hc a⁻¹
  let μ : Measure H := Measure.haar
  haveI : μ.IsMulRightInvariant := ⟨fun g => by
    rw [GlobalTheory.AdelicUnimod.map_mul_right_eq, hmod, one_smul]⟩
  have hcard := GlobalTheory.card_leftCosets_doubleCoset_inv_eq μ K a (R.preimage ι hι.injOn) R' ho.measurableSet
    (ho.measure_pos μ ⟨1, one_mem _⟩).ne' hc.measure_lt_top.ne (fun γ hγ => by
      obtain ⟨y, e, h⟩ := (hdc _ _).1 (h1 _ (Finset.mem_preimage.1 hγ))
      exact hι e ▸ h) (fun x hx => by
      obtain ⟨γ, ⟨hγ, h⟩, hu⟩ := h2 (ι x) ((hdc _ _).2 ⟨x, rfl, hx⟩)
      obtain ⟨y, rfl, -⟩ := (hdc _ _).1 (h1 _ hγ)
      refine ⟨y, ⟨Finset.mem_preimage.2 hγ, (hK' _).1 (by rwa [map_mul, map_inv])⟩, fun z hz => hι (hu _
        ⟨Finset.mem_preimage.1 hz.1, ?_⟩)⟩
      rw [← map_inv, ← map_mul]
      exact (hK' _).2 hz.2) h3 h4
  rw [← map_inv]
  refine ⟨R'.image ι, fun γ hγ => ?_, fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hγ
    exact ⟨⟨y, rfl⟩, (hdc _ _).2 ⟨y, rfl, h3 y hy⟩⟩
  · obtain ⟨y, rfl, hy⟩ := (hdc _ _).1 hx
    obtain ⟨γ, ⟨hγ, h⟩, hu⟩ := h4 y hy
    refine ⟨ι γ, ⟨Finset.mem_image_of_mem _ hγ, ?_⟩, ?_⟩
    · rw [← map_inv, ← map_mul]
      exact (hK' _).2 h
    · rintro z ⟨hz, h'⟩
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hz
      rw [hu w ⟨hw, (hK' _).1 (by rwa [map_mul, map_inv])⟩]
  · rw [Finset.card_image_of_injective _ hι, ← hcard, Finset.card_preimage, Finset.filter_true_of_mem]
    intro γ hγ
    obtain ⟨y, e, -⟩ := (hdc _ _).1 (h1 _ hγ)
    exact ⟨y, e⟩

end Group

section Local

open scoped TensorProduct
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.AdelicUnimod

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem modular_eq_one (hσ : ∀ x, σ (σ x) = x) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ) (hJ : IsHermND σ J)
    (v : HeightOneSpectrum (𝓞 F)) (g : GLoc σ J v) : Measure.modularCharacter g = 1 := by
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  haveI : IsArtinianRing (Fv F v ⊗[F] E) := IsArtinianRing.of_finite (Fv F v) _
  letI : Algebra ℚ (Fv F v ⊗[F] E) := ((inclR (F := F) (Fv F v)).comp (algebraMap ℚ E)).toAlgebra
  obtain ⟨M, hM⟩ := exists_framed (σ := (σ : E →+* E)) hσ (J := J) (by ext i j; exact hJ.1 i j) hJ.2
  have hF : Framed (sigR (Fv F v) σ) (JR (Fv F v) J) (M.map (inclR (Fv F v))) := hM.map fun x => rfl
  have hss : ∀ x, sigR (Fv F v) σ (sigR (Fv F v) σ x) = x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [sigR, hσ]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  obtain ⟨T, hTc, hT, hT'⟩ := exists_involution (GlobalTheory.AdelicUnitaryTop.continuous_sigR (Fv F v) σ) hss hF
  have hgen : Generic (sigR (Fv F v) σ) :=
    generic_of_semilocal (δ := inclR (Fv F v) δ) (hδ.isUnit.map _) (by
      rw [← map_neg, ← hσδ]; rfl)
  have key : ∀ T : GLoc σ J v →* GLoc σ J v, Continuous T → (∀ x, T (T x) = x) → ∀ x,
      Measure.modularCharacter (T x) = Measure.modularCharacter x := fun T => modular_involution T
  exact char_eq_one hss hF hgen (Measure.modularCharacter (G := GLoc σ J v)) (fun x x' h => by
    rw [hT' x x' h]
    exact key T hTc hT x) g

end Local

section Host

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem idem_of_isPrimeIdem {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} (h : IsPrimeIdem P e f) :
    e * e = e ∧ ∃ v, GlobalTheory.PlaceComp.IsIdemOf D.host.E v f := by
  rcases h with ⟨⟨⟨he, -, v, ε, ⟨α, rfl, h1, h2⟩, hf⟩, -⟩, rfl⟩ | ⟨rfl, ⟨v, ε, ⟨α, rfl, h1, h2⟩, rfl⟩, -⟩
  · exact ⟨he, v, hf ▸ GlobalTheory.PlaceComp.isIdemOf_algebraMap h1 h2⟩
  · have h := GlobalTheory.PlaceComp.isIdemOf_algebraMap (E := D.host.E) h1 h2
    exact ⟨(GlobalTheory.SuppLocal.idem_mul_iff h _).2 ⟨h.1, h.2.2⟩, v, h⟩

theorem suppF_iff (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D}
    (hf : GlobalTheory.PlaceComp.IsIdemOf D.host.E v f) (g : GA D V) :
    SuppF V f g ↔ g ∈ (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v).range := by
  have h1 : ∀ w (g : GA D V), GlobalTheory.PlaceComp.locMat D.sp.cm V w g = 1 ↔
      GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram w g = 1 := fun w g => by
    rw [← GlobalTheory.AdelicU.projFinLoc_projFin]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg (HA.mat _ _ _) h⟩
  refine (GlobalTheory.SuppLocal.supp_iff D.sp.cm V hf g).trans ?_
  simp only [h1]
  constructor
  · rintro ⟨h2, h3⟩
    refine ⟨GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g, GlobalTheory.AdelicU.GAd_ext _ _ (fun w => ?_) fun u => ?_⟩
    · rw [GlobalTheory.AdelicU.projArch_emb, GlobalTheory.AdelicU.mem_finPts_iff_forall.1 h2 w]
    · by_cases e : u = v
      · rw [e, GlobalTheory.AdelicU.proj_emb_self]
      · rw [GlobalTheory.AdelicU.proj_emb_ne _ _ e, h3 u e]
  · rintro ⟨x, rfl⟩
    exact ⟨GlobalTheory.AdelicU.mem_finPts.2 (GlobalTheory.AdelicU.projInf_emb _ _ v x), fun w hw => GlobalTheory.AdelicU.proj_emb_ne _ _ hw x⟩

theorem exists_skew (D : D7) : ∃ δ : D.host.E, δ ≠ 0 ∧ D.sp.cm.sig δ = -δ := by
  by_contra! h
  have hs : Function.Surjective (algebraMap D.host.F D.host.E) := fun a => (D.sp.cm.fixed a).1 (by
    by_contra hne
    exact h (star a - a) (sub_ne_zero.2 hne) (by show star _ = _; simp))
  have := (LinearEquiv.ofBijective (Algebra.linearMap D.host.F D.host.E)
    ⟨(algebraMap D.host.F D.host.E).injective, hs⟩).finrank_eq
  rw [D.sp.cm.deg2, Module.finrank_self] at this
  omega

theorem isLattice_frameLat (V : HSp D) : Submodule.IsLattice D.host.E (GlobalTheory.AdelicU.frameLat V) := by
  exact Submodule.IsLattice.of_fg D.host.E (GlobalTheory.AdelicU.frameLat_fg V)

end Host

end GlobalTheory.HeckeDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelTypeEigenfunctionOfLiftableElement
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.LevelRows

variable {D : D7}

theorem levelType_eigenfunction_of_liftable_element {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {P : LevelP L.Pg L.r ℂ} {F : GA D V → ℂ} (hF : HasType V β (withP L P) F) (p : P.H)
    (hex : ∃ κ, IsLevelLift V β L p.1 κ) :
    actG0 V β L p.1 F = fun h => ((P.chi p : ℂˣ) : ℂ) * F h := by
  have hκ : IsLevelLift V β L p.1 hex.choose := hex.choose_spec
  have hp : rTup β L (finE V hex.choose) ∈ P.H := by rw [hκ.2.2]; exact p.2
  have hmem : hex.choose ∈ levG V β (withP L P) := ⟨hκ.1, hκ.2.1, hp⟩
  have hc : levChi V β (withP L P) hex.choose = ((P.chi p : ℂˣ) : ℂ) * levChi V β (flagL L) hex.choose := by
    unfold levChi
    rw [levFn_withP, extendOne_of_mem _ hp, Units.val_mul]
    congr 3
    exact Subtype.ext hκ.2.2
  have ha := levChi_ne_zero (β := β) (flagL L) hex.choose
  funext h
  unfold actG0
  rw [dite_eq_left hex, hF _ hmem h, hc]
  field_simp

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_lift_of_ne_zero (R : RealDat D A Ks) (hinj : Function.Injective R.HE.e) (hg : R.models_gE)
    {x : R.HE.H} (hx : x ≠ 0) (g : G) : ∃ κ, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) κ := by
  by_contra hk
  apply hx
  have h0 : R.gE g x = 0 := by
    apply hinj
    rw [hg g x, map_zero]
    ext v h
    show actG0 _ _ _ _ _ h = 0
    unfold actG0
    rw [dite_eq_right hk]
    rfl
  have : R.gE g⁻¹ (R.gE g x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← this, h0, map_zero]

theorem rowsOfLevel_of_models (R : RealDat D A Ks) (F : Face D A) (hE : R.models_HE) (hg : R.models_gE) :
    GlobalTheory.IndefiniteRowSideFullHecke.TypeCharacterLevelRows.RowsOfLevel R F := by
  intro b x
  have hx : R.HE.e x ∈ R.EEat R.triv := hE.2.1 ▸ LinearMap.mem_range_self _ x
  unfold RealDat.EEat at hx ⊢
  rw [mem_goodPart, GlobalTheory.MultMem.mem_mult_iff] at hx ⊢
  constructor
  · rintro ⟨h1, -⟩ g
    by_cases h0 : x = 0
    · simp [h0]
    apply hE.1
    rw [hg, map_smul]
    ext v h
    have hmem : R.eG g ∈ (R.levR F b).H := by
      show R.eG.symm (R.eG g) ∈ (F.lvl b).P
      rw [MulEquiv.symm_apply_apply]; exact g.2
    have h2 := levelType_eigenfunction_of_liftable_element (V := Yc D 0) (β := R.βY 0) (L := R.dat0 R.triv) (P := R.levR F b)
      (F := R.HE.e x v) (fun κ hκ h => h1.lev v κ hκ h) ⟨R.eG g, hmem⟩ (exists_lift_of_ne_zero R hE.1 hg h0 g)
    have h3 : (R.eG.symm.toMonoidHom.subgroupComap (F.lvl b).P) ⟨R.eG g, hmem⟩ = g :=
      Subtype.ext (R.eG.symm_apply_apply g)
    refine (congrFun h2 h).trans ?_
    show D.what₂.embLL (((F.lvl b).ψ ((R.eG.symm.toMonoidHom.subgroupComap (F.lvl b).P) ⟨R.eG g, hmem⟩) : D.what₂.LLˣ) : D.what₂.LL) * _ = _
    rw [h3]
    rfl
  · intro h
    refine ⟨⟨hx.1.aut, hx.1.cusp, fun v => ?_, hx.1.equiv, hx.1.cont⟩, hx.2⟩
    have hP : IsPLevel (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.levR F b) (R.HE.e x v) := by
      refine ⟨fun κ hκ y => hx.1.lev v κ hκ y, fun p => ?_⟩
      have h1 := congrArg (fun z => R.HE.e z v) (h ⟨R.eG.symm p.1, p.2⟩)
      simp only [hg _ x, map_smul] at h1
      have h2 : R.eG (R.eG.symm p.1) = p.1 := R.eG.apply_symm_apply p.1
      rw [h2] at h1
      exact h1
    exact fun κ hκ y => hP.hasType κ hκ y

end GlobalTheory.LevelRows

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineBundlePullOfIsLineBundleOnOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineBundlePullOfIsLineBundleOnOpen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem gm_eq_stalkMap {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)ˣ) :
    gm r z U a = Units.map (r.stalkMap z).hom.toMonoidHom (gm (𝟙 X) (r z) U a) := by
  apply Units.ext
  rw [gm_val r z U h, Units.coe_map, gm_val (𝟙 X) (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r U z h a.val).symm

theorem pull_isLB_of_isOn : ∀ (X Z : Scheme.{0}) (W : X.Opens) (L : LB X) (r : Z ⟶ X), IsOn W L → (∀ z, r z ∈ W) →
    (L.pull r).IsLB := by
  intro X Z W L r hL hr
  have coc : ∀ (z : Z) (a b c : L.ι), r z ∈ L.U a → r z ∈ L.U b → r z ∈ L.U c →
      gm r z _ (L.g a b) * gm r z _ (L.g b c) = gm r z _ (L.g a c) := by
    intro z a b c ha hb hc
    rw [gm_eq_stalkMap r z (L.U a ⊓ L.U b) ⟨ha, hb⟩, gm_eq_stalkMap r z (L.U b ⊓ L.U c) ⟨hb, hc⟩,
      gm_eq_stalkMap r z (L.U a ⊓ L.U c) ⟨ha, hc⟩, ← map_mul,
      hL.coc (r z) a b c ha hb hc]
  refine ⟨?_, ?_, ?_⟩
  · refine top_le_iff.1 fun z _ => ?_
    obtain ⟨a, ha⟩ := hL.cov (r z) (hr z)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => a, mem_pull.2 ha⟩
  · intro J
    refine unit_ext fun z hz => ?_
    rw [gm_res (𝟙 Z) z _ hz, map_one, gm_pull_g L r (𝟙 Z) z J J hz hz, Category.id_comp]
    have hJ := mem_pull.1 hz
    exact mul_eq_left.1 (coc z _ _ _ hJ hJ hJ)
  · intro I J K
    refine unit_ext fun z hz => ?_
    rw [map_mul, gm_res (𝟙 Z) z _ hz, gm_res (𝟙 Z) z _ hz, gm_res (𝟙 Z) z _ hz, gm_pull_g L r (𝟙 Z) z I J hz.1.1 hz.1.2,
      gm_pull_g L r (𝟙 Z) z J K hz.1.2 hz.2, gm_pull_g L r (𝟙 Z) z I K hz.1.1 hz.2, Category.id_comp]
    exact coc z _ _ _ (mem_pull.1 hz.1.1) (mem_pull.1 hz.1.2) (mem_pull.1 hz.2)

end GlobalTheory.PicGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineBundlePullOfIsLineBundleOnOpenStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLineBundle_pull_of_isLineBundleOnOpen : ∀ (X Z : Scheme.{0}) (W : X.Opens) (L : LB X) (r : Z ⟶ X), IsOn W L → (∀ z, r z ∈ W) → (L.pull r).IsLB := by
  first | exact @GlobalTheory.PicGlue.pull_isLB_of_isOn | exact GlobalTheory.PicGlue.pull_isLB_of_isOn | (intros; apply GlobalTheory.PicGlue.pull_isLB_of_isOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitDeterminantCongruentElement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatReflection

theorem latHat_eq_lamHat {D : D7} (V : HSp D) : Formalism.L2.Pj.latHat V = Formalism.L2.NTheta.LamHat V := by
  rw [GlobalTheory.LatDual.lamHat_eq_hat]
  exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1

end GlobalTheory.LatReflection
end
