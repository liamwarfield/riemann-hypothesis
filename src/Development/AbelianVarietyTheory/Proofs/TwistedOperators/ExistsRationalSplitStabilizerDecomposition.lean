module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionLineOperatorSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalProductsTendstoFrameStabiliser
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalStabilizerDoubledVacuumEigenvalueEqOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalSplitStabilizerDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalSplitStabilizerDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open Matrix

namespace GlobalTheory.RatSplitLat

theorem colLat_fg {K : Type} [Field K] [NumberField K] {n : ℕ} (B : GL (Fin n) K) : (colLat B).FG :=
  Submodule.fg_span (Set.finite_range _)

theorem colLat_span {K : Type} [Field K] [NumberField K] {n : ℕ} (B : GL (Fin n) K) :
    Submodule.span K ((colLat B : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K)) = ⊤ := by
  unfold colLat
  rw [Submodule.span_span_of_tower]
  rw [eq_top_iff]
  intro x _
  have hx : x = ∑ j, (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) j •
      (fun a : Fin n => (B : Matrix (Fin n) (Fin n) K) a j) := by
    funext a
    have := congrFun (show (B : Matrix (Fin n) (Fin n) K) *ᵥ (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) = x by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]) a
    conv_lhs => rw [← this]
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [hx]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem stab_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (H : AddSubgroup (Fin n → GlobalTheory.AdLat.RA F E)) (k : GL (Fin n) (GlobalTheory.AdLat.RA F E)) (N : ℕ)
    (h1 : ∀ z ∈ H, ∃ w ∈ H, k.1 *ᵥ z - z = N • w) (h2 : ∀ z ∈ H, (k⁻¹).1 *ᵥ z ∈ H) (y : Fin n → GlobalTheory.AdLat.RA F E) :
    y ∈ H ↔ k.1 *ᵥ y ∈ H := by
  constructor
  · intro hy
    obtain ⟨w, hw, e⟩ := h1 y hy
    rw [show k.1 *ᵥ y = (k.1 *ᵥ y - y) + y by abel, e]
    exact H.add_mem (H.nsmul_mem hw N) hy
  · intro hy
    have := h2 _ hy
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this


set_option maxHeartbeats 1000000 in
theorem exists_rat_split_lat : ∀ {D : D7} (V : HSp D) (B : GL (Fin V.rank) D.host.E) (N : ℕ), 0 < N → ∀ g : GfC V,
    ∃ r s k : GfC V, GlobalTheory.MovedKappaEx.RatFin V r ∧ GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N (finHom V s.1).1 ∧
      (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B) ↔
        Matrix.mulVec (Formalism.IndefR.Lev.finE V k.1).1 v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B)) ∧ g = r * s * k := by
  intro D V B N hN g
  obtain ⟨-, -, -, -, c2, -, c1, gh, gd, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨γ', h', k', u1, u2, u3, hg, hs, hk, hki⟩ := GlobalTheory.T.exists_unitary_adelic_decomposition_split_support D.host.F D.host.E (GlobalTheory.Member.cF D) V.rank V.gramᵀ
    ⟨c2, c1, gh, gd⟩ (GlobalTheory.UnRep.Space.finrank_two D) (colLat B) (colLat_fg B) (colLat_span B) (finHom V g.1) N
    (GlobalTheory.UnRep.Space.isUnA_finHom V g.1) hN
  obtain ⟨-, -, -, lift, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D V
  obtain ⟨r1, -, r3, -⟩ := GlobalTheory.Member.RatElt.rational_elements D V
  obtain ⟨h, hh, eh⟩ := lift h' u2
  obtain ⟨k, hk', ek⟩ := lift k' u3
  obtain ⟨γ, hγ⟩ := r3 γ' fun u v => by rw [GlobalTheory.UnRep.Space.herm_neg_eq, GlobalTheory.UnRep.Space.herm_neg_eq, u1]
  have eγ : (finHom V γ).1 = GlobalTheory.UnRep.fm D.host.F γ'.1 := GlobalTheory.Member.RatElt.fin_eq hγ
  have e : finHom V g.1 = finHom V γ * finHom V h * finHom V k := by
    apply Units.ext
    rw [hg, Units.val_mul, Units.val_mul, eγ, eh, ek]
  refine ⟨g * ⟨k, hk'⟩⁻¹ * ⟨h, hh⟩⁻¹, ⟨h, hh⟩, ⟨k, hk'⟩, ⟨γ, (r1 γ).2 ⟨γ', hγ⟩, ?_⟩, ?_, ?_, by rw [inv_mul_cancel_right, inv_mul_cancel_right]⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, map_mul, map_mul, map_inv, map_inv, e]
    rw [mul_inv_cancel_right, mul_inv_cancel_right]
  · change GlobalTheory.UnRep.SuppSplit _ N (finHom V h).1
    rw [eh]
    exact hs
  · intro v
    have key := GlobalTheory.StdFrames.hatL_of_hat (F := D.host.F) (colLat B) (colLat B) k'.1
      (stab_iff _ k' N hk hki) v
    have hm : (Formalism.IndefR.Lev.finE V k).1 =
        k'.1.map (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E) := by
      rw [← ek]; rfl
    refine key.trans (iff_of_eq ?_)
    exact congrArg (fun M => M *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B)) hm.symm

end GlobalTheory.RatSplitLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalSplitStabilizerDecompositionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_split_stabilizer_decomposition : ∀ {D : D7} (V : HSp D) (B : GL (Fin V.rank) D.host.E) (N : ℕ), 0 < N → ∀ g : GfC V,
    ∃ r s k : GfC V, GlobalTheory.MovedKappaEx.RatFin V r ∧ GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N (finHom V s.1).1 ∧
      (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B) ↔
        Matrix.mulVec (Formalism.IndefR.Lev.finE V k.1).1 v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B)) ∧ g = r * s * k := by
  first | exact @GlobalTheory.RatSplitLat.exists_rat_split_lat | exact GlobalTheory.RatSplitLat.exists_rat_split_lat | (intros; apply GlobalTheory.RatSplitLat.exists_rat_split_lat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanPreimageRealPlaceLine
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanPreimageRealPlaceLine
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.ArchLinePreimage

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem smul_eq_zero_of_finPart_eq_zero (t : AE D) (ht : finPart D t = 0) (a : AF D.host.F)
    (ha : a.1 = 0) : a • t = 0 := by
  let ι : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F →ₗ[D.host.F] AF D.host.F :=
    (LinearMap.inr D.host.F (InfiniteAdeleRing D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)).comp
      (LinearMap.mulLeft D.host.F a.2)
  let g : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
    TensorProduct.map ι LinearMap.id
  let fL : AE D →ₗ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E :=
    TensorProduct.map (sndA D.host.F).toLinearMap LinearMap.id
  have hfL : fL t = finPart D t := rfl
  have key : ∀ s : AF D.host.F ⊗[D.host.F] D.host.E, a • s = g (fL s) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => rw [smul_zero, LinearMap.map_zero, LinearMap.map_zero]
    | tmul b x =>
      have hab : a * b = ι b.2 := by
        refine Prod.ext ?_ ?_
        · show a.1 * b.1 = 0
          rw [ha, zero_mul]
        · rfl
      have h1 : a • (b ⊗ₜ[D.host.F] x : AE D) = (a * b) ⊗ₜ[D.host.F] x := rfl
      rw [h1, hab]
      rfl
    | add s₁ s₂ h₁ h₂ =>
      rw [smul_add, h₁, h₂, LinearMap.map_add (f := _), LinearMap.map_add (f := _)]
  rw [key, hfL, ht, LinearMap.map_zero]

theorem arch_symm_lineAt : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (ε : Bool) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X),
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (cS.symm (lineAt θ τ z 1)) := by
  intro D θ hθ ε S X d e cS hcS τ z u hu
  have hx : (lineAt θ τ z 1).map (finPart D) = 0 :=
    funext fun i => funext fun j => congrFun (congrFun ((GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z).2.1 1) i) j
  set y := cS.symm (lineAt θ τ z 1) with hydef
  have hy := cS.apply_symm_apply (lineAt θ τ z 1)
  rw [← hydef, hcS] at hy
  set c : D.host.E := if ε then -1 else 1 with hc
  have hc0 : c ≠ 0 := by rw [hc]; split_ifs <;> norm_num
  set N : Matrix (Fin S.rank) (Fin S.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    (c • S.gram).map ((finPart D).comp (inclR (AF D.host.F))) with hN
  have hNdet : IsUnit N.det := by
    have hd : N.det = ((finPart D).comp (inclR (AF D.host.F))) (c • S.gram).det :=
      (RingHom.map_det ((finPart D).comp (inclR (AF D.host.F))) _).symm
    rw [hd]
    refine IsUnit.map _ (Ne.isUnit ?_)
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hc0) (gram_det_ne S)
  have hM : (HMul.hMul ((y.map (finPart D))ᵀ.submatrix e id) N :
      Matrix (Fin X.rank) (Fin S.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) = 0 := by
    have h3 := congrArg (fun m => Matrix.map m (finPart D)) hy
    simp only [Matrix.map_mul] at h3
    rw [hx] at h3
    exact h3
  have hM0 : (y.map (finPart D))ᵀ.submatrix e id = 0 := by
    calc _ = HMul.hMul (HMul.hMul ((y.map (finPart D))ᵀ.submatrix e id) N :
          Matrix (Fin X.rank) (Fin S.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) N⁻¹ :=
          (Matrix.mul_nonsing_inv_cancel_right N _ hNdet).symm
      _ = 0 := by rw [hM, Matrix.zero_mul]
  have hent : ∀ i j, finPart D (y i j) = 0 := by
    intro i j
    have h4 := congrFun (congrFun hM0 (e.symm j)) i
    simp only [Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply, Equiv.apply_symm_apply,
      id, Matrix.zero_apply] at h4
    exact h4
  have hu1 : u.1 = 0 := by
    have h5 : (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F) u.1 = 0 := hu
    exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).injective).1 h5
  funext i j
  exact smul_eq_zero_of_finPart_eq_zero (y i j) (hent i j) u hu1

end GlobalTheory.ArchLinePreimage
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanPreimageRealPlaceLineStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_preimage_realPlace_line : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (ε : Bool) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X),
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (cS.symm (lineAt θ τ z 1)) := by
  first | exact @GlobalTheory.ArchLinePreimage.arch_symm_lineAt | exact GlobalTheory.ArchLinePreimage.arch_symm_lineAt | (intros; apply GlobalTheory.ArchLinePreimage.arch_symm_lineAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicTypeFiniteDimStable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.FiniteGKSum

open GlobalTheory.SeriesToClosure Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes
open Matrix Filter
open scoped InnerProductSpace Topology

section Sums

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau)
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin V.rank → Bool)
  (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ)

def gkSums : Submodule ℂ (GA D V → ℂ) where
  carrier := {ψ | ∃ (m : ℕ) (T : Fin m → (kFin ε σ →ₗ[ℂ] (GA D V → ℂ))) (p : Fin m → kFin ε σ),
    (∀ j, IsGKMap θ V τ ε σ P (T j)) ∧ ψ = ∑ j, T j (p j)}
  zero_mem' := ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨m, T, p, hT, rfl⟩ ⟨m', T', p', hT', rfl⟩
    refine ⟨m + m', Fin.append T T', Fin.append p p', fun j => ?_, ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa using hT j
      · simpa using hT' j
    · simp [Fin.sum_univ_add]
  smul_mem' := by
    rintro c _ ⟨m, T, p, hT, rfl⟩
    exact ⟨m, T, fun j => c • p j, hT, by simp [Finset.smul_sum]⟩

end Sums

section Closure

variable {D : D7} {V : HSp D}

theorem mem_of_approx {E : Submodule ℂ (GA D V → ℂ)} [FiniteDimensional ℂ E] {φ : GA D V → ℂ}
    (h : ∀ C : Set (GA D V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ ψ ∈ E, ∀ x ∈ C, ‖φ x - ψ x‖ < δ) : φ ∈ E := by
  have hE : IsClosed (E : Set (GA D V → ℂ)) := Submodule.closed_of_finiteDimensional E
  have key : ∀ p : Finset (GA D V) × ℕ, ∃ ψ ∈ E, ∀ x ∈ p.1, ‖φ x - ψ x‖ < 1 / ((p.2 : ℝ) + 1) :=
    fun p => h _ p.1.finite_toSet.isCompact _ (by positivity)
  choose u hu hu' using key
  refine hE.mem_of_tendsto (f := u) (b := (atTop : Filter (Finset (GA D V) × ℕ))) ?_
    (Filter.Eventually.of_forall hu)
  refine tendsto_pi_nhds.2 fun x => Metric.tendsto_atTop.2 fun δ hδ => ?_
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine ⟨({x}, N), fun p hp => ?_⟩
  have h1 : x ∈ p.1 := hp.1 (Finset.mem_singleton_self x)
  have h2 : (N : ℝ) ≤ p.2 := by exact_mod_cast hp.2
  rw [dist_comm, dist_eq_norm]
  calc ‖φ x - u p x‖ < 1 / ((p.2 : ℝ) + 1) := hu' p x h1
    _ ≤ 1 / ((N : ℝ) + 1) := by gcongr
    _ < δ := hN

end Closure

section Avg

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {τ : D.what₂.Tau}
  {ε : Fin V.rank → Bool} {P : Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem avg_mem (hθ : IsInfFam (D := D) θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {W : Submodule ℂ (GA D V → ℂ)} [FiniteDimensional ℂ W]
    (hW : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), P * g * P⁻¹ ∈ Formalism.REAL.Kset ε →
      ∀ h ∈ W, rTr V (atTau θ V τ g) h ∈ W)
    {φ : GA D V → ℂ} (hφc : Continuous φ) (hφ : φ ∈ W) {e : KG ε → ℂ} (he : KFinFun ε e) :
    avg θ V τ ε P e φ ∈ W := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hk : Continuous fun k : KG ε => atTau θ V τ (P⁻¹ * toMK k * P) :=
    (continuousOn_atTau hθ V τ).comp_continuous continuous_conjK
      fun k => conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))
  have hd := (isUnit_iff_isUnit_det _).1 hP
  have cc : ∀ g : Matrix (Fin V.rank) (Fin V.rank) ℂ, P * (P⁻¹ * g * P) * P⁻¹ = g := fun g => by
    calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [Matrix.mul_nonsing_inv _ hd]; simp
  have hmem : ∀ k : KG ε, rTr V (atTau θ V τ (P⁻¹ * toMK k * P)) φ ∈ W := fun k =>
    hW _ (conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))) (by rw [cc]; exact toMK_mem_K k) φ hφ
  let f : KG ε → W := fun k => ⟨_, hmem k⟩
  have hf : Continuous f := (continuous_pi fun x => hφc.comp (continuous_const.mul hk)).subtype_mk _
  let b := Module.finBasis ℂ W
  have hc : ∀ i, Continuous fun k => b.coord i (f k) := fun i =>
    (LinearMap.continuous_of_finiteDimensional (b.coord i)).comp hf
  have he' : Continuous e := by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1
  have hint : ∀ i, Integrable (fun k => e k * b.coord i (f k)) (muK ε) := fun i =>
    integrableOn_univ.mp ((he'.mul (hc i)).continuousOn.integrableOn_compact isCompact_univ)
  have hrep : ∀ k, (f k : GA D V → ℂ) = ∑ i, b.coord i (f k) • (b i : GA D V → ℂ) := fun k => by
    nth_rw 1 [← b.sum_repr (f k)]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    rfl
  have key : avg θ V τ ε P e φ = ∑ i, (∫ k, e k * b.coord i (f k) ∂(muK ε)) • (b i : GA D V → ℂ) := by
    funext x
    have hx : ∀ k, φ (x * atTau θ V τ (P⁻¹ * toMK k * P)) = ∑ i, b.coord i (f k) * (b i : GA D V → ℂ) x :=
      fun k => by
        have := congrFun (hrep k) x
        simpa [f, rTr, Finset.sum_apply] using this
    simp only [avg, hx, Finset.mul_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_finsetSum _ fun i _ => ?_]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_mul_const]
      congr 1
      funext k
      ring
    · simpa [mul_assoc] using (hint i).mul_const ((b i : GA D V → ℂ) x)
  rw [key]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2

end Avg

end GlobalTheory.FiniteGKSum

namespace GlobalTheory.FiniteGKSum

end GlobalTheory.FiniteGKSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSplitPlaceFinitePointsOffPrimesOfSupported
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSplitPlaceFinitePointsOffPrimesOfSupported
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

namespace GlobalTheory.MovedKappaEx

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem


set_option maxHeartbeats 1000000 in
theorem mem_splitOff_of_suppSplit : ∀ {D : D7} (V : HSp D) (Q : Finset ℕ) (s : GfC V),
    GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) (∏ q ∈ Q, q) (finHom V s.1).1 → s ∈ GlobalTheory.MovedKappaEx.splitOff V Q := by
  classical
  intro D V Q s hs
  obtain ⟨g, hg⟩ := s
  let P : GA D V → Prop := fun x => ∃ h : x ∈ GfC V, (⟨x, h⟩ : GfC V) ∈ splitOff V Q
  have h1 : P 1 := ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
  have hmul : ∀ x y, P x → P y → P (x * y) := fun x y ⟨hx, mx⟩ ⟨hy, my⟩ =>
    ⟨Subgroup.mul_mem _ hx hy, Subgroup.mul_mem _ mx my⟩
  have hinj : Function.Injective (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D)) :=
    Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective
  obtain ⟨e₀, he1, he2, he3, he4⟩ := hs
  have heS : e₀ = GlobalTheory.LocalApprox.indA D.host.F he2.toFinset := by
    refine GlobalTheory.LocalApprox.af_ext _ fun w => ?_
    by_cases hw : w ∈ he2.toFinset
    · rw [GlobalTheory.LocalApprox.evalV_indA_of_mem _ hw]
      have hne : evalV D.host.F w e₀ ≠ 0 := he2.mem_toFinset.1 hw
      have h := congrArg (evalV D.host.F w) he1
      rw [map_mul] at h
      exact mul_left_cancel₀ hne (h.trans (mul_one _).symm)
    · rw [GlobalTheory.LocalApprox.evalV_indA_of_notMem _ hw]
      by_contra h
      exact hw (he2.mem_toFinset.2 h)
  have hsupp : ∀ i j, GlobalTheory.LocalApprox.idemE D he2.toFinset * (Formalism.L2.Theta.mt V g - 1) i j =
      (Formalism.L2.Theta.mt V g - 1) i j := by
    intro i j
    have e0 : GlobalTheory.LocalApprox.idemE D he2.toFinset = fj D e₀ := (congrArg (fj D) heS).symm
    rw [e0]
    refine GlobalTheory.UnitarySplit.parts_inj D _ _ ?_ ?_
    · have h5 : infPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
        have h6 : (Formalism.L2.Theta.mt V g).map (infPart D) = 1 := congrArg Units.val (show infHom V g = 1 from hg)
        have h7 := congrFun (congrFun h6 i) j
        rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero]
        refine h7.trans ?_
        by_cases e : i = j
        · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
        · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]
      rw [RingHom.map_mul, h5, mul_zero]
    · have h5 : finPart D ((Formalism.L2.Theta.mt V g - 1) i j) = ((finHom V g).1 - 1) i j := by
        rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub]
        congr 1
        by_cases e : i = j
        · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
        · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]
      rw [RingHom.map_mul, h5]
      exact congrFun (congrFun he4 i) j
  have hgS : GlobalTheory.LocalApprox.cutAt V g he2.toFinset = g := by
    refine GlobalTheory.IdemSupport.mt_inj V ?_
    rw [GlobalTheory.LocalApprox.mt_cutAt]
    ext i j
    have h := hsupp i j
    rw [Matrix.sub_apply] at h
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    linear_combination h
  have hpl : ∀ v, pl D v = GlobalTheory.LocalApprox.idemE D {v} := fun v => by
    show fj D _ = fj D _
    congr 1
    refine GlobalTheory.LocalApprox.af_ext _ fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [evalV_singleV_same, GlobalTheory.LocalApprox.evalV_indA_of_mem _ (Finset.mem_singleton_self _)]
    · rw [evalV_singleV_ne _ v _ hw, GlobalTheory.LocalApprox.evalV_indA_of_notMem _ (Finset.notMem_singleton.2 hw)]
  have hv : ∀ v ∈ he2.toFinset, P (GlobalTheory.LocalApprox.cutAt V g {v}) := by
    intro v hvS
    have hv' := he3 v (he2.mem_toFinset.1 hvS)
    obtain ⟨e, he⟩ := _root_.GlobalTheory.MovedSplit.exists_splitAt D v hv'.1
    refine ⟨GlobalTheory.LocalApprox.cutAt_mem_GfC V g {v}, Subgroup.subset_closure ⟨e, (isSplitIdem_iff e).2 ⟨v, he⟩, ?_, ?_⟩⟩
    · intro q hq v' ε' hε' heq
      have hε : ε' = pairA D.host.F 0 (GlobalTheory.LocalApprox.indA D.host.F {v}) :=
        hinj (heq.symm.trans ((he.2.2).trans (hpl v)))
      obtain ⟨α, hα, hα1, hα0⟩ := hε'
      have hαv : α = GlobalTheory.LocalApprox.indA D.host.F {v} := congrArg Prod.snd (hα.symm.trans hε)
      have hvv : v' = v := by
        by_contra hne
        have := hα0 v (Ne.symm hne)
        rw [hαv, GlobalTheory.LocalApprox.evalV_indA_of_mem _ (Finset.mem_singleton_self _)] at this
        exact one_ne_zero this
      subst hvv
      intro hqm
      refine hv'.2 ?_
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun q : ℕ => q) hq
      have hk' : ((∏ q ∈ Q, q : ℕ) : 𝓞 D.host.F) = (q : 𝓞 D.host.F) * (k : 𝓞 D.host.F) := by
        rw [hk, Nat.cast_mul]
      rw [hk']
      exact Ideal.mul_mem_right _ _ hqm
    · intro i j
      rw [he.2.2, hpl v]
      exact GlobalTheory.LocalApprox.cutAt_supp V g {v} i j
  have key : ∀ t : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)), t ⊆ he2.toFinset →
      P (GlobalTheory.LocalApprox.cutAt V g t) := by
    intro t
    induction t using Finset.cons_induction with
    | empty => intro _; rw [GlobalTheory.LocalApprox.cutAt_empty]; exact h1
    | cons v t h ih =>
      intro hsub
      rw [GlobalTheory.LocalApprox.cutAt_cons]
      exact hmul _ _ (hv v (hsub (Finset.mem_cons_self _ _))) (ih ((Finset.subset_cons h).trans hsub))
  obtain ⟨_, hm⟩ := hgS ▸ key _ subset_rfl
  exact hm

end GlobalTheory.MovedKappaEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSplitPlaceFinitePointsOffPrimesOfSupportedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_splitPlaceFinitePointsOffPrimes_of_supported : ∀ {D : D7} (V : HSp D) (Q : Finset ℕ) (s : GfC V),
    GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) (∏ q ∈ Q, q) (finHom V s.1).1 → s ∈ GlobalTheory.MovedKappaEx.splitOff V Q := by
  first | exact @GlobalTheory.MovedKappaEx.mem_splitOff_of_suppSplit | exact GlobalTheory.MovedKappaEx.mem_splitOff_of_suppSplit | (intros; apply GlobalTheory.MovedKappaEx.mem_splitOff_of_suppSplit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledVacuumEigenvalueEqOneSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledVacuumEigenvalueEqOneSplitPlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacSiegelAny
open GlobalTheory.DblVacSiegel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piE_locIdele_self (P : HeightOneSpectrum (𝓞 E)) (y : (P.adicCompletion E)ˣ) :
    piE F P (locIdele F P y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = y := by
  classical
  change (finAdEquiv F E (finTens F E (locIdele F P y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) P = _
  rw [finTens_locIdele, GlobalTheory.CMVal.single_apply]
  exact Function.update_self _ _ _

theorem piE_locIdele_ne {P Q : HeightOneSpectrum (𝓞 E)} (h : Q ≠ P) (y : (P.adicCompletion E)ˣ) :
    piE F Q (locIdele F P y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 1 := by
  classical
  change (finAdEquiv F E (finTens F E (locIdele F P y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) Q = _
  rw [finTens_locIdele, GlobalTheory.CMVal.single_apply]
  exact Function.update_of_ne h _ _

theorem eq_one_of_comp {x : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ} (h1 : infTens F E x = 1) (h2 : ∀ P, piE F P (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 1) : x = 1 := by
  refine Units.ext (tens_ext (h1.trans (map_one _).symm) ((finAdEquiv F E).injective ?_))
  refine FiniteAdeleRing.ext _ fun P => ?_
  rw [Units.val_one, map_one, map_one]
  exact h2 P

theorem chr_eq_one_of_supp (χ : Chr F E) (S : Finset (HeightOneSpectrum (𝓞 E))) (hχ : ∀ P ∈ S, UnrAt χ P)
    (x : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) (h1 : infTens F E x = 1) (hoff : ∀ P ∉ S, piE F P (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 1)
    (hu : ∀ P ∈ S, Valued.v (piE F P (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = 1) : χ x = 1 := by
  classical
  induction S using Finset.induction_on generalizing x with
  | empty =>
    rw [eq_one_of_comp h1 fun P => hoff P (Finset.notMem_empty P), map_one]
  | insert P S hPS ih =>
    let y : (P.adicCompletion E)ˣ := Units.map (piE F P).toMonoidHom x
    have hy : Formalism.L2.Host.IsUnitAt P y := hu P (Finset.mem_insert_self P S)
    have hl : χ (locIdele F P y) = 1 := Circle.ext (congrArg Units.val (hχ P (Finset.mem_insert_self P S) y hy))
    set x' := x * (locIdele F P y)⁻¹ with hx'
    have ex : (x' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) * (locIdele F P y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = x := by
      rw [hx', Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
    have hcomp : ∀ {R : Type} [CommRing R] (φ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* R), φ (locIdele F P y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 1 →
        φ (x' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = φ x := fun φ h => by rw [← ex, map_mul, h, mul_one]
    have hx : x = x' * locIdele F P y := by rw [hx', inv_mul_cancel_right]
    rw [hx, map_mul, hl, mul_one]
    refine ih (fun Q hQ => hχ Q (Finset.mem_insert_of_mem hQ)) x' ?_ (fun Q hQ => ?_) (fun Q hQ => ?_)
    · rw [hcomp _ (infTens_locIdele P y), h1]
    · by_cases hQP : Q = P
      · subst hQP
        have e := congrArg (piE F Q) ex
        rw [map_mul, piE_locIdele_self] at e
        have h0 : (piE F Q (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) ≠ 0 := (Units.map (piE F Q).toMonoidHom x).ne_zero
        exact mul_right_cancel₀ h0 (e.trans (one_mul _).symm)
      · rw [hcomp _ (piE_locIdele_ne hQP y)]
        exact hoff Q (by simp [hQP, hQ])
    · have hQP : Q ≠ P := fun h => hPS (h ▸ hQ)
      rw [hcomp _ (piE_locIdele_ne hQP y)]
      exact hu Q (Finset.mem_insert_of_mem hQ)

theorem finite_under_eq (v : Pl (F := F)) : {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) = v}.Finite := by
  have h0 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact v.ne_bot
  refine (Ideal.finite_factors h0).subset fun P hP => ?_
  simp only [Set.mem_setOf_eq] at hP ⊢
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← hP]
  exact le_rfl

theorem chr_det_eq_one_any {d : ℕ} (W : Spc F E d) (hL : W.L.IsFullLattice E) {v : Pl (F := F)} {χ : Chr F E}
    (hχ : ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → UnrAt χ P) (t : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (h1 : At (evFin F v) ((t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1))
    (ht : ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
      ((t⁻¹ : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    χ (Matrix.GeneralLinearGroup.det t) = 1 := by
  classical
  set δ := Matrix.GeneralLinearGroup.det t with hδ
  have hN := h1 (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
  have hφ : ∀ {R : Type} [CommRing R] (φ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* R),
      φ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) = 0 → φ (δ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 1 := by
    intro R _ φ hφ
    have : φ.mapMatrix (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = φ.mapMatrix 1 := by
      ext i j
      have h2 := congrArg φ (congrFun (congrFun hN i) j)
      rw [Matrix.smul_apply, Algebra.smul_def, map_mul, map_sub, map_sub, map_one, map_one, hφ, sub_zero, one_mul,
        Matrix.sub_apply, map_sub, Matrix.zero_apply, map_zero, sub_eq_zero] at h2
      exact h2
    rw [hδ, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det, this, map_one, Matrix.det_one]
  refine chr_eq_one_of_supp χ (finite_under_eq (E := E) v).toFinset
    (fun P hP => hχ P ((finite_under_eq v).mem_toFinset.1 hP)) δ (hφ _ (TensorProduct.zero_tmul _ _))
    (fun P hP => ?_) (fun P hP => ?_)
  · have hPv : P.under (𝓞 F) ≠ v := fun h => hP ((finite_under_eq v).mem_toFinset.2 h)
    refine hφ _ ?_
    rw [piE_algebraMap rfl]
    exact (congrArg _ (evalV_singleFin_ne hPv 1)).trans (map_zero _)
  · have hu : P.under (𝓞 F) = v := (finite_under_eq v).mem_toFinset.1 hP
    let y : (P.adicCompletion E)ˣ := Units.map (piE F P).toMonoidHom δ
    have a1 : Valued.v (y : P.adicCompletion E) ≤ 1 := val_det_le_one W hL hu _ fun z hz => (ht z hz).1
    have a2 : Valued.v ((y⁻¹ : (P.adicCompletion E)ˣ) : P.adicCompletion E) ≤ 1 := by
      have := val_det_le_one W hL hu _ fun z hz => (ht z hz).2
      rw [← Matrix.GeneralLinearGroup.val_det_apply, map_inv] at this
      exact this
    have h0 : 0 < Valued.v (y : P.adicCompletion E) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 y.ne_zero)
    rw [Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ h0] at a2
    exact le_antisymm a1 a2

theorem eigen_eq_one_of_diag_any : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), v ∉ X.T →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M.co dd →
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.β (diagCols (Fin (a + a'))) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r → tens (evFin F v) (G.M.vac v) r ≠ 0 →
    ∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PDiag σ G.W → ∀ μ : ℂ,
      omd p (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) → μ = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv dd omd hdd hW r hr h0 p hp hpd μ hμ
  obtain ⟨t, ht₀⟩ := hpd
  have ht : GlobalTheory.DblVac.matD p * (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
      (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * (t : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := ht₀
  have hF := hT.base.cm.1
  set Ψ := tens (evFin F v) (G.M.vac v) r with hΨ
  have hS := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hr.2 _ (GlobalTheory.SchAConj.star_mem_schA F _ Ψ hr.2)
  have hl := lDiag_box_ne_zero hF hr.2 h0
  have hS0 : (boxFun Ψ fun x => star (Ψ x)) ≠ 0 := fun h => hl (by rw [h, map_zero])
  have hn := norm_eq_one_of_eigen hF hW.2.1.unit hS hS0 hμ
  have hrule := hW.2.2 _ DiagForm.lDiag_adm (fun z φ hφ => by
    have e : z * (diagCols (Fin (a + a')) : Matrix _ _ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ = Matrix.fromCols z z := by
      rw [diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols, Matrix.transpose_one, Matrix.mul_one]
    rw [e, Darboux.rho, hdd]
    exact DiagForm.lDiag_schr B.ψ _ _ hφ) p t ht _ hS
  have hvec : ∀ (g : GlobalTheory.DblVac.UD σ G.W) (s : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
      GlobalTheory.DblVac.matD g * (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * s → ∀ z,
      (GlobalTheory.DblVac.matD g *ᵥ Sum.elim z z) ∘ Sum.inl = s *ᵥ z := fun g s hs z => by
    have e : ∀ z : Fin (a + a') → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z = Sum.elim z z := fun z => by
      rw [diagCols, Matrix.fromRows_mulVec, Matrix.one_mulVec]
    rw [← e, Matrix.mulVec_mulVec, hs, ← Matrix.mulVec_mulVec, e]
    rfl
  have ht' : GlobalTheory.DblVac.matD p⁻¹ * (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
      (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * ((t⁻¹ : GL (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
    have e1 : GlobalTheory.DblVac.matD p⁻¹ * GlobalTheory.DblVac.matD p = 1 := p.1.inv_mul
    calc _ = GlobalTheory.DblVac.matD p⁻¹ * ((diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * (t : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) *
          ((t⁻¹ : GL (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, t.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← ht, ← Matrix.mul_assoc, e1, Matrix.one_mul]
  have hβ : X.β (Matrix.GeneralLinearGroup.det t) = 1 := by
    refine chr_det_eq_one_any (v := v) G.W hT.geo.hW.lat (fun P hP => hT.chars.unrβ P fun h => hv (hP ▸ (h : P.under (𝓞 F) ∈ (X.T : Set (Pl (F := F)))))) t
      (fun u hu => ?_) fun z hz => ?_
    · have e1 : (GlobalTheory.DblVac.matD p - 1) * (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
          (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * ((t : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) := by
        rw [Matrix.sub_mul, Matrix.mul_sub, ht, Matrix.one_mul, Matrix.mul_one]
      have e2 : (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * (u • ((t : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1)) = 0 := by
        rw [Matrix.mul_smul, ← e1, ← Matrix.smul_mul, hp.1 u hu, Matrix.zero_mul]
      rw [diagCols, Matrix.fromRows_mul, Matrix.one_mul] at e2
      ext i j
      exact congrFun (congrFun e2 (Sum.inl i)) j
    · have hz' := hp.2 (Sum.elim z z) ⟨hz, hz⟩
      exact ⟨hvec p _ ht z ▸ hz'.1.1, hvec p⁻¹ _ ht' z ▸ hz'.2.1⟩
  have hrule' := (congrArg (DiagForm.lDiag F (Fin a × Fin (a + a'))) hμ).symm.trans hrule
  simp only [map_smul, smul_eq_mul, hβ, Circle.coe_one, one_mul] at hrule'
  have hμ' := mul_right_cancel₀ hl hrule'
  rw [hμ', Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)] at hn
  rw [hμ', hn, Complex.ofReal_one]

theorem eigen_eq_one_of_diag_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → v ∉ X.T → PsiUnr B.ψ v →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M.co dd →
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.β (diagCols (Fin (a + a'))) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r → tens (evFin F v) (G.M.vac v) r ≠ 0 →
    ∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PDiag σ G.W → ∀ μ : ℂ,
      omd p (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) → μ = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v _ hv _ dd omd hdd hW r hr h0 p hp hpd μ hμ
  exact eigen_eq_one_of_diag_any F E σ B a a' G X om om' hT v hv dd omd hdd hW r hr h0 p hp hpd μ hμ

end GlobalTheory.DblVacSiegelAny
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledVacuumEigenvalueEqOneSplitPlaceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuum_eigenvalue_eq_one_splitPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → v ∉ X.T → PsiUnr B.ψ v →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M.co dd →
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.β (diagCols (Fin (a + a'))) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r → tens (evFin F v) (G.M.vac v) r ≠ 0 →
    ∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PDiag σ G.W → ∀ μ : ℂ,
      omd p (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) → μ = 1 := by
  first | exact @GlobalTheory.DblVacSiegelAny.eigen_eq_one_of_diag_split | exact GlobalTheory.DblVacSiegelAny.eigen_eq_one_of_diag_split | (intros; apply GlobalTheory.DblVacSiegelAny.eigen_eq_one_of_diag_split <;> assumption)
end
end
