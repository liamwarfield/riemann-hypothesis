module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ExistsNeZeroOfIsMatch
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeOrbitVectorsMovedPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateLevelRealBoxLeIndexMul

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedWeilRepresentationConvergence
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
namespace GlobalTheory.WeilConv
theorem twisted_weil_representation_convergence : GlobalTheory.Published.SiegelSetUnitary → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.SquareSt.WeilConvergence :=
  fun hRT _ => weilConvergence_of_siegelSet hRT
end GlobalTheory.WeilConv
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_theta_integral_converges : GlobalTheory.Published.SiegelSetUnitary → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.SquareSt.WeilConvergence := by
  first | exact @_root_.GlobalTheory.WeilConv.twisted_weil_representation_convergence | exact _root_.GlobalTheory.WeilConv.twisted_weil_representation_convergence | (intros; apply _root_.GlobalTheory.WeilConv.twisted_weil_representation_convergence <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DifferentiableMovedOperatorEval
section
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
namespace GlobalTheory.MovedDict.Entire
theorem differentiable_moved_operator_eval : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    Differentiable ℂ (Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p)) := by
  intro _ _ D Γ _ _ Pl0 T A Ks _ _ _ R ch _ p hp x y
  exact differentiable_Iop' _ _ (ch.S.Z.e0_is p hp).1.1
end GlobalTheory.MovedDict.Entire
end

section
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
theorem _root_.GlobalTheory.T.twisted_moved_operator_entire : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    Differentiable ℂ (Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p)) := by
  first | exact @_root_.GlobalTheory.MovedDict.Entire.differentiable_moved_operator_eval | exact _root_.GlobalTheory.MovedDict.Entire.differentiable_moved_operator_eval | (intros; apply _root_.GlobalTheory.MovedDict.Entire.differentiable_moved_operator_eval <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedMovedSeriesDecomposition
section
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
set_option maxHeartbeats 800000
namespace GlobalTheory.MovedSD
open Matrix
end GlobalTheory.MovedSD
theorem GlobalTheory.MovedSD.moved_series_decomposition : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    SD D (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) ∧ SD D (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y) := by
  intro _ _ D Γ _ _ Pl0 T A Ks _ _ _ R ch _ p hp x y
  have hn := DefPair.nodes hp
  cases p with
  | chi i j => exact ⟨GlobalTheory.MovedSD.sd_latAt _ _ hn.2 y, GlobalTheory.MovedSD.sd_latAt _ _ hn.1 x⟩
  | top t j => exact ⟨GlobalTheory.MovedSD.sd_latAt _ _ hn.1 x, GlobalTheory.MovedSD.sd_latAt _ _ hn.2 y⟩
  | _ => exact hp.elim
end

section
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
theorem _root_.GlobalTheory.T.twisted_moved_series_decomposition : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    SD D (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) ∧ SD D (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y) := by
  first | exact @_root_.GlobalTheory.MovedSD.moved_series_decomposition | exact _root_.GlobalTheory.MovedSD.moved_series_decomposition | (intros; apply _root_.GlobalTheory.MovedSD.moved_series_decomposition <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RankPolarizationPiLeAleph0
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
private theorem countable_compactOpen_local (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    {K : Set X | IsCompact K ∧ IsOpen K}.Countable := by
  classical
  have hB := TopologicalSpace.isBasis_countableBasis X
  haveI : Countable (TopologicalSpace.countableBasis X) := (TopologicalSpace.countable_countableBasis X).to_subtype
  refine (Set.countable_range fun t : Finset (TopologicalSpace.countableBasis X) => ⋃ b ∈ t, (b : Set X)).mono ?_
  rintro K ⟨hKc, hKo⟩
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun b : {b : TopologicalSpace.countableBasis X // (b : Set X) ⊆ K} => (b.1 : Set X))
    (fun b => hB.isOpen b.1.2) (fun x hx => by
      obtain ⟨b, hbB, hxb, hbK⟩ := hB.exists_subset_of_mem_open hx hKo
      exact Set.mem_iUnion.2 ⟨⟨⟨b, hbB⟩, hbK⟩, hxb⟩)
  refine ⟨t.image (fun c => c.1), ?_⟩
  apply Set.Subset.antisymm
  · intro x hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨b, hb, hxb⟩ := hx
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hb
    exact c.2 hxb
  · intro x hx
    have := ht hx
    rw [Set.mem_iUnion₂] at this
    obtain ⟨c, hc, hxc⟩ := this
    rw [Set.mem_iUnion₂]
    exact ⟨c.1, Finset.mem_image.2 ⟨c, hc, rfl⟩, hxc⟩

private theorem finite_range_of_sb_local {X : Type} [TopologicalSpace X] {f : X → ℂ} (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) : (Set.range f).Finite := by
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (fun w => f ⁻¹' {w}) (fun w => hf _)
    fun x _ => Set.mem_iUnion.2 ⟨f x, rfl⟩
  refine (t.finite_toSet.insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : f x = 0
  · exact Or.inl hx
  · simpa using Or.inr (by simpa using ht (subset_tsupport f hx))

private theorem sb_le_span_local (X : Type) [TopologicalSpace X] :
    GlobalTheory.WeilM.SB X ≤ Submodule.span ℂ
      ((fun K : Set X => K.indicator (1 : X → ℂ)) '' {K : Set X | IsCompact K ∧ IsOpen K}) := by
  classical
  rintro f ⟨hf, hcs⟩
  have hfin := finite_range_of_sb_local hf hcs
  have hsum : f = ∑ c ∈ hfin.toFinset.erase 0, c • (f ⁻¹' {c}).indicator (1 : X → ℂ) := by
    funext x
    rw [Finset.sum_apply]
    by_cases hx : f x = 0
    · rw [hx]
      refine (Finset.sum_eq_zero fun c hc => ?_).symm
      have hc0 : c ≠ 0 := (Finset.mem_erase.1 hc).1
      have : x ∉ f ⁻¹' {c} := by simp [hx, Ne.symm hc0]
      simp [Set.indicator_of_notMem this]
    · rw [Finset.sum_eq_single (f x)]
      · simp
      · intro c _ hcx
        have : x ∉ f ⁻¹' {c} := by simp [Ne.symm hcx]
        simp [Set.indicator_of_notMem this]
      · intro h
        exact absurd (Finset.mem_erase.2 ⟨hx, by simp⟩) h
  rw [hsum]
  refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ (Submodule.subset_span ⟨f ⁻¹' {c}, ⟨?_, hf _⟩, rfl⟩)
  have hc0 : c ≠ 0 := (Finset.mem_erase.1 hc).1
  refine hcs.isCompact.of_isClosed_subset (hf.isClosed_fiber c) fun x hx => subset_tsupport f ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
  simp [Function.mem_support, hx, hc0]

private theorem rank_sb_le_aleph0_local (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    Module.rank ℂ (GlobalTheory.WeilM.SB X) ≤ Cardinal.aleph0 := by
  refine (Submodule.rank_mono (sb_le_span_local X)).trans ((rank_span_le _).trans ?_)
  exact Cardinal.mk_le_aleph0_iff.2 ((countable_compactOpen_local X).image _).to_subtype

private theorem rank_sb_localField_le_local {F : Type} [Field F] [NumberField F]
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (κ : Type) [Fintype κ] :
    Module.rank ℂ (GlobalTheory.WeilM.SB (κ → Fv F v)) ≤ Cardinal.aleph0 := by
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  haveI := GlobalTheory.LocAtTopology.secondCountable_localField (Fv F v)
  exact rank_sb_le_aleph0_local _

theorem GlobalTheory.SquareAgree.rank_polarization_pi_le_aleph0 : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    Module.rank ℂ Pi ≤ Cardinal.aleph0 := by
  intro _ _ D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB _ _ hO hT R Rf _ Pm rf rl p p' hm
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hO.psi ▸ hT.base.std
  let S := GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank))
  let T : S →ₗ[ℂ] (WO W X → ℂ) :=
    { toFun := fun Φ x => GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho ψ (cA.symm x) Φ.1)
      map_add' := fun Φ Ψ => funext fun x => by
        have e : Γ.M.co.rho ψ (cA.symm x) (Φ.1 + Ψ.1) = Γ.M.co.rho ψ (cA.symm x) Φ.1 + Γ.M.co.rho ψ (cA.symm x) Ψ.1 := by
          funext z; simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.add_apply]; ring
        simp only [Submodule.coe_add, Pi.add_apply, e]
        exact GlobalTheory.WeilM.thetaSum_add _ (GlobalTheory.HeisSchA.rho_mem_schA Γ.M ψ hstd _ _ Φ.2) (GlobalTheory.HeisSchA.rho_mem_schA Γ.M ψ hstd _ _ Ψ.2)
      map_smul' := fun c Φ => funext fun x => by
        have e : Γ.M.co.rho ψ (cA.symm x) (c • Φ.1) = c • Γ.M.co.rho ψ (cA.symm x) Φ.1 := by
          funext z; simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]; ring
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, e]
        exact GlobalTheory.WeilM.thetaSum_smul _ c _ }
  let Q := (algD Γ.M Bs.ψ Bs.emb).comap S.subtype
  have hle : algF ψ θ true A B ≤ Q.map T := by
    intro Φ hΦ
    obtain ⟨ΦD, hD, hDat⟩ := hO.algA Φ hΦ
    refine ⟨⟨ΦD, hDat.1⟩, hD, funext fun x => ?_⟩
    have := hDat.2 (cA.symm x)
    rw [AddEquiv.apply_symm_apply] at this
    exact this
  have hQ : Module.rank ℂ Q ≤ Module.rank ℂ (algD Γ.M Bs.ψ Bs.emb) := by
    rw [(Submodule.equivMapOfInjective S.subtype Subtype.val_injective Q).rank_eq]
    exact Submodule.rank_mono (Submodule.map_comap_le _ _)
  have hD : Module.rank ℂ (algD Γ.M Bs.ψ Bs.emb) ≤ Cardinal.aleph0 :=
    GlobalTheory.T.rank_algebraicData_schrodingerModel_le_aleph0 Γ.M Bs.ψ Bs.emb hT.geo.hM (GlobalTheory.T.rank_polynomialFock_schrodingerModel_le_aleph0 Bs Γ.M hT.base hT.geo.hV hT.geo.hW hT.geo.hM) (fun v => rank_sb_localField_le_local v _)
  calc Module.rank ℂ Pm = Module.rank ℂ (⊤ : Submodule ℂ Pm) := (rank_top ℂ Pm).symm
    _ = Module.rank ℂ ((algF ψ θ true A B).map p) := by rw [hm.mapA.onto]
    _ ≤ Module.rank ℂ (algF ψ θ true A B) := rank_map_le _ _
    _ ≤ Module.rank ℂ (Q.map T) := Submodule.rank_mono hle
    _ ≤ Module.rank ℂ Q := rank_map_le _ _
    _ ≤ _ := hQ.trans hD
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LieSecondOrderOfRealLift
section
noncomputable section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl
namespace GlobalTheory.RealLift.LieSecondPf
theorem lie_second_order_of_real_lift : _root_.GlobalTheory.FunPr.ThetaLocalInputs → DerEx → FockEx → VacLine → LieScalar → LieSecond := by
  intro _ hD hF hV hL F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ om χ m hCM hψ hFr hΦ hW hχ
  obtain ⟨hU, dd, omd, hdd, hWS, hres⟩ := hW
  obtain ⟨c, hc⟩ := hL F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ om hCM hψ hFr hΦ hU
  have hFrd := GlobalTheory.T.doubled_hermitian_space_frame_of_frame F E α β P Q R S τ JA JB a b A C hFr
  obtain ⟨Φd, hΦd⟩ := hF F E σ α (β ⊕ β) (κ ⊕ κ) P Q (R + S) (S + R) ψ τ JA (dbl JB) dd a b A
    (fun w => dblM (C w)) hCM hψ hFrd
  obtain ⟨cd, hcd⟩ := hL F E σ α (β ⊕ β) (κ ⊕ κ) P Q (R + S) (S + R) ψ τ JA (dbl JB) dd a b A
    (fun w => dblM (C w)) Φd omd hCM hψ hFrd hΦd hWS.2.1
  have key : ∀ w (Y : Mat R S), c w * Y.trace = (m w : ℂ) / 2 * Y.trace := by
    intro w Y
    rcases Nat.eq_zero_or_pos (R + S) with h0 | hpos
    · have hR : R = 0 := by omega
      have hS : S = 0 := by omega
      subst hR hS
      have : Y.trace = 0 := by simp [Matrix.trace]
      rw [this, mul_zero, mul_zero]
    · have hbox := GlobalTheory.T.doubledFockVacuum_eq_smul_vacuum_mul_conj hD hV F E σ α β κ P Q R S ψ τ JA JB d dd a b A C Φ Φd hCM hψ hFr hΦ hdd hΦd
      have hl := GlobalTheory.T.diagonal_integral_invariant_form_diagonalLagrangian F E σ α β κ ψ JA JB d dd hψ hdd
      have hne : (∫ x : κ → mixedEmbedding.mixedSpace F,
          Φd (PiTensorProduct.tprod ℂ fun _ => 1) (Sum.elim x x)) ≠ 0 := by
        obtain ⟨z, hz, hzx⟩ := hbox
        have h1 : ∀ x : κ → mixedEmbedding.mixedSpace F, Φd (PiTensorProduct.tprod ℂ fun _ => 1) (Sum.elim x x) =
            z * (Φ (PiTensorProduct.tprod ℂ fun _ => 1) x * star (Φ (PiTensorProduct.tprod ℂ fun _ => 1) x)) := by
          intro x
          rw [hzx, Sum.elim_comp_inl, Sum.elim_comp_inr, mul_assoc]
        simp_rw [h1]
        rw [MeasureTheory.integral_const_mul]
        refine mul_ne_zero hz (GlobalTheory.T.archimedeanSchwartz_integral_mul_star_ne_zero F κ _ ?_)
        intro h0
        exact GlobalTheory.T.tprod_constant_polynomials_ne_zero F P Q R S (hΦ.1 (by rw [h0, map_zero]))
      have h1 := GlobalTheory.T.doubledSpace_splitting_constant_half_realPlaces F E σ α β κ P Q R S ψ τ JA JB dd a b A C Φd omd χ m cd hCM hψ hFr hWS hχ hcd hl hne hpos w
      have h2 := GlobalTheory.T.realPlace_splittingConstant_eq_doubledSpace F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ Φd om omd c cd hCM hψ hΦ hres hc hcd hbox hpos w
      rw [h2, h1]
  intro γ hγ Y hY T
  have e : (fun w => fockAct2 P Q R S (Y w) + (((m w : ℂ) / 2) * (Y w).trace) • (1 : Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))) =
      fun w => fockAct2 P Q R S (Y w) + (c w * (Y w).trace) • 1 := by
    funext w
    rw [key w (Y w)]
  have := hc γ hγ Y hY T
  rw [← e] at this
  exact this
end GlobalTheory.RealLift.LieSecondPf
end
end

section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_lift_lie_second_order : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.FockEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar → GlobalTheory.RealLift.LieSecond := by
  first | exact @_root_.GlobalTheory.RealLift.LieSecondPf.lie_second_order_of_real_lift | exact _root_.GlobalTheory.RealLift.LieSecondPf.lie_second_order_of_real_lift | (intros; apply _root_.GlobalTheory.RealLift.LieSecondPf.lie_second_order_of_real_lift <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaPairLiftCuspidalOfHypotheses
section
namespace GlobalTheory.PairLift
theorem thetaPairLift_cuspidal_of_hypotheses : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal := fun h =>
  liftsCuspidal_of_functoriality h.discreteSeriesCover h.harishChandraModules h.cuspRapidDecay h.casselmanWallach
end GlobalTheory.PairLift
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_thetaLift_cuspidal : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal := by
  first | exact @_root_.GlobalTheory.PairLift.thetaPairLift_cuspidal_of_hypotheses | exact _root_.GlobalTheory.PairLift.thetaPairLift_cuspidal_of_hypotheses | (intros; apply _root_.GlobalTheory.PairLift.thetaPairLift_cuspidal_of_hypotheses <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeilRepresentationSquareComm
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.SquareComm.WeilOfTriple
theorem exists_weilPair_of_triple : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (W W₁ X : HSp D) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
      ∃ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA ∧ IsWeil ψ false W₁ X α (α / β) ωB := by
  intro hP D ψ hψ W W₁ X α β h
  obtain ⟨⟨ωA, hA⟩, ⟨ωB, hB⟩⟩ :=
    GlobalTheory.SquareSt.Model.exists_weil_of_isTriple hP.weilRepresentationUnitaryPair hψ h
  exact ⟨ωA, ωB, hA, hB⟩
end GlobalTheory.SquareComm.WeilOfTriple
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentation_square_comm : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (W W₁ X : HSp D) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
      ∃ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA ∧ IsWeil ψ false W₁ X α (α / β) ωB := by
  first | exact @_root_.GlobalTheory.SquareComm.WeilOfTriple.exists_weilPair_of_triple | exact _root_.GlobalTheory.SquareComm.WeilOfTriple.exists_weilPair_of_triple | (intros; apply _root_.GlobalTheory.SquareComm.WeilOfTriple.exists_weilPair_of_triple <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedDownwardThetaLiftIsSmoothAutomorphic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.DnLiftAut
theorem downward_theta_lift_isSmoothAutomorphic : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → IsAutFunSm R.θ (G.P i).V (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ φ hφ hint
  have hθ : IsInfFam R.θ := hR.inf
  have hW := (hG.arrows.dn i hi).weil
  have hκ := GlobalTheory.Mem.Lift.isKerSys_thKer hθ hW.std (GlobalTheory.Ker.isWeak_of_datum hW) hW.om_cont
  have hm := hG.meas.P (i + 1) hi
  have hq0 : (G.mP (i + 1)).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.P (i + 1)).V) (G.mP (i + 1)).fd (G.mP (i + 1)).ν := by
    by_cases hd : i + 1 = D.R.m
    · exact ⟨(hm.1 hd).1.1, (hm.1 hd).2⟩
    · exact ⟨(hm.2 hd).1.1, (hm.2 hd).2⟩
  obtain ⟨ν₁, hH, hF, hI⟩ := (GlobalTheory.SgnIdent.sgnLaw_holds D R.θ hθ true (G.P (i + 1)).V).meas _ _ hq0.1 hq0.2
  have hL' := GlobalTheory.SgnIdent.sgnLaw_holds D R.θ hθ true (G.P (i + 1)).V
  have hc : GlobalTheory.Mem.Th.IsCuspForm R.θ (GlobalTheory.Grid.sgn true (G.P (i + 1)).V) (fun g => φ (GlobalTheory.Grid.ofSgn true (G.P (i + 1)).V g)) :=
    ⟨(GlobalTheory.SgnFun.isAutFunSm_sgn_true hL' φ).2 hφ.1, (GlobalTheory.SgnFun.isCuspFun_sgn_true hL' φ).2 hφ.2.1⟩
  have key := hκ.lift hP.cuspRapidDecay hθ ⟨hH, hF⟩ hc ⟨Φ, hΦ⟩
  have e : (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) =
      fun h => ∫ g in GlobalTheory.Grid.ofSgn true (G.P (i + 1)).V ⁻¹' (G.mP (i + 1)).fd,
        GlobalTheory.Mem.Lift.thKer R.ψ (GlobalTheory.Grid.sgn true (G.P (i + 1)).V) (G.P i).V ((G.dn i).ω.toSgn true) ⟨Φ, hΦ⟩ g h *
          φ (GlobalTheory.Grid.ofSgn true (G.P (i + 1)).V g) ∂ν₁ :=
    funext fun h => ((hI fun g => thetaKO (G.dn i).ω g h Φ * φ g).2).symm
  rw [e]
  exact key.2
end GlobalTheory.DnLiftAut
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_downward_theta_lift_isSmoothAutomorphic : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → IsAutFunSm R.θ (G.P i).V (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) := by
  first | exact @_root_.GlobalTheory.DnLiftAut.downward_theta_lift_isSmoothAutomorphic | exact _root_.GlobalTheory.DnLiftAut.downward_theta_lift_isSmoothAutomorphic | (intros; apply _root_.GlobalTheory.DnLiftAut.downward_theta_lift_isSmoothAutomorphic <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaKernelLocalOperatorAction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix Filter Topology
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.ThK.LocalOps
end GlobalTheory.ThK.LocalOps
namespace GlobalTheory.ThK.LocalOps
theorem theta_kernel_local_operators_act (_hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) : GlobalTheory.ThK.ActsEx := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v
  have hex : ∀ x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J, x.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v) →
      x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (evFin F v) → ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v),
        ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om x) φ φ₁ :=
    fun x hx1 hx2 φ hφ => acts_exists hP v x hx1 hx2 φ hφ
  refine ⟨fun g hg h hh φ hφ => ?_, fun u hu φ hφ => ?_, GlobalTheory.T.weilRep_smooth_at_finitePlace B X W M χX χW om r s r' s' hP v hex⟩
  · obtain ⟨φ₁, h1, h2⟩ := hex (g, h) hg hh φ hφ
    exact ⟨φ₁, ⟨h1, h2⟩, fun φ₂ hφ₂ => acts_unique v _ hφ hφ₂.2 h2⟩
  · refine ⟨GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u) φ,
      ⟨GlobalTheory.SchrSB.schr_mem_SB B.ψ hP.base.std.1 v _ φ hφ, GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v u hu φ⟩,
      fun φ₂ hφ₂ => acts_unique v _ hφ hφ₂.2 (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v u hu φ)⟩
end GlobalTheory.ThK.LocalOps
namespace GlobalTheory.ThK.LocalOps
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
end GlobalTheory.ThK.LocalOps
namespace GlobalTheory.ThK.LocalOps
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
end GlobalTheory.ThK.LocalOps
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_kernel_local_operator_action : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.ThK.ActsEx := by
  first | exact @_root_.GlobalTheory.ThK.LocalOps.theta_kernel_local_operators_act | exact _root_.GlobalTheory.ThK.LocalOps.theta_kernel_local_operators_act | (intros; apply _root_.GlobalTheory.ThK.LocalOps.theta_kernel_local_operators_act <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HasTypeAtCuspOfCuspValueType
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.CuspValueType
section Model
open Matrix Formalism.REAL Formalism.MainNotions.S _root_.Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
end Model
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice _root_.Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Matrix
open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
end GlobalTheory.CuspValueType
theorem GlobalTheory.CuspValueType.hasTypeAt_cusp_of_cusp_value_type : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam (D := D) θ → ∀ (N : GlobalTheory.Grid.Node D), N.V.SigOK → ∀ F ∈ N.Cusp θ, ∀ (w : SmT N.M) (τ : D.what₂.Tau), GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ N.V τ (N.S τ) (F w) := by
  intro hP D θ hθ N hN F hF w τ
  have hgood : GoodPar N.V.rank (N.V.sig (tauE D τ)).1 (N.V.sig (tauE D τ)).2 (N.S τ) :=
    ⟨N.M.lam τ, N.M.ε τ, N.M.enum τ, GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (N.M.enum τ).1 (N.M.ds τ),
      GlobalTheory.TypeAtCompare.card_eq_of_congr (N.M.fr_unit τ) (N.M.fr_gram τ) (hN (tauE D τ))⟩
  have key : ∀ T, Mult.IsMultMap θ N.M ∅ 1 T → ∀ v, T v ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.typeSub θ N.V τ (N.S τ) := fun T hT v =>
    GlobalTheory.SeriesToClosure.hasTypeAt_of_isTypeAt θ N.V τ (N.S τ) (T v) hP.discreteSeriesUpqExists
      (GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hP.discreteSeriesHermitianUnique) hP.harishChandraModules
      hP.casselmanWallach hθ hN hgood (hT.aut v)
      (GlobalTheory.CuspValueType.isTypeAt_value θ hP.harishChandraModules N.M hT v τ)
  have main : ∀ T ∈ Mult.Mult θ N.M ∅ 1, ∀ w, PiTensorProduct.lift T w ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.typeSub θ N.V τ (N.S τ) := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem T hT =>
      intro w
      induction w using PiTensorProduct.induction_on with
      | smul_tprod r v =>
        rw [map_smul, PiTensorProduct.lift.tprod]
        exact Submodule.smul_mem _ r (key T hT v)
      | add a b ha hb =>
        rw [map_add (f := _)]
        exact Submodule.add_mem _ ha hb
    | zero =>
      intro w
      simp only [map_zero, LinearMap.zero_apply]
      exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      intro w
      rw [map_add (f := _), LinearMap.add_apply]
      exact Submodule.add_mem _ (ha w) (hb w)
    | smul c a _ ha =>
      intro w
      rw [map_smul, LinearMap.smul_apply]
      exact Submodule.smul_mem _ c (ha w)
  have hF' := (Mult.mem_multT θ N.M ∅ 1 F).1 hF
  have eF : F = PiTensorProduct.lift (PiTensorProduct.lift.symm F) := (LinearEquiv.apply_symm_apply _ F).symm
  rw [eF]
  exact main _ hF' w
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_value_has_prescribed_type : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam (D := D) θ → ∀ (N : GlobalTheory.Grid.Node D), N.V.SigOK → ∀ F ∈ N.Cusp θ, ∀ (w : SmT N.M) (τ : D.what₂.Tau), GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ N.V τ (N.S τ) (F w) := by
  first | exact @_root_.GlobalTheory.CuspValueType.hasTypeAt_cusp_of_cusp_value_type | exact _root_.GlobalTheory.CuspValueType.hasTypeAt_cusp_of_cusp_value_type | (intros; apply _root_.GlobalTheory.CuspValueType.hasTypeAt_cusp_of_cusp_value_type <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaActionLocalAtArchimedeanPlace
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
noncomputable section
namespace GlobalTheory.ArchLocality
theorem theta_action_local_at_archimedean_place : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) f f₁ := by
  intro _ F E _ _ _ _ _ σ n d X W M ψ χX χW om _ hψ hW h hh f
  have hS := IsUWeilPair.isUSplitting hW
  set T := om (1, h) with hTdef
  have hpres : ∀ Φ ∈ schA F (Fin n × Fin d), T Φ ∈ schA F (Fin n × Fin d) := fun Φ hΦ => hS.pres (1, h) Φ hΦ
  have hcomm := comm_fin M ψ χX χW om hW h hh
  obtain ⟨r₀, hr₀1, hr₀⟩ := ref_fun (F := F) (Fin n × Fin d)
  set Φ₀ := tens (evI F) (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) r₀ with hΦ₀
  have hm₀ : Φ₀ ∈ schA F _ := (hr₀ f).2
  obtain ⟨f₁, hf₁⟩ := res_arch (T Φ₀) (hpres Φ₀ hm₀)
  refine ⟨f₁, fun r hr => ?_⟩
  funext y
  set u : AF F := (0, 1) with hu
  have hu0 : evI F u = 0 := evI_fin
  have htr : ∀ Ψ ∈ schA F (Fin n × Fin d), T (fun w => Ψ (w + u • (-y))) = fun w => T Ψ (w + u • (-y)) := by
    intro Ψ hΨ
    have e := hcomm u hu0 (-y) 0 Ψ hΨ
    have hs0 : ∀ G : (Fin n × Fin d → AF F) → ℂ, schr ψ (u • (-y), u • (0 : Fin n × Fin d → AF F)) G =
        fun w => G (w + u • (-y)) := by
      intro G; funext w; simp [schr]
    rw [hs0, hs0] at e
    exact e
  set Φ₁ := tens (evI F) (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) r with hΦ₁
  set Φ₂ : (Fin n × Fin d → AF F) → ℂ := r y • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
  have hm₂ : Φ₂ ∈ schA F _ := Submodule.smul_mem _ _ (GlobalTheory.SchwartzTranslation.schA_add_const _ _ hm₀)
  have hz2 : ∀ z : Fin n × Fin d → AF F, At (evI F) z → ∀ i, (z i).2 = 0 := by
    intro z hz i
    have := congrArg Prod.snd (congrFun (hz u hu0) i)
    change (u * z i).2 = (0 : AF F).2 at this
    have e : (u * z i).2 = (z i).2 := one_mul _
    rw [e] at this
    exact this
  have hvan : ∀ z, At (evI F) z → (Φ₁ - Φ₂) (y + z) = 0 := by
    intro z hz
    have e1 : r (y + z) = r y := hr.1 y z hz
    have e2 : (fun i => evI F ((y + z + u • (-y)) i)) = fun i => evI F ((y + z) i) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, evI_add, evI_mul, hu0, zero_mul, add_zero]
    have e3 : r₀ (y + z + u • (-y)) = 1 := by
      refine hr₀1 _ fun i => ?_
      change ((y i + z i) + u * -(y i)).2 = 0
      change (y i).2 + (z i).2 + 1 * -(y i).2 = 0
      rw [hz2 z hz i]
      ring
    simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, tens]
    rw [e2, e3, e1]
    ring
  have h0 := fibre ψ hψ T hcomm (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hvan
  rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
  have hy0 : y + u • (-y) = fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (evI F (y i)), 0) : AF F) := by
    funext i
    refine Prod.ext ?_ ?_
    · change (y i).1 + 0 * -(y i).1 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        (InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1)
      rw [RingEquiv.symm_apply_apply]
      ring
    · change (y i).2 + 1 * -(y i).2 = 0
      ring
  have h2 : T Φ₂ y = r y * f₁ (fun i => evI F (y i)) := by
    rw [hΦ₂, map_smul, htr Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hy0, hf₁]
  rw [h0, h2]
  simp only [tens]
  ring
end GlobalTheory.ArchLocality
end
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_action_archimedean_locality : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) f f₁ := by
  first | exact @_root_.GlobalTheory.ArchLocality.theta_action_local_at_archimedean_place | exact _root_.GlobalTheory.ArchLocality.theta_action_local_at_archimedean_place | (intros; apply _root_.GlobalTheory.ArchLocality.theta_action_local_at_archimedean_place <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedMovedLatticeAction
section
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
noncomputable section
namespace GlobalTheory.MovedHomLat
open Matrix
variable {D : D7}
set_option synthInstance.maxHeartbeats 400000
end GlobalTheory.MovedHomLat
open GlobalTheory.MovedHomLat in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.MovedDict.moved_lattice_action_compat : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    (∀ w ∈ latO _ _ (ch.S.N.latS p : Set _) (ch.S.N.latT p : Set _) (fun _ => True), actO _ _ (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).1 (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).2 w ∈ latO _ _ (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (fun _ => True)) ∧
    (∀ w' ∈ latO _ _ (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (fun _ => True), ∃ w ∈ latO _ _ (ch.S.N.latS p : Set _) (ch.S.N.latT p : Set _) (fun _ => True), actO _ _ (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).1 (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).2 w = w') := by
  intro _ _ D Γ _ _ Pl0 T A Ks _ _ _ R ch _ p hp x y
  have hn := DefPair.nodes hp
  cases p with
  | chi i j =>
    rw [show inV (frS ch.S.N (.chi i j)) (srcLat ch.S.toGridChoice (.chi i j) x y) = _ from
        movedLat_eq ch.S.toGridChoice _ hn.2 y,
      show inV (frT ch.S.N (.chi i j)) (tgtLat ch.S.toGridChoice (.chi i j) x y) = _ from
        movedLat_eq ch.S.toGridChoice _ hn.1 x]
    let N := ch.S.N
    let ky : Formalism.L2.Theta.GA D (ch.G.V (.grid (i + 1) j)) := ((y * N.u (.grid (i + 1) j) : FinPt ch.G (.grid (i + 1) j)) : Formalism.L2.Theta.GA D _)
    let kx : Formalism.L2.Theta.GA D (ch.G.V (.grid i j)) := ((x * N.u (.grid i j) : FinPt ch.G (.grid i j)) : Formalism.L2.Theta.GA D _)
    have H := actO_latO_onto (negSp (ch.G.V (.grid (i + 1) j))) (ch.G.V (.grid i j)) (negGA _ ky) kx
      (colLat (N.fr (.grid (i + 1) j)))
      (Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE (ch.G.V (.grid (i + 1) j)) ky) (colLat (N.fr (.grid (i + 1) j))))
      (colLat (N.fr (.grid i j)))
      (Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE (ch.G.V (.grid i j)) kx) (colLat (N.fr (.grid i j))))
      (fwd (ch.G.V (.grid (i + 1) j)) ky _ (colLat_fin _) (colLat_span _))
      (fwd (ch.G.V (.grid i j)) kx _ (colLat_fin _) (colLat_span _))
      (bwd (ch.G.V (.grid (i + 1) j)) ky _)
      (bwd (ch.G.V (.grid i j)) kx _)
    exact H
  | top t j =>
    rw [show inV (frS ch.S.N (.top t j)) (srcLat ch.S.toGridChoice (.top t j) x y) = _ from
        movedLat_eq ch.S.toGridChoice _ hn.1 x,
      show inV (frT ch.S.N (.top t j)) (tgtLat ch.S.toGridChoice (.top t j) x y) = _ from
        movedLat_eq ch.S.toGridChoice _ hn.2 y]
    let N := ch.S.N
    let kx : Formalism.L2.Theta.GA D (ch.G.V (.top j)) := ((x * N.u (.top j) : FinPt ch.G (.top j)) : Formalism.L2.Theta.GA D _)
    let ky : Formalism.L2.Theta.GA D (ch.G.V (.top (j + 1))) := ((y * N.u (.top (j + 1)) : FinPt ch.G (.top (j + 1))) : Formalism.L2.Theta.GA D _)
    have H := actO_latO_onto (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) kx ky
      (colLat (N.fr (.top j)))
      (Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE (ch.G.V (.top j)) kx) (colLat (N.fr (.top j))))
      (colLat (N.fr (.top (j + 1))))
      (Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE (ch.G.V (.top (j + 1))) ky) (colLat (N.fr (.top (j + 1)))))
      (fwd (ch.G.V (.top j)) kx _ (colLat_fin _) (colLat_span _))
      (fwd (ch.G.V (.top (j + 1))) ky _ (colLat_fin _) (colLat_span _))
      (bwd (ch.G.V (.top j)) kx _)
      (bwd (ch.G.V (.top (j + 1))) ky _)
    exact H
  | mu t i j => exact absurd hp (by simp [DefPair])
  | core i => exact absurd hp (by simp [DefPair])
end
end

section
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
theorem _root_.GlobalTheory.T.twisted_moved_lattice_action : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    (∀ w ∈ latO _ _ (ch.S.N.latS p : Set _) (ch.S.N.latT p : Set _) (fun _ => True), actO _ _ (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).1 (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).2 w ∈ latO _ _ (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (fun _ => True)) ∧
    (∀ w' ∈ latO _ _ (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (fun _ => True), ∃ w ∈ latO _ _ (ch.S.N.latS p : Set _) (ch.S.N.latT p : Set _) (fun _ => True), actO _ _ (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).1 (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).2 w = w') := by
  first | exact @_root_.GlobalTheory.MovedDict.moved_lattice_action_compat | exact _root_.GlobalTheory.MovedDict.moved_lattice_action_compat | (intros; apply _root_.GlobalTheory.MovedDict.moved_lattice_action_compat <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FirstFactorMapThetaSumPureTensor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.TripleAssembly.PureImage
theorem firstFactorMap_thetaSum_pure_tensor : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
      ∀ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)))
        (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
        (∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = Γ.M.vac v) →
        (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb →
        GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i))) =
          ∑ i, R.p (f i) ⊗ₜ[ℂ] GlobalTheory.SmallThetaModules.pureT (GlobalTheory.TripleAssembly.vacIm Γ Rf) (fun v => Rf.p v (φ i v)) := by
  intro hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hA hB e Bs Γ Xc om om' h tA tB R Rf hm m f φ hφ hmem
  classical
  have hg := hm.triple.geo
  have hψ' : Bs.ψ = ψ := h.ψ
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hψ' ▸ hm.triple.base.std
  obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
  have dV : Γ.V.J.det ≠ 0 := det_ne_of_sig_map (Bs.emb w).1 1 (by rw [one_smul]; exact hg.hV.sig w)
  have dW : Γ.W.J.det ≠ 0 := det_ne_of_sig_map (Bs.emb w).1 Complex.I (hg.hW.sig w)
  have gA : (sgn true W).gram.det ≠ 0 := by
    have e1 : (sgn true W).gram = -W.gram := rfl
    rw [h.JW, one_smul] at dV
    rw [e1, Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) dV
  obtain ⟨T, hT, hinj⟩ := GlobalTheory.T.thetaTransform_darbouxModel_linear_injective D Γ.M ψ (sgn true W).gram e (hψ' ▸ hg.hM) hstd dV dW gA
  have hS := GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz _ _ _ Γ.M Bs.ψ Bs.emb hg.hM
  have Hq : ∃ q : (Matrix (Fin X.rank) (Fin W.rank) (AE D) → ℂ) →ₗ[ℂ] PiT R Γ Rf,
      ∀ Ψ ∈ darbAlg Γ.M Bs.ψ Bs.emb, q (GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e Ψ) =
        liftPure Γ.M R.p Rf.p (vacIm Γ Rf) Ψ := by
    obtain ⟨q, hq⟩ := exists_factor_inj T _ (fun x hx => hinj x (hS hx)) (liftPure Γ.M R.p Rf.p (vacIm Γ Rf))
    exact ⟨q, fun Ψ hΨ => by rw [← hT Ψ (hS hΨ)]; exact hq Ψ hΨ⟩
  have HL := GlobalTheory.T.weil_model_projection_factorisation D.sp.cm.sig Γ.V Γ.W Γ.M Bs.ψ hg.hM _ R.p _ Rf.p (vacIm Γ Rf)
    (Filter.Eventually.of_forall fun _ => rfl)
  have hL : ∀ i, liftPure Γ.M R.p Rf.p (vacIm Γ Rf) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) =
      R.p (f i) ⊗ₜ[ℂ] GlobalTheory.SmallThetaModules.pureT (vacIm Γ Rf) (fun v => Rf.p v (φ i v)) := by
    intro i
    unfold liftPure
    rw [dite_eq_left HL]
    exact HL.choose_spec (f i) (φ i) (hφ i).1 (hφ i).2
  unfold mapA thetaLift
  set_option synthInstance.maxHeartbeats 100000 in
    rw [dite_eq_left Hq, Hq.choose_spec _ hmem, map_sum]
  exact Finset.sum_congr rfl fun i _ => hL i
end GlobalTheory.TripleAssembly.PureImage
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tripleProduct_image_thetaSum_pure : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
      ∀ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)))
        (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
        (∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = Γ.M.vac v) →
        (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb →
        GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i))) =
          ∑ i, R.p (f i) ⊗ₜ[ℂ] GlobalTheory.SmallThetaModules.pureT (GlobalTheory.TripleAssembly.vacIm Γ Rf) (fun v => Rf.p v (φ i v)) := by
  first | exact @_root_.GlobalTheory.TripleAssembly.PureImage.firstFactorMap_thetaSum_pure_tensor | exact _root_.GlobalTheory.TripleAssembly.PureImage.firstFactorMap_thetaSum_pure_tensor | (intros; apply _root_.GlobalTheory.TripleAssembly.PureImage.firstFactorMap_thetaSum_pure_tensor <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaKernelFundamentalProperties
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaPairModerateGrowth
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
namespace GlobalTheory.ThetaModGrowthPair
theorem theta_moderate_growth : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖theta om Φ g h‖ ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  have hlat := GlobalTheory.T.adelicThetaSum_norm_le_polynomial_scale
  have hfin := GlobalTheory.T.weilRep_rational_support_common_denominator
  have harch := GlobalTheory.T.weilRepresentation_pointwise_archimedeanDecay_bound
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  obtain ⟨N₀, k₂, C₂, hL⟩ := hlat F (Fin n × Fin d)
  obtain ⟨C₁, k₁, hA⟩ := harch F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ N₀
  obtain ⟨C₃, k₃, hF⟩ := hfin F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  refine ⟨|C₂| * |C₁| * |C₃| ^ k₂, k₁ + k₃ * k₂, fun g h => ?_⟩
  obtain ⟨m, hm1, hmC, hsupp⟩ := hF g h
  set H : ℝ := (ht g : ℝ) * ht h with hH
  have hH0 : 0 ≤ H := by rw [hH]; positivity
  have hb := hL (C₁ * H ^ k₁) m (om (g, h) Φ) hm1 (fun ξ => hA g h _) hsupp
  have hA0 : 0 ≤ C₁ * H ^ k₁ :=
    le_trans (by positivity) (hA g h (fun i => algebraMap F (AF F) ((0 : Fin n × Fin d → F) i)))
  have hm0 : (0 : ℝ) ≤ (m : ℝ) ^ k₂ := by positivity
  have hmk : (m : ℝ) ^ k₂ ≤ (|C₃| * H ^ k₃) ^ k₂ :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (hmC.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hH0 _))) _
  have hC1 : C₁ * H ^ k₁ ≤ |C₁| * H ^ k₁ := mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hH0 _)
  show ‖thetaSum F (om (g, h) Φ)‖ ≤ _
  calc ‖thetaSum F (om (g, h) Φ)‖ ≤ C₂ * (C₁ * H ^ k₁) * (m : ℝ) ^ k₂ := hb
    _ ≤ |C₂| * (C₁ * H ^ k₁) * (m : ℝ) ^ k₂ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hA0) hm0
    _ ≤ |C₂| * (|C₁| * H ^ k₁) * (|C₃| * H ^ k₃) ^ k₂ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hC1 (abs_nonneg _)) hmk hm0 (mul_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (pow_nonneg hH0 _)))
    _ = |C₂| * |C₁| * |C₃| ^ k₂ * H ^ (k₁ + k₃ * k₂) := by rw [pow_add, pow_mul]; ring
end GlobalTheory.ThetaModGrowthPair
end

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_pair_moderate_growth : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖theta om Φ g h‖ ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  first | exact @_root_.GlobalTheory.ThetaModGrowthPair.theta_moderate_growth | exact _root_.GlobalTheory.ThetaModGrowthPair.theta_moderate_growth | (intros; apply _root_.GlobalTheory.ThetaModGrowthPair.theta_moderate_growth <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSumOmegaRational
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
noncomputable section
namespace GlobalTheory.ThetaRatPair
theorem theta_sum_omega_rational : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP γ hγ γ' hγ' Φ hΦ
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have hX : X.J.det ≠ 0 := det_ne_zero_of_map X.J (B.emb w).1 (det_ne_zero_of_hasSig _ (hP.herm.sig w))
  have hW : W.J.det ≠ 0 := by
    refine det_ne_zero_of_map W.J (B.emb w).1 fun h0 => det_ne_zero_of_hasSig _ (hP.skew.sig w) ?_
    rw [Matrix.det_smul, h0, mul_zero]
  exact GlobalTheory.T.weilRep_rationalDarboux_fixes_thetaDistribution F E σ hP.base.cm B.ψ hP.base.std n d X.J W.J hP.herm.herm hX hP.skew.skew hW M.co
    hP.good.rat χX χW hP.hX hP.hW om hP.weil γ hγ γ' hγ' Φ hΦ
end GlobalTheory.ThetaRatPair
end
end

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_pair_sum_rational : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  first | exact @_root_.GlobalTheory.ThetaRatPair.theta_sum_omega_rational | exact _root_.GlobalTheory.ThetaRatPair.theta_sum_omega_rational | (intros; apply _root_.GlobalTheory.ThetaRatPair.theta_sum_omega_rational <;> assumption)
end
end

section
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
namespace GlobalTheory.ThKBasic
theorem theta_kernel_basic_properties : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.ThK.ThetaBasic := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hS := hP.weil.isUSplitting
  obtain ⟨l, hl, hlt⟩ := GlobalTheory.T.exists_admissibleForm_adelicThetaSum F (Fin n × Fin d)
  refine ⟨fun Φ hΦ => ⟨?_, ?_, _root_.GlobalTheory.T.theta_pair_moderate_growth hKP F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ⟩, ?_⟩
  · refine (hS.cont l hl Φ hΦ).congr fun x => ?_
    simp only [theta]
    exact hlt _ (hS.pres _ _ hΦ)
  · intro γ hγ γ' hγ' g h
    simp only [theta]
    have e : om (γ * g, γ' * h) Φ = om (γ, γ') (om (g, h) Φ) := by
      rw [← Module.End.mul_apply, ← map_mul]; rfl
    rw [e]
    exact _root_.GlobalTheory.T.theta_pair_sum_rational hKP F E σ B n d X W M χX χW om r s r' s' hP γ hγ γ' hγ' _ (hS.pres _ _ hΦ)
  · intro φ hφ g h
    obtain ⟨T, hT⟩ := hS.adm (g, h) l hl φ hφ
    refine T.continuous.congr fun f => ?_
    simp only [theta]
    have hm : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) φ ∈ schA F (Fin n × Fin d) :=
      Submodule.subset_span ⟨f, φ, hφ, rfl⟩
    rw [← hlt _ (hS.pres _ _ hm)]
    exact (hT f).symm
end GlobalTheory.ThKBasic
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_kernel_fundamental_properties : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.ThK.ThetaBasic := by
  first | exact @_root_.GlobalTheory.ThKBasic.theta_kernel_basic_properties | exact _root_.GlobalTheory.ThKBasic.theta_kernel_basic_properties | (intros; apply _root_.GlobalTheory.ThKBasic.theta_kernel_basic_properties <;> assumption)
end
end
