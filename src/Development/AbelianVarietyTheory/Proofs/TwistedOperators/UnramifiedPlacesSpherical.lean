module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabilizerFixesVacuumStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentConjugateToSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitScalarFourier
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilCompositionLines
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockMatrixCoefficientSplitsRealFiniteFactors
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JointHarmonicsLowestKTypeCoefficientReal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerStandardLeviAction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleGkLeMultiplicitySpan
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformGaussianVacuumIsFiniteDatum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedPlacesSpherical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.SphOffFinite

theorem isUnram_of_unramified {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h : Algebra.Unramified (𝓞 F) (𝓞 E)) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v := by
  intro P hP
  rw [Ideal.ramificationIdx_eq_one_iff]
  infer_instance

end GlobalTheory.SphOffFinite
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingSwap
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanOneParamEqProdCmTypeLines
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanOneParamEqProdCmTypeLines
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.ConjLineSplit

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (conjU continuous_conjU)
open GlobalTheory.ConjUTransport (conjUInv conjEquiv continuous_conjUInv)

theorem exists_lie_eq_exp {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (M : ℝ → Matrix (Fin n) (Fin n) ℂ) (hc : Continuous M)
    (h0 : M 0 = 1) (hm : ∀ s t, M (s + t) = M s * M t) (hU : ∀ t, (M t)ᴴ * H * M t = H) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, Yᴴ * H + H * Y = 0 ∧ ∀ t : ℝ, NormedSpace.exp (t • Y) = M t := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  obtain ⟨Y, hY⟩ := GlobalTheory.banach_oneParamGroup_eq_exp M hc h0 hm
  refine ⟨Y, ?_, hY⟩
  have hd : HasDerivAt M Y 0 := by
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0
    rw [zero_smul, NormedSpace.exp_zero, one_mul, funext hY] at h
    exact h
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun A => Aᴴ
      map_add' := fun A B => Matrix.conjTranspose_add A B
      map_smul' := fun c A => by rw [Matrix.conjTranspose_smul]; simp }
  have hT : HasDerivAt (fun t => (M t)ᴴ) Yᴴ 0 :=
    (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt 0 hd
  have hF := (hT.mul_const H).fun_mul hd
  rw [funext hU] at hF
  have huniq := hF.unique (hasDerivAt_const (0 : ℝ) H)
  rwa [h0, Matrix.conjTranspose_one, mul_one, one_mul] at huniq

variable {D : D7}

theorem finTens_eq_zero {z : AE D} (h : ∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F u = 0 → u • z = 0) :
    GlobalTheory.LFun.finTens D.host.F D.host.E z = 0 := by
  let e : AF D.host.F := ((0, 1) : Ainf D.host.F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)
  have he : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F e = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F)
  have h1 := congrArg (GlobalTheory.LFun.finTens D.host.F D.host.E) (h e he)
  rw [Algebra.smul_def, map_mul, map_zero] at h1
  have h2 : GlobalTheory.LFun.finTens D.host.F D.host.E (algebraMap (AF D.host.F) (AE D) e) = 1 := rfl
  rwa [h2, one_mul] at h1

theorem cA_smul (u : AF D.host.F) (z : AE D) : cA D (u • z) = u • cA D z :=
  map_smul (Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig) u z

theorem smul_cA_sub (u : AF D.host.F) {n : ℕ} (A : Matrix (Fin n) (Fin n) (AE D)) (i j : Fin n) :
    (u • (A.map (cA D) - 1)) i j = cA D ((u • (A - 1)) i j) := by
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, cA_smul, map_sub, Matrix.one_apply]
  split_ifs <;> simp

theorem conjU_mem_UAt_iff (W : HSp D) (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank)
    (hJ : Wd.J = (1 : D.host.E) • W.gram) (g : GA D W) :
    conjU W 1 hJ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Wd (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) ↔ g ∈ GinfC W := by
  have hone : ∀ a b : Fin W.rank, GlobalTheory.LFun.finTens D.host.F D.host.E ((1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) a b) =
      (1 : Matrix (Fin W.rank) (Fin W.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) a b := by
    intro a b
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  constructor
  · intro h
    show finHom W g = 1
    refine Units.ext (Matrix.ext fun a b => ?_)
    have h1 : GlobalTheory.LFun.finTens D.host.F D.host.E ((Formalism.L2.Theta.mt W g - 1) a b) = 0 := by
      refine finTens_eq_zero fun u hu => ?_
      have h2 : (u • ((Formalism.L2.Theta.mt W g).map (cA D) - 1)) a b = 0 := congrFun (congrFun (h u hu) a) b
      rw [smul_cA_sub] at h2
      have h3 := congrArg (cA D) h2
      rw [Formalism.L2.Theta.cA_cA, map_zero] at h3
      exact h3
    rw [Matrix.sub_apply, map_sub, hone, sub_eq_zero] at h1
    exact h1
  · intro hg u hu
    have hf : finHom W g = 1 := hg
    refine Matrix.ext fun a b => ?_
    show (u • ((Formalism.L2.Theta.mt W g).map (cA D) - 1)) a b = 0
    rw [smul_cA_sub, Matrix.smul_apply, GlobalTheory.KapXLine.smul_eq_zero_of_finTens hu, map_zero]
    rw [Matrix.sub_apply, map_sub, hone, sub_eq_zero]
    exact congrArg (fun k : GL (Fin W.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => k.1 a b) hf

theorem ext_of_infMat {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) {g h : GA D W} (hg : g ∈ GinfC W) (hh : h ∈ GinfC W)
    (e : ∀ τ, infMat D.sp.cm.sig W.gram (θ τ) g = infMat D.sp.cm.sig W.gram (θ τ) h) : g = h := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have a : (finHom W g).1 = (finHom W h).1 := by
    rw [show finHom W g = 1 from hg, show finHom W h = 1 from hh]
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)))
  · rw [RingHom.map_sub, sub_eq_zero]
    exact congrFun (congrFun a i) j
  · rw [RingHom.map_sub, RingHom.map_sub, sub_eq_zero]
    exact congrFun (congrFun (e τ) i) j


open Classical in
theorem infMat_prod {θ : InfFam D} (W : HSp D) (m : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (x : D.what₂.Tau → GA D W) (hx : ∀ τ, IsAtTau θ W τ (m τ) (x τ)) (τ : D.what₂.Tau) (l : List D.what₂.Tau)
    (hl : l.Nodup) : infMat D.sp.cm.sig W.gram (θ τ) (l.map x).prod = if τ ∈ l then m τ else 1 := by
  induction l with
  | nil => simpa using GlobalTheory.PointAtPlaceHom.infMat_one W (θ τ)
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, GlobalTheory.PointAtPlaceHom.infMat_mul, ih hl.2]
    by_cases c : τ = a
    · subst c
      rw [(hx τ).2.1, if_neg hl.1, if_pos List.mem_cons_self, Matrix.mul_one]
    · rw [(hx a).2.2 τ c, Matrix.one_mul]
      simp only [List.mem_cons, c, false_or]

theorem exists_eq_prod_oneP {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (g : ℝ → GA D W) (hc : Continuous g)
    (h0 : g 0 = 1) (hm : ∀ s t, g (s + t) = g s * g t) (hg : ∀ t, g t ∈ GinfC W) :
    ∃ Y : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ, (∀ τ, Y τ ∈ lieAt W τ) ∧
      ∀ t, g t = ((Finset.univ : Finset D.what₂.Tau).toList.map fun τ => oneP θ W τ (Y τ) t).prod := by
  have h1 : Continuous (matHom W) := continuous_subtype_val
  choose Y hY hexp using fun τ => exists_lie_eq_exp (gramAt D W τ) (fun t => infMat D.sp.cm.sig W.gram (θ τ) (g t))
    (continuous_matrix fun i j => (GlobalTheory.FockCompare.continuous_comp hθ τ).comp
      ((Units.continuous_val.comp (h1.comp hc)).matrix_elem i j))
    (by rw [h0, GlobalTheory.PointAtPlaceHom.infMat_one]) (fun s t => by rw [hm, GlobalTheory.PointAtPlaceHom.infMat_mul])
    (fun t => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ W (g t) τ)
  refine ⟨Y, hY, fun t => ext_of_infMat hθ W (hg t) ?_ fun τ => ?_⟩
  · refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
    exact GlobalTheory.PointAtPlaceHom.atTau_mem W τ _
  · rw [infMat_prod W _ _ (fun τ' => GlobalTheory.Mem.Lift.isAtTau_oneP hθ (hY τ') t) τ _ (Finset.nodup_toList _),
      if_pos (Finset.mem_toList.2 (Finset.mem_univ τ)), hexp]

theorem line_eq_prod : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (W : HSp D) (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank)
    (hJ : Wd.J = (1 : D.host.E) • W.gram), ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Wd,
    ∃ (Y : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
      (γs : D.what₂.Tau → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Wd.J)),
      (∀ τ, Y τ ∈ lieAt W τ) ∧ (∀ τ, γs τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Wd) ∧
      (∀ τ t, γs τ (Multiplicative.ofAdd t) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ (oneP θ W τ (Y τ) t)) ∧
      ∀ t, γ t = ((Finset.univ : Finset D.what₂.Tau).toList.map fun τ => γs τ t).prod := by
  intro D θ hθ W Wd hJ γ hγ
  let φ := conjEquiv W 1 one_ne_zero hJ
  obtain ⟨Y, hY, hprod⟩ := exists_eq_prod_oneP hθ W (fun t => φ.symm (γ (Multiplicative.ofAdd t)))
    ((continuous_conjUInv W 1 one_ne_zero hJ).comp (hγ.1.comp continuous_ofAdd))
    (by rw [ofAdd_zero, map_one, map_one]) (fun s t => by rw [ofAdd_add, map_mul, map_mul])
    (fun t => (conjU_mem_UAt_iff W Wd hJ _).1 (by
      have e : conjU W 1 hJ (φ.symm (γ (Multiplicative.ofAdd t))) = γ (Multiplicative.ofAdd t) := φ.apply_symm_apply _
      rw [e]
      exact hγ.2 _))
  let p : D.what₂.Tau → (Multiplicative ℝ →* GA D W) := fun τ =>
    { toFun := fun t => oneP θ W τ (Y τ) (Multiplicative.toAdd t)
      map_one' := GlobalTheory.Mem.Lift.oneP_zero hθ
      map_mul' := fun s t => GlobalTheory.Mem.Lift.oneP_add hθ (hY τ) _ _ }
  refine ⟨Y, fun τ => φ.toMonoidHom.comp (p τ), hY, fun τ => ⟨?_, fun t => ?_⟩, fun τ t => rfl, fun t => ?_⟩
  · exact (continuous_conjU W 1 hJ).comp ((GlobalTheory.Mem.Lift.continuous_oneP hθ (hY τ)).comp continuous_toAdd)
  · exact (conjU_mem_UAt_iff W Wd hJ _).2 (GlobalTheory.PointAtPlaceHom.atTau_mem W τ _)
  · have e := congrArg φ (hprod (Multiplicative.toAdd t))
    rw [φ.apply_symm_apply, map_list_prod, List.map_map] at e
    exact e

end GlobalTheory.ConjLineSplit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanOneParamEqProdCmTypeLinesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryArchimedeanOneParam_eq_prod_cmType_lines : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (W : HSp D) (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank)
    (hJ : Wd.J = (1 : D.host.E) • W.gram), ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Wd,
    ∃ (Y : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
      (γs : D.what₂.Tau → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Wd.J)),
      (∀ τ, Y τ ∈ lieAt W τ) ∧ (∀ τ, γs τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Wd) ∧
      (∀ τ t, γs τ (Multiplicative.ofAdd t) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ (oneP θ W τ (Y τ) t)) ∧
      ∀ t, γ t = ((Finset.univ : Finset D.what₂.Tau).toList.map fun τ => γs τ t).prod := by
  first | exact @GlobalTheory.ConjLineSplit.line_eq_prod | exact GlobalTheory.ConjLineSplit.line_eq_prod | (intros; apply GlobalTheory.ConjLineSplit.line_eq_prod <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section
namespace GlobalTheory.LineKillV

theorem isDatum_list_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} {M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd}
    {ψ : AddChar (AF F) ℂ} {Z : Type} {crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z}
    (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) {ι : Type} (l : List ι) (Ψ : ι → (Fin n × Fin d → AF F) → ℂ) (f : ι → Z → ℂ)
    (h : ∀ i, IsDatum M ψ crd (Ψ i) (f i)) : IsDatum M ψ crd (l.map Ψ).sum (l.map f).sum := by
  induction l with
  | nil => simpa using (GlobalTheory.SquareAgree.CoinvPass.isDatum_zero (M := M) (ψ := ψ) (crd := crd))
  | cons a l ih => simpa [List.map_cons, List.sum_cons] using GlobalTheory.SquareAgree.CoinvPass.isDatum_add hψ (h a) ih

end GlobalTheory.LineKillV

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalTypePreserved
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CuspTypeApproxUp

theorem norm_sub_sum_sigma_lt {E : Type*} [SeminormedAddCommGroup E] {m : ℕ} (I : E) (L : Fin m → E) (n : Fin m → ℕ)
    (J : ∀ k, Fin (n k) → E) {δ : ℝ} (hδ : 0 < δ) (h1 : ‖I - ∑ k, L k‖ < δ / 2)
    (h2 : ∀ k, ‖L k - ∑ j, J k j‖ < δ / (2 * (m + 1))) :
    ‖I - ∑ l : Fin (∑ k, n k), J (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2‖ < δ := by
  have hs : ∑ l : Fin (∑ k, n k), J (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2 = ∑ k, ∑ j, J k j := by
    rw [Equiv.sum_comp finSigmaFinEquiv.symm (fun x => J x.1 x.2), Fintype.sum_sigma]
  have hd : I - ∑ k, ∑ j, J k j = (I - ∑ k, L k) + ∑ k, (L k - ∑ j, J k j) := by
    rw [Finset.sum_sub_distrib]; abel
  rw [hs, hd]
  have h3 : ‖∑ k, (L k - ∑ j, J k j)‖ ≤ m * (δ / (2 * (m + 1))) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖L k - ∑ j, J k j‖ ≤ ∑ _k : Fin m, δ / (2 * (m + 1)) := Finset.sum_le_sum fun k _ => (h2 k).le
      _ = m * (δ / (2 * (m + 1))) := by simp
  have h4 : (m : ℝ) * (δ / (2 * (m + 1))) ≤ δ / 2 := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc ‖(I - ∑ k, L k) + ∑ k, (L k - ∑ j, J k j)‖ ≤ ‖I - ∑ k, L k‖ + ‖∑ k, (L k - ∑ j, J k j)‖ := norm_add_le _ _
    _ < δ / 2 + δ / 2 := by linarith
    _ = δ := by ring

end GlobalTheory.CuspTypeApproxUp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaSeventh
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DnCusp
variable {D : D7}


open GlobalTheory.Size in
theorem isCuspFun_of_mem_cusp (N : GlobalTheory.Grid.Node D) (θ : InfFam D) {Φ : N.Maps} (hΦ : Φ ∈ N.Cusp θ) (v : SmT N.M) :
    IsCuspFun N.V (Φ v) := by
  obtain ⟨U, hU, rfl⟩ := Submodule.mem_map.1 hΦ
  clear hΦ
  have h0 : IsCuspFun N.V (0 : GA D N.V → ℂ) := fun r C hC μ 𝓕 hμ h𝓕 g => by simp
  have hU' : ∀ w, IsAutFun N.V (U w) ∧ IsCuspFun N.V (U w) := by
    induction hU using Submodule.span_induction with
    | mem x hx => exact fun w => ⟨(hx.aut w).toIsAutFun, hx.cusp w⟩
    | zero => exact fun w => ⟨GlobalTheory.RowLift.isAutFun_zero _, h0⟩
    | add x y _ _ hx hy => exact fun w => ⟨GlobalTheory.RowLift.isAutFun_add (hx w).1 (hy w).1,
        GlobalTheory.MultMem.isCuspFun_add (hx w).1 (hy w).1 (hx w).2 (hy w).2⟩
    | smul c x _ hx => exact fun w => ⟨GlobalTheory.RowLift.isAutFun_smul (hx w).1 c, GlobalTheory.MultMem.isCuspFun_smul c (hx w).2⟩
  suffices H : IsAutFun N.V ((PiTensorProduct.lift U) v) ∧ IsCuspFun N.V ((PiTensorProduct.lift U) v) from H.2
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f => simpa using ⟨GlobalTheory.RowLift.isAutFun_smul (hU' f).1 r, GlobalTheory.MultMem.isCuspFun_smul r (hU' f).2⟩
  | add x y hx hy => simpa using ⟨GlobalTheory.RowLift.isAutFun_add hx.1 hy.1, GlobalTheory.MultMem.isCuspFun_add hx.1 hy.1 hx.2 hy.2⟩

end GlobalTheory.DnCusp

namespace GlobalTheory.DnCusp

end GlobalTheory.DnCusp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HorizontalThetaLevelFourth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ThetaArrowType


open GlobalTheory.Grid in
theorem sigOK_vert {D : D7} {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (G : GridPre R) (hG : G.Is) :
    ∀ i j, i ≤ D.R.m → j ≤ D.R.m → (G.V i j).V.SigOK
  | 0, 0, _, _ => D.sp.Y_sig 0
  | 0, j + 1, _, _ => by
    show (row0 R (j + 1)).V.SigOK
    by_cases h : j + 1 < D.R.m
    · rw [← nodeY_eq_chainVertexAtRowZero_of_lt R h]; exact D.sp.Y_sig _
    · rw [← nodeX_eq_chainVertexAtRowZero_of_ge R h]; exact D.sp.X'_sig
  | i + 1, j, hi, hj => (hG.spaces.vert i j hi hj).sigOK

theorem goodPar_of_node {D : D7} (N : GlobalTheory.Grid.Node D) (hV : N.V.SigOK) (τ : D.what₂.Tau) :
    GoodPar N.V.rank (N.V.sig (tauE D τ)).1 (N.V.sig (tauE D τ)).2 (N.S τ) := by
  obtain ⟨hp, hq⟩ := GlobalTheory.TypeAtCompare.card_eq_of_congr (N.M.fr_unit τ) (N.M.fr_gram τ) (hV (tauE D τ))
  exact ⟨N.M.lam τ, N.M.ε τ, N.M.enum τ,
    GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (N.M.enum τ).1 (N.M.ds τ), hp, hq⟩

end GlobalTheory.ThetaArrowType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorMatrixCoefficientFormula
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorMatrixCoefficientFormula
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.FockCoeffImage

theorem fockCoefficientC : GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts.HarmonicModule → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → FockCoefficientC R F := by
  intro hHM D G _ _ Pl0 T A Ks _ _ _ R F hPM
  intro i t σ s P cμ cη m ω BW f₀ f c io h μ 𝓧 hμ x hx g hg e e' w w'
  obtain ⟨hne, hth, hcart1, hvac⟩ := GlobalTheory.T.thetaLiftDatum_isNonzeroFockVacuum R F i t σ s P cμ cη m ω BW f₀ f c io h μ 𝓧 hμ
  have hreal := GlobalTheory.T.jointHarmonics_lowest_KType_coefficient_real hHM R F hPM i t σ s P cμ cη m ω BW f₀ f c io h μ 𝓧 hμ g hg e e' w w'
  obtain ⟨hC, -, -, -, -, hW, hON, -, hPt, -, -⟩ := h
  have hinf : IsInfFam R.θ := hC.models.inf
  have hbM : GlobalTheory.AdelicScalar.realElt R.θ (Wc D i) g ∈ GinfC (Wc D i) := by
    refine list_prod_mem fun y hy => ?_
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hy
    exact GlobalTheory.PointAtPlaceHom.atTau_mem _ τ _
  have key := GlobalTheory.T.fockMatrixCoefficient_splits_real_finite_factors D R.ψ R.θ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω hinf hW μ 𝓧 hμ (fun _ => 1) (R.BV i)
    (cart (R.MW i σ)) BW hcart1 (fun τ => GlobalTheory.Chain.VacVec.cart_isCartanInv _ τ) (fun _ => (Vc D i).rank) (pW D i)
    (fun τ => hC.models.BV i τ) hON f hth hvac (fun Q => hPt Q) 1 (one_mem _) _ hbM 1 (one_mem _) x hx
    (io (PiTensorProduct.tprod ℂ e) w) (io (PiTensorProduct.tprod ℂ e') w')
  rw [one_mul] at key
  change _ * l2 μ 𝓧 f f = l2 μ 𝓧 (ω (1, GlobalTheory.AdelicScalar.realElt R.θ (Wc D i) g) (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ e) w)))
    (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ e') w')) * _ at key
  rw [hreal] at key
  refine mul_right_cancel₀ hne (key.trans ?_)
  ring

end GlobalTheory.FockCoeffImage
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorMatrixCoefficientFormulaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVector_matrixCoefficient_formula : GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts.HarmonicModule → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → FockCoefficientC R F := by
  first | exact @GlobalTheory.FockCoeffImage.fockCoefficientC | exact GlobalTheory.FockCoeffImage.fockCoefficientC | (intros; apply GlobalTheory.FockCoeffImage.fockCoefficientC <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdVLeOfLoc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff Pointwise

noncomputable section

namespace GlobalTheory.StairLine

open GlobalTheory.SeeSaw (FI idV dI)

variable {D : D7}


set_option maxHeartbeats 800000 in
theorem line_mem_iff {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FI D) (q : Fin c) (hq : 2 * q.1 + 1 ≠ c)
    {x : D.host.E} (hx : x ≠ 0) (v : GlobalTheory.FinPl.Pl D) (a : AE D) :
    (fun k => a * incA D (x * d.a k q)) ∈ latV B (d.lat Λ 𝔟) (· = v) ↔
      a ∈ idV (FractionalIdeal.spanSingleton _ x⁻¹ * 𝔟 q) v := by
  classical
  set σ : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E) with hσdef
  have hσ : ∀ e, σ (σ e) = e := fun e => star_star e
  have hG : Formalism.UG.cT σ B.gram = B.gram := by funext i j; exact B.herm.eq (B.frame j) (B.frame i)
  have eT : ∀ {m n p : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E) (Y : Matrix (Fin n) (Fin p) D.host.E),
      Formalism.UG.cT σ (X * Y) = Formalism.UG.cT σ Y * Formalism.UG.cT σ X := by
    intros; simp [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have eTT : ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E), Formalism.UG.cT σ (Formalism.UG.cT σ X) = X := by
    intros; ext i j; simp [Formalism.UG.cT, hσ]
  have hperp : Formalism.UG.cT σ d.a * B.gram * frameMat B A d.ι = 0 := by
    have h1 := congrArg (Formalism.UG.cT σ) d.perp
    rw [eT, eT, eTT, hG, ← Matrix.mul_assoc] at h1
    rw [h1]; ext i j; simp [Formalism.UG.cT]
  let P := Formalism.UG.cT σ d.a * B.gram
  let r : Fin B.rank → D.host.E := x⁻¹ • P q.rev
  have hrow : ∀ {n : ℕ} (N : Matrix (Fin B.rank) (Fin n) D.host.E), r ᵥ* N = x⁻¹ • (P * N) q.rev := by
    intros; funext j; simp [r, Matrix.vecMul, dotProduct, Matrix.mul_apply, Finset.mul_sum, mul_assoc]
  have hrM : ∀ y, r ⬝ᵥ (frameMat B A d.ι *ᵥ y) = 0 := by
    intro y
    rw [Matrix.dotProduct_mulVec, hrow, show P * frameMat B A d.ι = 0 from hperp,
      show ((0 : Matrix (Fin c) (Fin A.rank) D.host.E) q.rev) = 0 from rfl, smul_zero, zero_dotProduct]
  have hgram : P * d.a = antiDiagonalSignGramMatrix c ε := d.gram
  have hra : ∀ u : Fin c → D.host.E, r ⬝ᵥ (d.a *ᵥ u) = x⁻¹ * u q := by
    intro u
    rw [Matrix.dotProduct_mulVec, hrow, hgram]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, antiDiagonalSignGramMatrix]
    rw [Finset.sum_eq_single q]
    · have h1 : q.rev.1 + q.1 + 1 = c := by rw [Fin.val_rev]; omega
      have h2 : q.rev ≠ q := by intro h; rw [Fin.ext_iff, Fin.val_rev] at h; omega
      rw [if_pos h1, if_neg h2, mul_one]
    · intro p _ hp
      have : ¬ (q.rev.1 + p.1 + 1 = c) := by
        intro h; apply hp; rw [Fin.ext_iff]; rw [Fin.val_rev] at h; omega
      rw [if_neg this, mul_zero, zero_mul]
    · simp
  have hlat : ∀ y ∈ d.lat Λ 𝔟, r ⬝ᵥ y ∈ FractionalIdeal.spanSingleton _ x⁻¹ * 𝔟 q := by
    rintro _ ⟨y, -, u, hu, rfl⟩
    rw [dotProduct_add, hrM, zero_add, hra]
    exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) (hu q)
  have hcol : r ⬝ᵥ (fun k => x * d.a k q) = 1 := by
    have e : (fun k => x * d.a k q) = d.a *ᵥ Pi.single q x := by
      funext k; simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
    rw [e, hra, Pi.single_eq_same, inv_mul_cancel₀ hx]
  constructor
  · intro hmem
    have hΦ : ∀ Y ∈ latV B (d.lat Λ 𝔟) (· = v), ∑ k, incA D (r k) * Y k ∈
        idV (FractionalIdeal.spanSingleton _ x⁻¹ * 𝔟 q) v := by
      intro Y hY
      induction hY using AddSubgroup.closure_induction with
      | mem Y hY =>
        obtain ⟨α, h1, h2, b, hb, y, hy, rfl⟩ := hY
        rw [Set.mem_singleton_iff] at hb
        subst hb
        refine AddSubgroup.subset_closure ⟨α, h1, h2, _, hlat y hy, ?_⟩
        simp only [GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, one_mul, ← TensorProduct.tmul_sum, dotProduct]
      | zero => simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]; exact zero_mem _
      | add Y Z _ _ hY hZ =>
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]; exact add_mem hY hZ
      | neg Y _ hY =>
        simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]; exact neg_mem hY
    have h := hΦ _ hmem
    have e : ∑ k, incA D (r k) * (a * incA D (x * d.a k q)) = a := by
      calc _ = a * incA D (r ⬝ᵥ (fun k => x * d.a k q)) := by
            set_option synthInstance.maxHeartbeats 100000 in
              simp only [dotProduct, map_sum, map_mul, Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            ring
        _ = a := by rw [hcol, map_one, mul_one]
    rwa [e] at h
  · intro ha
    induction ha using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨α, h1, h2, b, hb, rfl⟩ := hz
      obtain ⟨b', hb', rfl⟩ := (FractionalIdeal.mem_singleton_mul).1 hb
      refine AddSubgroup.subset_closure ⟨α, h1, h2, 1, rfl, d.a *ᵥ Pi.single q b', ?_, ?_⟩
      · refine ⟨0, Λ.zero_mem, Pi.single q b', fun p => ?_, by simp⟩
        by_cases hp : p = q
        · subst hp; simpa using hb'
        · rw [Pi.single_eq_of_ne hp]; exact (𝔟 p).zero_mem
      · funext k
        have e1 : x * d.a k q * (x⁻¹ * b') = 1 * (d.a *ᵥ Pi.single q b') k := by
          simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
            if_true]
          field_simp
        rw [mul_comm (pairA D.host.F 0 α ⊗ₜ[D.host.F] (x⁻¹ * b')), GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, e1]
    | zero =>
      have e0 : (fun k => (0 : AE D) * incA D (x * d.a k q)) = 0 := by funext k; exact zero_mul _
      rw [e0]; exact zero_mem _
    | add y z _ _ hy hz =>
      have : (fun k => (y + z) * incA D (x * d.a k q)) =
          (fun k => y * incA D (x * d.a k q)) + fun k => z * incA D (x * d.a k q) := by
        funext k; simp [add_mul]
      rw [this]; exact add_mem hy hz
    | neg y _ hy =>
      have : (fun k => -y * incA D (x * d.a k q)) = -fun k => y * incA D (x * d.a k q) := by
        funext k; simp [neg_mul]
      rw [this]; exact neg_mem hy

theorem idV_le_of_loc {𝔞 𝔟 : FI D} {v : GlobalTheory.FinPl.Pl D}
    (h : ∀ z ∈ 𝔞, ∃ t : 𝓞 D.host.F, t ∉ v.asIdeal ∧ algebraMap D.host.F D.host.E t * z ∈ 𝔟) : idV 𝔞 v ≤ idV 𝔟 v := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, h1, h2, a, ha, rfl⟩
  obtain ⟨t, ht, htb⟩ := h a ha
  obtain ⟨g1, g2⟩ := GlobalTheory.IdVGen.smul_inv_mem ht h1 h2
  exact AddSubgroup.subset_closure ⟨_, g1, g2, _, htb, GlobalTheory.IdVGen.tmul_eq ht α a⟩

theorem exists_modul {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∉ P.S0) :
    ∃ t : 𝓞 D.host.F, t ∉ v.asIdeal ∧ algebraMap D.host.F D.host.E t ∈
      (((P.modul sc * P.modulBar sc : Ideal (𝓞 D.host.E))) : FI D) := by
  classical
  have hu : ∀ u ∈ P.S0, ∃ t : 𝓞 D.host.F, t ∈ u.asIdeal ∧ t ∉ v.asIdeal := by
    intro u hu
    by_contra hcon
    push_neg at hcon
    have e : u = v := IsDedekindDomain.HeightOneSpectrum.ext
      (u.isMaximal.eq_of_le v.isPrime.ne_top hcon)
    exact hv (e ▸ hu)
  choose! tu htu htv using hu
  let t : 𝓞 D.host.F := ∏ u ∈ P.S0, tu u ^ P.depth sc u
  have htv' : t ∉ v.asIdeal := by
    intro hmem
    obtain ⟨u, hu, hmem'⟩ := (Ideal.IsPrime.prod_mem_iff (hp := v.isPrime)).1 hmem
    exact htv u hu (v.isPrime.mem_of_pow_mem _ hmem')
  have hmod : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ P.modul sc := by
    simp only [t, map_prod, map_pow, Places.modul]
    refine Ideal.prod_mem_prod fun u hu => Ideal.pow_mem_pow ?_ _
    have e := P.under_w hu
    have : tu u ∈ ((P.w u).under (𝓞 D.host.F)).asIdeal := by rw [e]; exact htu u hu
    exact this
  have hfix : D.host.conj • algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t := by
    apply Subtype.ext
    exact (D.host.conjE_mem_hostF_iff _).1 (t : D.host.F).2
  have hbar : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ P.modulBar sc := by
    rw [← hfix]
    exact Ideal.smul_mem_pointwise_smul _ _ _ hmod
  refine ⟨t * t, v.isPrime.mul_notMem htv' htv', ?_⟩
  refine (FractionalIdeal.mem_coeIdeal _).2 ⟨_, Ideal.mul_mem_mul hmod hbar, ?_⟩
  rw [← map_mul]
  rfl

end GlobalTheory.StairLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSetSumApproximation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DnTypeApprox

theorem norm_sub_sum_sum_lt {E : Type*} [SeminormedAddCommGroup E] {m : ℕ} (I : E) (L : Fin m → E) (n : Fin m → ℕ)
    (J : ∀ k, Fin (n k) → E) {δ : ℝ} (hδ : 0 < δ) (h1 : ‖I - ∑ k, L k‖ < δ / 2)
    (h2 : ∀ k, ‖L k - ∑ q, J k q‖ < δ / (2 * (m + 1))) :
    ‖I - ∑ k, ∑ q, J k q‖ < δ := by
  have hd : I - ∑ k, ∑ q, J k q = (I - ∑ k, L k) + ∑ k, (L k - ∑ q, J k q) := by
    rw [Finset.sum_sub_distrib]; abel
  rw [hd]
  have h3 : ‖∑ k, (L k - ∑ q, J k q)‖ ≤ m * (δ / (2 * (m + 1))) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖L k - ∑ q, J k q‖ ≤ ∑ _k : Fin m, δ / (2 * (m + 1)) := Finset.sum_le_sum fun k _ => (h2 k).le
      _ = m * (δ / (2 * (m + 1))) := by simp
  have h4 : (m : ℝ) * (δ / (2 * (m + 1))) ≤ δ / 2 := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc ‖(I - ∑ k, L k) + ∑ k, (L k - ∑ q, J k q)‖ ≤ ‖I - ∑ k, L k‖ + ‖∑ k, (L k - ∑ q, J k q)‖ := norm_add_le _ _
    _ < δ / 2 + δ / 2 := by linarith
    _ = δ := by ring

end GlobalTheory.DnTypeApprox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftVerticalCuspidalGrid
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CuspApproxX

open GlobalTheory.Grow GlobalTheory.Size

theorem thetaKO_le_quotHeight {D : D7} {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {χS χT : (AE D)ˣ →* Circle} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f : WO V W → ℂ}
    (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) {C : Set (GA D V)}
    (hC : IsCompact C) : ∃ (K : ℝ) (a : ℕ), ∀ g ∈ C, ∀ h, ‖thetaKO ω g h f‖ ≤ K * quotHeight W h ^ a := by
  obtain ⟨A, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D V.rank W.rank
  obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 hf
  obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne V W
  obtain ⟨c, hc0, hc⟩ := (H V W rfl rfl).real ψ hθ hU
  obtain ⟨B, hB⟩ := exists_height_le_of_isCompact V hC
  have key := (hc χS χT ω hω μ 𝓕 hμ f hl).2
  set s := (sobO ψ θ μ 𝓕 d f).toReal
  have hs : 0 ≤ s := ENNReal.toReal_nonneg
  refine ⟨c * s * max B 1 ^ A * 2 ^ A, A, fun g hg h => ?_⟩
  have h1 : ∀ h', ‖thetaKO ω g h' f‖ ≤ (c * s * height V g ^ A) * height W h' ^ A := fun h' => by
    rw [mul_assoc _ (height V g ^ A), ← mul_pow]; exact key g h'
  refine (norm_le_quotHeight_pow (GlobalTheory.Chain.LiftConv.thetaKO_left hω hf g) h1 h).trans ?_
  have hg1 : height V g ^ A ≤ max B 1 ^ A :=
    pow_le_pow_left₀ (height_pos V g).le ((hB g hg).trans (le_max_left _ _)) A
  have hq := (pow_pos (quotHeight_pos W h) A).le
  have h2 : (0:ℝ) ≤ 2 ^ A := by positivity
  calc c * s * height V g ^ A * 2 ^ A * quotHeight W h ^ A
      ≤ c * s * max B 1 ^ A * 2 ^ A * quotHeight W h ^ A := by gcongr
    _ = _ := rfl

end GlobalTheory.CuspApproxX

namespace GlobalTheory.CuspApproxX

open GlobalTheory.Grow GlobalTheory.Size

end GlobalTheory.CuspApproxX

namespace GlobalTheory.CuspApproxX

end GlobalTheory.CuspApproxX

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianThetaImagesAlgebraic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ThetaGaussAlg

variable {D : D7}

theorem fockF_one (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) {M X : HSp D} (A : Fr M) (B : Fr X)
    (f : WO M X → ℂ) : fockF ψ θ ε A B f 1 = f := by
  simp only [fockF, pureTensorO, pureTensorL]
  have h1 : (1 : MvPolynomial (FVar D X.rank M.rank) ℂ) = MvPolynomial.basisMonomials (FVar D X.rank M.rank) ℂ 0 := by
    rw [MvPolynomial.coe_basisMonomials]
    rfl
  rw [h1, Module.Basis.constr_basis]
  simp [opPow]

theorem det_gram_ne_zero (V : HSp D) : V.gram.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet

  have hb : ∀ i, V.hT (V.frame i) (∑ j, v j • V.frame j) = 0 := by
    intro i
    have hi : V.hT (V.frame i) (∑ j, v j • V.frame j) = (V.gram *ᵥ v) i := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul, Matrix.mulVec, dotProduct, Formalism.BasicNotions.HSpace.gram]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hi, hv]
    rfl
  have hy : (∑ j, v j • V.frame j) = 0 := by
    refine V.nondeg.2 _ fun x => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← V.frame.sum_repr x, map_sum V.hT, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun i _ => by rw [map_smulₛₗ, LinearMap.smul_apply, hb, smul_zero]
  exact hv0 (funext (Fintype.linearIndependent_iff.mp V.frame.linearIndependent v hy))

theorem incM_gram_inv (S : HSp D) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram⁻¹ = 1 ∧
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram = 1 := by
  have hu : IsUnit S.gram.det := isUnit_iff_ne_zero.mpr (det_gram_ne_zero S)
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  constructor
  · rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]

def crd (S X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) : Matrix (Fin S.rank) (Fin k) (AE D) ≃+ WO S X where
  toFun u := (HMul.hMul (uᵀ.submatrix e.symm id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram) : Matrix (Fin X.rank) (Fin S.rank) (AE D))
  invFun x := GlobalTheory.TripleRead.ptO S.gram e x
  left_inv u := by
    simp only [GlobalTheory.TripleRead.ptO]
    rw [Matrix.mul_assoc, (incM_gram_inv S).1, Matrix.mul_one]
    ext i j
    simp
  right_inv x := by
    have : (GlobalTheory.TripleRead.ptO S.gram e x)ᵀ.submatrix e.symm id =
        (HMul.hMul x (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram⁻¹) : Matrix (Fin X.rank) (Fin S.rank) (AE D)) := by
      ext i j
      simp [GlobalTheory.TripleRead.ptO]
    simp only [this]
    rw [Matrix.mul_assoc, (incM_gram_inv S).2, Matrix.mul_one]
  map_add' u v := by
    rw [← Matrix.add_mul]
    rfl

end GlobalTheory.ThetaGaussAlg

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilDoublingFactor
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.GaussThetaAlg

def transposeMulEquiv {A : Type} [CommRing A] {α β γ : Type} [Fintype β] [DecidableEq β] (e : γ ≃ α)
    (G H : Matrix β β A) (hHG : H * G = 1) : Matrix β γ A ≃+ Matrix α β A where
  toFun u := uᵀ.submatrix e.symm id * G
  invFun x := (x * H)ᵀ.submatrix id e
  left_inv u := by
    show ((uᵀ.submatrix e.symm id * G) * H)ᵀ.submatrix id e = u
    rw [Matrix.mul_assoc, mul_eq_one_comm.1 hHG, Matrix.mul_one]
    ext i j
    simp
  right_inv x := by
    show ((x * H)ᵀ.submatrix id e)ᵀ.submatrix e.symm id * G = x
    have : ((x * H)ᵀ.submatrix id e)ᵀ.submatrix e.symm id = x * H := by
      ext i j
      simp only [submatrix_apply, transpose_apply, id, Equiv.apply_symm_apply]
    rw [this, Matrix.mul_assoc, hHG, Matrix.mul_one]
  map_add' u v := by
    show (u + v)ᵀ.submatrix e.symm id * G = _
    rw [← Matrix.add_mul]
    rfl

theorem mem_algF_of_isFinF {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) {M X : HSp D} (A : Fr M)
    (B : Fr X) (f : WO M X → ℂ) (hf : IsFinF ψ θ ε A B f) : f ∈ algF ψ θ ε A B := by
  refine Submodule.subset_span ⟨f, 1, hf, ?_⟩
  show f = pureTensorL _ f 1
  have h1 : (1 : MvPolynomial (FVar D X.rank M.rank) ℂ) = MvPolynomial.basisMonomials _ ℂ 0 := by
    simp [MvPolynomial.coe_basisMonomials]
  simp only [pureTensorL]
  rw [h1, Module.Basis.constr_basis]
  simp [opPow]

theorem isFinF_thO (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ)
    (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin d ≃ Fin X.rank)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (hBs : Bs.IsGood D.sp.cm.sig) (hψ : Bs.ψ = ψ)
    (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
    (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix e e)
    (hV : Vs.IsHerm D.sp.cm.sig Bs r s) (hW : Ws.IsSkew D.sp.cm.sig Bs r' s')
    (hemb : ∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = conj (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
      Ws.θ w = ((B.cart τ).submatrix e e).map conj)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws) (hM : M.IsGood Bs.ψ)
    (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d))
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin S.rank × Fin d → Fv D.host.F v) → ℂ) (hg : M.IsGauss Bs.ψ Bs.emb g)
    (hφ : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _) (hvac : ∀ᶠ v in Filter.cofinite, φ v = M.vac v) :
    IsFinF ψ θ ε A B (GlobalTheory.TripleRead.thO M ψ (sgn ε S).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) := by
  classical
  have hsg : (sgn ε S).gram = (if ε then -1 else 1 : D.host.E) • S.gram := by
    cases ε <;> ext i j <;> simp [sgn, HSpace.gram]
  have hdet : IsUnit ((if ε then -1 else 1 : D.host.E) • S.gram).det := by
    rw [Matrix.det_smul]
    refine IsUnit.mul (IsUnit.pow _ (by cases ε <;> simp)) ?_
    exact LatVac.gram_det_isUnit S
  have hHG : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)⁻¹ *
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram) = 1 := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet]
    simp
  obtain ⟨f, hf, hD⟩ := GlobalTheory.T.thetaTransform_gaussianVacuum_isFiniteDatum D ψ θ hθ ε S X A B e.symm Bs hBs hψ Vs Ws r s r' s' hJ
    (by rw [hJW]; rfl) hV hW (fun w => by
      obtain ⟨τ, h1, h2, h3⟩ := hemb w
      exact ⟨τ, h1, h2, by rw [h3]; rfl⟩) M hM
    (transposeMulEquiv e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram))
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)⁻¹) hHG)
    (fun u => rfl) g φ hg hφ hvac
  convert hf using 1
  funext x
  show GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho ψ (GlobalTheory.TripleRead.ptO (sgn ε S).gram e x)
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) = f x
  rw [hD.2, hsg]
  congr 1
  show (((x * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)⁻¹)ᵀ.submatrix id e)ᵀ.submatrix e.symm id) *
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram) = x
  have hx : ((x * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)⁻¹)ᵀ.submatrix id e)ᵀ.submatrix e.symm id =
      x * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)⁻¹ := by
    ext i j
    simp
  rw [hx, Matrix.mul_assoc, hHG, Matrix.mul_one]

end GlobalTheory.GaussThetaAlg

end
end
