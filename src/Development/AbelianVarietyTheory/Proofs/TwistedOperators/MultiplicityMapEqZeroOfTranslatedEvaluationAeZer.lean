module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeKernelSchemeGeometricPointsEqKernels
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorLinearInFactorAndHeisenbergDerivReal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityMapEqZeroOfTranslatedEvaluationAeZer
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityMapEqZeroOfTranslatedEvaluationAeZer
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TranslatedEvalInj

section Count

open Formalism.MainNotions.S

theorem gfset_countable (I : AutInst) : I.GFset.Countable := by
  classical
  haveI : Countable I.E := (Module.finBasis ℚ I.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin I.n) (Fin I.n) I.E) :=
    inferInstanceAs (Countable (Fin I.n → Fin I.n → I.E))
  haveI : Countable (GL (Fin I.n) I.E) :=
    Function.Injective.countable (f := (Units.val : GL (Fin I.n) I.E → Matrix (Fin I.n) (Fin I.n) I.E)) fun _ _ h => Units.ext h

  let W : GL (Fin I.n) I.E → Set I.GA := fun γ =>
    {x | (∀ v, uMat (x.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧
      I.fmat x.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))}
  have hsub : I.GFset ⊆ ⋃ γ, W γ := by
    rintro x ⟨γ, -, h1, h2⟩
    exact Set.mem_iUnion.2 ⟨γ, h1, h2⟩
  refine Set.Countable.mono hsub (Set.countable_iUnion fun γ => Set.Subsingleton.countable ?_)
  rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩
  refine Prod.ext (funext fun v => ?_) ?_
  · exact Subtype.ext (Units.ext ((hx1 v).trans (hy1 v).symm))
  · exact Subtype.ext (Units.ext (hx2.trans hy2.symm))

theorem eq_zero_of_ae_fund (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] {fund : Set I.GA}
    (hfund : I.IsFundDom (I.muA μf) fund) {φ : I.GA → ℂ} (hc : Continuous φ)
    (hinv : ∀ γ ∈ I.GFset, ∀ y, φ (γ * y) = φ y) (h0 : φ =ᵐ[(I.muA μf).restrict fund] 0) (y : I.GA) : φ y = 0 := by
  by_contra hy
  obtain ⟨hl, -, -, -, hpos⟩ := GlobalTheory.AdelicUnimod.adelic_unimodular I μf

  have hpre : ∀ γ : I.GA, ∀ A : Set I.GA, I.muA μf A = 0 → I.muA μf ((fun z => γ * z) ⁻¹' A) = 0 := by
    intro γ A hA
    obtain ⟨t, hAt, ht, ht0⟩ := exists_measurable_superset_of_null hA
    refine measure_mono_null (Set.preimage_mono hAt) ?_
    have hf : AEMeasurable (fun z => γ * z) (I.muA μf) :=
      (continuous_const_mul γ).measurable.aemeasurable
    rw [← Measure.map_apply_of_aemeasurable hf ht, hl γ]
    exact ht0
  have hopen : IsOpen {z | φ z ≠ 0} := isOpen_ne_fun hc continuous_const

  have hnull : I.muA μf ({z | φ z ≠ 0} ∩ fund) = 0 := by
    have h1 : ∀ᵐ z ∂(I.muA μf), z ∈ fund → φ z = 0 := (ae_restrict_iff' hfund.1).1 h0
    rw [ae_iff] at h1
    refine measure_mono_null ?_ h1
    intro z hz
    exact fun h => hz.1 (h hz.2)

  have hcov : {z | φ z ≠ 0} ⊆ ⋃ γ ∈ I.GFset, (fun z => γ * z) ⁻¹' ({z | φ z ≠ 0} ∩ fund) := by
    intro z hz
    obtain ⟨γ, hγ, hγz⟩ := hfund.2.1 z
    refine Set.mem_biUnion hγ ⟨?_, hγz⟩
    show φ (γ * z) ≠ 0
    rw [hinv γ hγ z]
    exact hz
  have hall : I.muA μf {z | φ z ≠ 0} = 0 := by
    refine measure_mono_null hcov ((measure_biUnion_null_iff (gfset_countable I)).2 fun γ _ => ?_)
    exact hpre γ _ hnull
  exact (hpos _ hopen ⟨y, hy⟩).ne' hall

theorem castGA_symm_mem {I I' : AutInst} (p : I = I') (γ : I'.GA) (hγ : γ ∈ I'.GFset) :
    (castGA p).symm γ ∈ I.GFset := by
  subst p
  exact hγ

end Count

section Cyclic

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : Formalism.IndefR.Datum.InfFam D} {M : DSModel V S} {J : Set (GA D V)}
  {χ : GA D V → ℂ}

theorem eq_zero_of_value {T : MMap M} (hT : IsMultMap θ M J χ T) (v₀ : M.Vec) (hv₀ : ∀ τ, (v₀ τ : M.H τ) ≠ 0)
    (h0 : T v₀ = 0) : T = 0 := by
  classical

  have step : ∀ (u : M.Vec) (τ : D.what₂.Tau), T u = 0 → (u τ : M.H τ) ≠ 0 →
      ∀ w : M.sm τ, T (Function.update u τ w) = 0 := by
    intro u τ hu hne w
    funext x
    obtain ⟨ℓ, hℓ, hval⟩ := hT.cont τ u x
    have horb : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ℓ (M.rep τ g (u τ)) = 0 := by
      intro g hg
      have hmem : M.rep τ g (u τ) ∈ M.sm τ := GlobalTheory.ConjMult.rep_mem_sm M τ hg (u τ).2
      have h1 := hval ⟨_, hmem⟩
      rw [hT.equiv τ g hg u ⟨_, hmem⟩ rfl, hu] at h1
      simpa [rTr] using h1
    have h2 := GlobalTheory.SmoothCyclic.eq_zero_of_orbit D V S M τ ℓ hℓ (u τ) (u τ).2 hne horb w w.2
    rw [hval w] at h2
    exact h2

  have key : ∀ s : Finset D.what₂.Tau, ∀ w : M.Vec, T (fun τ => if τ ∈ s then w τ else v₀ τ) = 0 := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro w
      simpa using h0
    · intro a s ha ih w
      have hne : ((if a ∈ s then w a else v₀ a : M.sm a) : M.H a) ≠ 0 := by
        simp only [ha, if_false]
        exact hv₀ a
      have h3 := step _ a (ih w) hne (w a)
      convert h3 using 2
      funext τ
      rcases eq_or_ne τ a with rfl | hτ
      · simp
      · simp [hτ]
  apply MultilinearMap.ext
  intro w
  simpa using key Finset.univ w

end Cyclic

end GlobalTheory.TranslatedEvalInj

theorem GlobalTheory.TranslatedEvalInj.eq_zero : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (t : GA D (Yc D 0)) (v₀ : (MP R).Vec), (∀ τ, (v₀ τ : (MP R).H τ) ≠ 0) → ∀ S ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))), ∀ S' : MMap (R.MY 0), S' = postOn (R.MY 0) R.e0 S - S → ((fun x => ev (MP R) v₀ S' (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) =ᵐ[muX X] 0) → S' = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h _ _ hmod t v₀ hv₀ S hS S' hS' hae

  have hsub : ∀ k ∈ (levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) : Set (GA D (Yc D 0))),
      k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) ∧
        levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) k =
          levChi (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) k := by
    intro k hk
    have h1 : Formalism.L2.DIV.rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) k) = 1 := Subgroup.mem_bot.1 hk.2.2
    refine ⟨⟨hk.1, hk.2.1, ?_⟩, ?_⟩
    · change Formalism.L2.DIV.rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) k) ∈ (R.levR F true).H
      rw [h1]
      exact Subgroup.one_mem _
    · rw [GlobalTheory.FlagAction.levChi_flag1]
      have e1 := Formalism.IndefR.Lev.levFn_withP (V := Yc D 0) (β := R.βY 0) (L := R.dat0 R.triv) (R.levR F true)
        (finE (Yc D 0) k)
      have e2 : Formalism.L2.DIV.ext1 (R.levR F true).H (R.levR F true).chi
          (Formalism.L2.DIV.rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) k)) = 1 := by
        rw [h1]
        exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
      calc levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) k
          = ((Formalism.L2.DIV.ext1 (R.levR F true).H (R.levR F true).chi
              (Formalism.L2.DIV.rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) k)) *
              Formalism.L2.DIV.levFn (R.βY 0) (flagL (R.dat0 R.triv)) (finE (Yc D 0) k) : ℂˣ) : ℂ) :=
            congrArg Units.val e1
        _ = ((Formalism.L2.DIV.levFn (R.βY 0) (flagL (R.dat0 R.triv)) (finE (Yc D 0) k) : ℂˣ) : ℂ) := by
            rw [e2, one_mul]
  have hSp : S ∈ Mult R.θ (R.MY 0) (levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) : Set (GA D (Yc D 0)))
      (levChi (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))) :=
    GlobalTheory.ProjectedLift.mult_mono hsub hS
  have hS'm : S' ∈ Mult R.θ (R.MY 0) (levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) : Set (GA D (Yc D 0)))
      (levChi (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))) := by
    rw [hS']
    exact Submodule.sub_mem _
      (GlobalTheory.ProjectedLift.postOn_gaL_mem (β := R.βY 0) (L := R.dat0 R.triv) hmod.inf R.eG
        (RealDat.eC (A := A) D.what₂.embLL) hSp) hSp
  have hT := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hS'm

  have hQ : ∀ γ ∈ X.B.I.GFset, (iotaX X h).symm γ ∈ GQ (D.sp.Y 0) := by
    intro γ hγ
    have h1 := GlobalTheory.TranslatedEvalInj.castGA_symm_mem h.symm γ hγ
    rw [Formalism.IndefR.RationalEmbedding.iota_rat]
    change Formalism.IndefR.RationalEmbedding.iota D ((Formalism.IndefR.RationalEmbedding.iota D).symm ((castGA h.symm).symm γ)) ∈ _
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact h1

  have hfun : ∀ y : X.B.I.GA, S' v₀ ((iotaX X h).symm (y * iotaX X h t)) =
      ev (MP R) v₀ S' (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm y) t) := by
    intro y
    rw [map_mul]
    exact congrArg (fun z : GA D (D.sp.Y 0) => S' v₀ ((iotaX X h).symm y * z)) ((iotaX X h).symm_apply_apply t)
  have hv : ∀ y : X.B.I.GA, S' v₀ ((iotaX X h).symm (y * iotaX X h t)) = 0 := by
    have hc : Continuous fun y : X.B.I.GA => S' v₀ ((iotaX X h).symm (y * iotaX X h t)) :=
      (hT.aut v₀).cont.comp ((iotaX X h).symm.continuous.comp (continuous_mul_const _))
    have hinv : ∀ γ ∈ X.B.I.GFset, ∀ y,
        S' v₀ ((iotaX X h).symm (γ * y * iotaX X h t)) = S' v₀ ((iotaX X h).symm (y * iotaX X h t)) := by
      intro γ hγ y
      rw [mul_assoc, map_mul]
      exact (hT.aut v₀).left _ (hQ γ hγ) _
    have hae' : (fun y : X.B.I.GA => S' v₀ ((iotaX X h).symm (y * iotaX X h t))) =ᵐ[(X.B.I.muA X.B.μf).restrict X.B.fund] 0 := by
      have e : (fun y : X.B.I.GA => S' v₀ ((iotaX X h).symm (y * iotaX X h t))) =
          fun x => ev (MP R) v₀ S' (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t) :=
        funext hfun
      rw [e]
      exact hae
    exact GlobalTheory.TranslatedEvalInj.eq_zero_of_ae_fund X.B.I X.B.μf X.B.fund_spec hc hinv hae'
  have h0 : S' v₀ = 0 := by
    funext g
    have h2 := hv (iotaX X h (g * t⁻¹))
    have e : (iotaX X h).symm (iotaX X h (g * t⁻¹) * iotaX X h t) = g := by
      refine ((congrArg (iotaX X h).symm (map_mul (iotaX X h) (g * t⁻¹) t).symm).trans
        ((iotaX X h).symm_apply_apply _)).trans ?_
      first
        | exact inv_mul_cancel_right g t
        | simp
    rw [e] at h2
    exact h2
  exact GlobalTheory.TranslatedEvalInj.eq_zero_of_value hT v₀ hv₀ h0

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityMapEqZeroOfTranslatedEvaluationAeZerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicityMap_eq_zero_of_translated_evaluation_ae_zero : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (t : GA D (Yc D 0)) (v₀ : (MP R).Vec), (∀ τ, (v₀ τ : (MP R).H τ) ≠ 0) → ∀ S ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))), ∀ S' : MMap (R.MY 0), S' = postOn (R.MY 0) R.e0 S - S → ((fun x => ev (MP R) v₀ S' (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) =ᵐ[muX X] 0) → S' = 0 := by
  first | exact @GlobalTheory.TranslatedEvalInj.eq_zero | exact GlobalTheory.TranslatedEvalInj.eq_zero | (intros; apply GlobalTheory.TranslatedEvalInj.eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridRowZeroVerticesAgreeWeilData
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridRowZeroVerticesAgreeWeilData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

theorem lattice_heq_of_eq_hermitianSpaceWithLattice_mk {D : D7} {x : LSp D} {s : HSp D} {l : Submodule (𝓞 D.host.E) (Fin s.rank → D.host.E)}
    (e : x = ⟨s, l⟩) : HEq l x.lat := by subst e; rfl

theorem nodeAgree_grid0_of_weil_over : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ j, j ≤ D.R.m → NodeAgree (GlobalTheory.Grid.row0 R j) W (.grid 0 j) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc G' W hW j hj
  rcases Nat.lt_or_ge j D.R.m with h | h
  · rw [← nodeY_eq_chainVertexAtRowZero_of_lt R h]
    have e : G'.node (.grid 0 j) = ⟨Yc D j, R.ΛY j⟩ := colY_lt R.toLevCh h
    exact ⟨(congrArg LSp.sp e).symm, lattice_heq_of_eq_hermitianSpaceWithLattice_mk e, (hW.cartY j h).symm, (hW.onbY j h).symm⟩
  · obtain rfl : j = D.R.m := le_antisymm hj h
    rw [← nodeX_eq_chainVertexAtRowZero_top R]
    have e : G'.node (.grid 0 D.R.m) = ⟨D.sp.X', R.ΛX⟩ := colY_m R.toLevCh
    exact ⟨(congrArg LSp.sp e).symm, lattice_heq_of_eq_hermitianSpaceWithLattice_mk e, hW.cartX.symm, hW.onbX.symm⟩

end GlobalTheory.GridJoin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridRowZeroVerticesAgreeWeilDataStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.testGridRowZero_vertices_agree_weilData : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ j, j ≤ D.R.m → NodeAgree (GlobalTheory.Grid.row0 R j) W (.grid 0 j) := by
  first | exact @GlobalTheory.GridJoin.nodeAgree_grid0_of_weil_over | exact GlobalTheory.GridJoin.nodeAgree_grid0_of_weil_over | (intros; apply GlobalTheory.GridJoin.nodeAgree_grid0_of_weil_over <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivHeckeKernelSchemePointsHeckeKernels
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivHeckeKernelSchemePointsHeckeKernels
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

namespace GlobalTheory.HeckeEx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {P : Ideal (𝓞 E)} {p i : ℕ}

theorem exists_carried (Z : KerScheme Xo P p i) {k : Type} [Field k] [IsAlgClosed k] (w : Sp k ⟶ Z.Hk)
    (y : Sp k ⟶ Xo.X) (hw : w ≫ Z.π₁ = y) :
    ∃ C : Subgroup (Over.mk y ⟶ Xo.univ.t.G), Xo.univ.t.HeckeKer (Over.mk y) Dw P p i C ∧
      ∀ C', Z.Carries w y C' ↔ C' = C := by
  subst hw
  obtain ⟨C₀, hC₀, hk⟩ := Z.hecke k w
  obtain ⟨ρ, e₀⟩ := GlobalTheory.HkSetPull.exists_equiv Z.m₁.cart (Over.mk w)
  have hh : ∀ (u : Over.mk w ⟶ Z.o₁.t.G) (v : Over.mk (w ≫ Z.π₁) ⟶ Xo.univ.t.G),
      v.left = u.left ≫ Z.m₁.toSABMap.φ → (u ∈ C₀ ↔ v ∈ Subgroup.comap ρ.symm.toMonoidHom C₀) := fun u v e => by
    rw [show v = ρ u from Over.OverMorphism.ext (e.trans (e₀ u).symm)]
    show _ ↔ ρ.symm (ρ u) ∈ C₀
    rw [ρ.symm_apply_apply]
  refine ⟨Subgroup.comap ρ.symm.toMonoidHom C₀,
    (GlobalTheory.HkSetPull.heckeKer_iff Dw P p i Z.m₁.toSABMap (Over.mk w) C₀ _ hh).1 hk, fun C' => ⟨fun h => ?_, ?_⟩⟩
  · ext v
    obtain ⟨u, rfl⟩ := ρ.surjective v
    exact (h.2 u _ (e₀ u)).symm.trans ((hC₀ u).symm.trans (hh u _ (e₀ u)))
  · rintro rfl
    exact ⟨rfl, fun u v e => (hC₀ u).symm.trans (hh u v e)⟩

theorem exists_equiv_carries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : KerScheme Xo P p i), admitted l P p → ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo.X), ∃ e : {w : Sp k ⟶ Z.Hk // w ≫ Z.π₁ = y} ≃ {C : Subgroup (Over.mk y ⟶ Xo.univ.t.G) // Xo.univ.t.HeckeKer (Over.mk y) Dw P p i C}, ∀ w C, Z.Carries w.1 y C ↔ C = (e w).1 := by
  intro E _ _ _ H Dw l Xo P p i Z hA k _ _ y
  choose c hc hcc using fun w : {w : Sp k ⟶ Z.Hk // w ≫ Z.π₁ = y} => exists_carried Z w.1 y w.2
  refine ⟨Equiv.ofBijective (fun w => ⟨c w, hc w⟩) ⟨fun w w' e => ?_, fun C => ?_⟩, hcc⟩
  · exact Subtype.ext (((GlobalTheory.kerScheme_points E H Dw l Xo P p i Z hA).1 k y (c w) (hc w)).unique
      ((hcc w _).2 rfl) ((hcc w' _).2 (congrArg Subtype.val e)))
  · obtain ⟨z, hz, -⟩ := (GlobalTheory.kerScheme_points E H Dw l Xo P p i Z hA).1 k y C.1 C.2
    exact ⟨⟨z, hz.1⟩, Subtype.ext ((hcc ⟨z, hz.1⟩ _).1 hz).symm⟩

end GlobalTheory.HeckeEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivHeckeKernelSchemePointsHeckeKernelsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_heckeKernelScheme_points_heckeKernels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : KerScheme Xo P p i), admitted l P p → ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo.X), ∃ e : {w : Sp k ⟶ Z.Hk // w ≫ Z.π₁ = y} ≃ {C : Subgroup (Over.mk y ⟶ Xo.univ.t.G) // Xo.univ.t.HeckeKer (Over.mk y) Dw P p i C}, ∀ w C, Z.Carries w.1 y C ↔ C = (e w).1 := by
  first | exact @GlobalTheory.HeckeEx.exists_equiv_carries | exact GlobalTheory.HeckeEx.exists_equiv_carries | (intros; apply GlobalTheory.HeckeEx.exists_equiv_carries <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHarishChandraParamGridVertexRealParameter
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHarishChandraParamGridVertexRealParameter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Grid

open GlobalTheory.SignedHC

theorem parD_entry_int (D : D7) (τ : D.what₂.Tau) (i j : ℕ) {x : ℚ × Bool} (hx : x ∈ (grid D τ).parD i j) :
    ∃ z : ℤ, x.1 = z := by
  obtain ⟨c, hc⟩ := D.R.t_odd
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have hk := D.R.m_add_three_le_k
  have hs : ∃ d : ℕ, sLen D = 2 * d + 1 := ⟨a + b + 2, by unfold sLen Formalism.BasicNotions.Ranks.r; omega⟩
  obtain ⟨d, hd⟩ := hs
  rcases GridData.mem_parD.1 hx with ⟨h1, -⟩ | ⟨l, -, -, rfl⟩ | ⟨l, -, -, h3, -⟩ | ⟨l, -, -, h4, -⟩
  · obtain ⟨i', -, -, h⟩ := GridData.mem_cloud.1 h1
    exact ⟨_, h⟩
  · exact ⟨-(grid D τ).b l, by push_cast; rfl⟩
  · simp only [GridData.blockM, TPar.block, Finset.mem_image, Finset.mem_range] at h3
    obtain ⟨a', -, h⟩ := h3
    refine ⟨-((grid D τ).e l) + c - a', ?_⟩
    rw [← h]
    have ht : ((grid D τ).t : ℚ) = 2 * c + 1 := by exact_mod_cast hc
    rw [ht]; push_cast; ring
  · simp only [GridData.blockC, TPar.block, Finset.mem_image, Finset.mem_range] at h4
    obtain ⟨a', -, h⟩ := h4
    refine ⟨(grid D τ).cen l + d - a', ?_⟩
    rw [← h]
    have ht : ((grid D τ).s : ℚ) = 2 * d + 1 := by exact_mod_cast hd
    rw [ht]; push_cast; ring

theorem even_rkV_iff (D : D7) (i j : ℕ) : Even (rkV D i j) ↔ Odd (i + j) := by
  obtain ⟨c, hc⟩ := D.R.t_odd
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have hk := D.R.m_add_three_le_k
  obtain ⟨u, hu⟩ : ∃ u, a + b = u + 1 := ⟨a + b - 1, by omega⟩
  have hr : D.R.r = 2 * u + 1 := by unfold Formalism.BasicNotions.Ranks.r; omega
  have e : rkV D i j = 2 * (u + j * c + i * (u + 3)) + (1 + j + i) := by
    unfold rkV sLen; rw [hr, hc]; ring
  rw [e, Nat.even_add, Nat.odd_add]
  simp only [even_two, Even.mul_right, true_iff, Nat.even_add, Nat.odd_add]
  simp only [Nat.odd_iff, Nat.even_iff]; omega

theorem isHCParam_parV : ∀ (D : D7), HostHyp D → ∀ (i j : ℕ), 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → ∀ (τ : D.what₂.Tau) (n : ℕ) (lam : Fin n → ℝ) (ε : Fin n → Bool), n = GlobalTheory.Grid.rkV D i j → IsEnum (GlobalTheory.Grid.parV D i j τ) lam ε → Formalism.QuantumDeterminants.IsHCParam lam := by
  intro D _ i j _ _ _ τ n lam ε hn hE
  refine ⟨hE.1, fun a' => ?_⟩
  obtain ⟨-, q, hq, hS⟩ := hE
  have hmem : (q a', ε a') ∈ parV D i j τ := by rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  simp only [parV, dualPar, GlobalTheory.SignedHC.shift, Finset.mem_image, Prod.mk.injEq] at hmem
  obtain ⟨y, ⟨x, hx, rfl⟩, hy1, -⟩ := hmem
  obtain ⟨z, hz⟩ := parD_entry_int D τ i j hx
  have hpar := even_rkV_iff D i j
  rw [hq a', ← hy1]
  by_cases ho : Odd (i + j)
  · obtain ⟨N, hN⟩ := hpar.2 ho
    rw [if_pos ho] at *
    refine ⟨-z + 1 - N, ?_⟩
    have : (n : ℝ) = N + N := by rw [hn, hN]; push_cast; ring
    simp only [hz, this]; push_cast; ring
  · have hne : ¬ Even (rkV D i j) := fun h => ho (hpar.1 h)
    obtain ⟨N, hN⟩ := Nat.not_even_iff_odd.1 hne
    rw [if_neg ho] at *
    refine ⟨-z - N, ?_⟩
    have : (n : ℝ) = 2 * N + 1 := by rw [hn, hN]; push_cast; ring
    simp only [hz, this]; push_cast; ring

end GlobalTheory.Grid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHarishChandraParamGridVertexRealParameterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHarishChandraParam_gridVertexRealParameter : ∀ (D : D7), HostHyp D → ∀ (i j : ℕ), 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → ∀ (τ : D.what₂.Tau) (n : ℕ) (lam : Fin n → ℝ) (ε : Fin n → Bool), n = GlobalTheory.Grid.rkV D i j → IsEnum (GlobalTheory.Grid.parV D i j τ) lam ε → Formalism.QuantumDeterminants.IsHCParam lam := by
  first | exact @GlobalTheory.Grid.isHCParam_parV | exact GlobalTheory.Grid.isHCParam_parV | (intros; apply GlobalTheory.Grid.isHCParam_parV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceEigenvalueIsSqrtNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NatCastMemOfPrimeDvdAbsNorm
namespace GlobalTheory.NatCastMemOfPrimeDvdNorm

open NumberField IsDedekindDomain

theorem natCast_mem_of_prime_dvd_absNorm {K : Type} [Field K] [NumberField K]
    (w : HeightOneSpectrum (RingOfIntegers K)) {q : ℕ} (hq : Nat.Prime q)
    (hd : q ∣ Ideal.absNorm w.asIdeal) : (q : RingOfIntegers K) ∈ w.asIdeal := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI : Finite (RingOfIntegers K ⧸ w.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  have hc : q ∣ Nat.card (RingOfIntegers K ⧸ w.asIdeal) := by
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' q hc
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact hq.one_lt.ne hx
  have h1 : (q : RingOfIntegers K ⧸ w.asIdeal) * x = 0 := by
    rw [← nsmul_eq_mul, ← hx]
    exact addOrderOf_nsmul_eq_zero x
  have h2 : (q : RingOfIntegers K ⧸ w.asIdeal) = 0 := (mul_eq_zero.mp h1).resolve_right hx0
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h2

end GlobalTheory.NatCastMemOfPrimeDvdNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceEigenvalueIsSqrtNorm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FinZeta.SplitNorm

theorem natCast_mem_of_dvd_absNorm {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {q : ℕ}
    (hq : q.Prime) (hd : q ∣ Ideal.absNorm w.asIdeal) : (q : 𝓞 K) ∈ w.asIdeal := by
  first
  | exact @_root_.GlobalTheory.NatCastMemOfPrimeDvdNorm.natCast_mem_of_prime_dvd_absNorm
  | exact _root_.GlobalTheory.NatCastMemOfPrimeDvdNorm.natCast_mem_of_prime_dvd_absNorm
  | (apply _root_.GlobalTheory.NatCastMemOfPrimeDvdNorm.natCast_mem_of_prime_dvd_absNorm <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatCastMemOfPrimeDvdNorm.natCast_mem_of_prime_dvd_absNorm <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatCastMemOfPrimeDvdNorm.natCast_mem_of_prime_dvd_absNorm <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatCastMemOfPrimeDvdNorm.natCast_mem_of_prime_dvd_absNorm ..)

theorem conj_smul_ne_of_isSplit (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w.under (𝓞 D.host.F) = v) (hv : IsSplit (E := D.host.E) v) : D.host.conj • w.asIdeal ≠ w.asIdeal := by
  intro hfix
  set c := GlobalTheory.Member.cF D
  have hcc : ∀ x : D.host.E, c x = D.host.conj x := fun x => Formalism.BasicNotions.bridge_star_holds D.R D.host x
  have hself : GlobalTheory.Mem.Chr.ConjPl c.toRingEquiv w w := by
    rw [GlobalTheory.Mem.Chr.conjPl_iff_mem]
    intro x y hxy
    have hy : y = D.host.conj • x := RingOfIntegers.ext (by rw [hxy]; exact hcc _)
    rw [hy]
    conv_rhs => rw [← hfix]
    exact Ideal.smul_mem_pointwise_smul_iff.symm
  have key : ∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v → u = w := fun u hu =>
    ((GlobalTheory.Mem.Chr.under_eq_iff_conjPl c D.sp.cm.deg2 (GlobalTheory.IdeleNinety.conj_ne_one D) w u).1 (hu.trans hw.symm)).elim id
      fun h => (GlobalTheory.Mem.Chr.existsUnique_conjPl _ w).unique h hself
  obtain ⟨w₁, w₂, hne, h₁, h₂⟩ := GlobalTheory.LFun.isSplit_iff.1 hv
  exact hne ((key w₁ h₁).trans (key w₂ h₂).symm)

theorem lam_qV_pow (D : D7) (lam : ℕ →* ℂ)
    (hlam : ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w.under (𝓞 D.host.F) = v)
    (hv : IsSplit (E := D.host.E) v) (m : ℕ) :
    lam (qV D.host.E w ^ m) = (Real.sqrt ((qV D.host.E w ^ m : ℕ) : ℝ) : ℂ) := by
  apply hlam
  · exact pow_ne_zero _ fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  · intro q hq hi hd
    have hmem := natCast_mem_of_dvd_absNorm w hq (hq.dvd_of_dvd_pow hd)
    refine conj_smul_ne_of_isSplit D v w hw hv (hi w.asIdeal w.isPrime w.ne_bot hmem)

end GlobalTheory.FinZeta.SplitNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceEigenvalueIsSqrtNormStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_eigenvalue_is_sqrt_norm : ∀ (D : D7) (lam : ℕ →* ℂ), (∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → IsSplit (E := D.host.E) v → ∀ m : ℕ, lam (qV D.host.E w ^ m) = (Real.sqrt ((qV D.host.E w ^ m : ℕ) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.FinZeta.SplitNorm.lam_qV_pow | exact GlobalTheory.FinZeta.SplitNorm.lam_qV_pow | (intros; apply GlobalTheory.FinZeta.SplitNorm.lam_qV_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearHeckeIsogenyInverseUpToPSq
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearHeckeIsogenyInverseUpToPSq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem isAbelianScheme_fib {K : Type} [CommRing K] (x : Sp K ⟶ Xo.X) : IsAbelianScheme (Fib Xo x) :=
  have hA := GlobalTheory.HeckePoint.isAbelianScheme_of_proper Xo.univ.t Xo.univ.proper
  { comm := by have := hA.comm; infer_instance
    smooth := by have := hA.smooth; show Smooth (pullback.snd _ _); infer_instance
    proper := by have := hA.proper; show IsProper (pullback.snd _ _); infer_instance
    geomConnected := by have := hA.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }

theorem exists_fibPtsEquiv {K : Type} [Field K] (x : Sp K ⟶ Xo.X) :
    ∃ ρ : (𝟙_ (Over (Sp K)) ⟶ Fib Xo x) ≃* (Over.mk x ⟶ Xo.univ.t.G),
      (∀ u, fibPt _ (ρ u) = u.left) ∧
      ∀ (g : Xo.univ.t.G ⟶ Xo.univ.t.G) u, ρ (u ≫ (Over.pullback x).map g) = ρ u ≫ g := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.HeckePoint.exists_ptsEquiv (isGrpPullback_pullback Xo.univ.t.G x) (𝟙_ (Over (Sp K))) x
    (Category.id_comp _)
  refine ⟨ρ, fun u => ?_, fun g u => Over.OverMorphism.ext ?_⟩
  · apply pullback.hom_ext
    · rw [fibPt, pullback.lift_fst, hρ]
    · rw [fibPt, pullback.lift_snd]
      exact (Over.w u).symm
  · have A : ((Over.pullback x).map g).left ≫ pullback.fst _ x = pullback.fst _ x ≫ g.left :=
      pullback.lift_fst _ _ _
    rw [hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, Category.assoc]
    exact congrArg (u.left ≫ ·) A

theorem exists_hkWith_of_hkRelFr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l P p → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y : FrPt Xo c Ω) (C : hkKer (Xo := Xo) P p i Ω y) (z : FrPt Xo c Ω), hkRelFr P p i (hkTr Xo c p) Ω y C z → ∃ f f', HkWith p y z f f' := by
  intro E _ _ _ H Dw l Xo c P p i ⟨hP, hco, hp, hpP, hpM⟩ Ω _ _ _ y C z ⟨ψ, ψp, h, hLie, hTr⟩
  obtain ⟨⟨hfin, het, hsur⟩, -⟩ := GlobalTheory.HeckePointLaw.isHkIsog_etale_unique Xo hP hco hp hpP hpM C.2 h
  obtain ⟨-, h0, hf, hact, -, hker, -⟩ := h
  have hL : Out.Laws := abelianSchemeLaws_all.1
  have hA := isAbelianScheme_fib y.x
  have hB := isAbelianScheme_fib z.x
  have := hA.proper
  have := hB.proper
  have := hA.comm
  obtain ⟨ρ, e₁, e₂⟩ := exists_fibPtsEquiv y.x
  obtain ⟨σ, s₁, s₂⟩ := exists_fibPtsEquiv z.x
  let f : Fib Xo y.x ⟶ Fib Xo z.x := Over.homMk ψ h0
  have hψ : ∀ u, σ (u ≫ f) = ψp (ρ u) := fun u => GlobalTheory.HeckePoint.fibPt_injective _ (by
    rw [s₁, ← hf, e₁]; rfl)
  have one : ∀ (G : Over (Sp Ω)) [GrpObj G], (1 : 𝟙_ (Over (Sp Ω)) ⟶ G) = η[G] := fun G _ => by
    rw [Hom.one_def]; simp
  have hom : IsMonHom f := hL.rigidity _ _ _ hA hB f (by
    rw [← one, ← one]
    exact σ.injective (by rw [hψ, map_one, map_one, map_one]))
  have lin : Lin f := fun a => GlobalTheory.HeckePoint.hom_ext_pts hA.smooth fun u => σ.injective (by
    rw [← Category.assoc, ← Category.assoc, hψ, s₂, hψ, e₂, hact])
  have hkill : ∀ u : 𝟙_ (Over (Sp Ω)) ⟶ Fib Xo y.x, u ≫ f = 1 → u ^ p ^ 2 = 1 := fun u hu => by
    have hx : ρ u ∈ C.1 := by rw [← hker, MonoidHom.mem_ker, ← hψ, hu, map_one]
    refine ρ.injective ?_
    rw [map_pow, map_one]
    refine (GlobalTheory.HeckeKerModel.mem_tors_span Xo.univ.t _ (p ^ 2)).1 fun a ha => C.2.2.2.1 hx a ?_
    refine (Ideal.span_singleton_le_iff_mem _).2 ?_ ha
    rw [sq, Nat.cast_mul]
    refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
    have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hpP
    rwa [map_natCast] at this
  have hpow : ∀ m : ℕ, IsMonHom (𝟙 (Fib Xo y.x) ^ m) := fun m => by
    induction m with
    | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (toUnit _ ≫ η[Fib Xo y.x]))
    | succ m ih =>
      rw [pow_succ]
      exact inferInstanceAs (IsMonHom (lift (𝟙 (Fib Xo y.x) ^ m) (𝟙 _) ≫ μ[Fib Xo y.x]))
  have := hpow (p ^ 2)
  have : IsFinite f.left := hfin
  have : Etale f.left := het
  have : Surjective f.left := hsur
  obtain ⟨π, hπ⟩ := GlobalTheory.HeckePoint.exists_fac hA.smooth f (𝟙 (Fib Xo y.x) ^ p ^ 2) fun u hu => by
    rw [MonObj.comp_pow, Category.comp_id, hkill u hu]
  have homπ : IsMonHom π := hL.rigidity _ _ _ hB hA π (by
    rw [← IsMonHom.one_hom f, Category.assoc, hπ, IsMonHom.one_hom])
  have : Epi f.left := Flat.epi_of_flat_of_surjective _
  have : Epi f := Over.epi_of_epi_left f
  refine ⟨f, π, ⟨hom, homπ, hπ, ?_, lin, fun a => ?_⟩, hLie, hTr⟩
  · rw [← cancel_epi f, ← Category.assoc, hπ, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  · have := Xo.univ.t.act.hom a
    rw [← cancel_epi f, ← Category.assoc, ← lin a, Category.assoc, hπ, ← Category.assoc, hπ, MonObj.pow_comp,
      MonObj.comp_pow, Category.id_comp, Category.comp_id]

end GlobalTheory.HkIntegral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearHeckeIsogenyInverseUpToPSqStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_heckeIsogeny_inverse_up_to_p_sq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l P p → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y : FrPt Xo c Ω) (C : hkKer (Xo := Xo) P p i Ω y) (z : FrPt Xo c Ω), hkRelFr P p i (hkTr Xo c p) Ω y C z → ∃ f f', HkWith p y z f f' := by
  first | exact @GlobalTheory.HkIntegral.exists_hkWith_of_hkRelFr | exact GlobalTheory.HkIntegral.exists_hkWith_of_hkRelFr | (intros; apply GlobalTheory.HkIntegral.exists_hkWith_of_hkRelFr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneSubIdempotentSmulMemCompletionPrimeMul
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneSubIdempotentSmulMemCompletionPrimeMul
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.ComplOffPlace

open IsDedekindDomain
open scoped TensorProduct

private theorem valued_v_coe_inv_le_one_of_not_mem {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E))
    {x : 𝓞 E} (hx : x ∉ Q.asIdeal) : Valued.v ((((x : E)⁻¹ : E)) : Q.adicCompletion E) ≤ 1 := by
  rw [HeightOneSpectrum.adicCompletion.valued_coe, map_inv₀, RingOfIntegers.coe_eq_algebraMap,
    (HeightOneSpectrum.valuation_eq_one_iff_notMem (v := Q) (K := E)).mpr hx, inv_one]

private theorem adicCompletion_coe_inv_mul_coe {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E))
    {x : E} (hx : x ≠ 0) : ((x⁻¹ : E) : Q.adicCompletion E) * ((x : E) : Q.adicCompletion E) = 1 := by
  rw [← HeightOneSpectrum.adicCompletion.coe_mul, inv_mul_cancel₀ hx, HeightOneSpectrum.adicCompletion.coe_one]

theorem exists_comb {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    (f : FiniteAdeleRing (𝓞 E) E) (h1 : f P = 1) (h0 : ∀ Q, Q ≠ P → f Q = 0) :
    ∃ x ∈ P.asIdeal, ∃ y ∈ P.asIdeal, ∃ b c : FiniteAdeleRing (𝓞 E) E, (∀ Q, Valued.v (b Q) ≤ 1) ∧
      (∀ Q, Valued.v (c Q) ≤ 1) ∧
      1 - f = b * algebraMap E _ (x : E) + c * algebraMap E _ (y : E) := by
  classical
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot

  have hfin : {Q : HeightOneSpectrum (𝓞 E) | Q.asIdeal ∣ Ideal.span {x}}.Finite :=
    Ideal.finite_factors (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])

  have hcov : ¬ ((P.asIdeal : Set (𝓞 E)) ⊆
      ⋃ Q ∈ ((hfin.toFinset.erase P : Finset (HeightOneSpectrum (𝓞 E))) : Set (HeightOneSpectrum (𝓞 E))),
        ((fun Q : HeightOneSpectrum (𝓞 E) => Q.asIdeal) Q : Set (𝓞 E))) := by
    rw [Ideal.subset_union_prime (f := fun Q : HeightOneSpectrum (𝓞 E) => Q.asIdeal) P P
      (fun Q _ _ _ => Q.isPrime)]
    rintro ⟨Q, hQS, hle⟩
    exact (Finset.mem_erase.mp hQS).1
      (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top hle).symm)
  obtain ⟨y, hyP, hyS⟩ := Set.not_subset.mp hcov
  have hy : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → x ∈ Q.asIdeal → y ∉ Q.asIdeal := by
    intro Q hQ hxQ hyQ
    apply hyS
    refine Set.mem_biUnion (x := Q) ?_ hyQ
    rw [Finset.coe_erase, Set.mem_diff, Set.Finite.coe_toFinset]
    exact ⟨Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hxQ), hQ⟩

  let bf : ∀ Q : HeightOneSpectrum (𝓞 E), Q.adicCompletion E := fun Q =>
    if Q = P then 0 else if x ∈ Q.asIdeal then 0 else (((x : E)⁻¹ : E) : Q.adicCompletion E)
  let cf : ∀ Q : HeightOneSpectrum (𝓞 E), Q.adicCompletion E := fun Q =>
    if Q = P then 0 else if x ∈ Q.asIdeal then (((y : E)⁻¹ : E) : Q.adicCompletion E) else 0
  have hbf : ∀ Q, Valued.v (bf Q) ≤ 1 := by
    intro Q
    show Valued.v (if Q = P then 0 else if x ∈ Q.asIdeal then 0 else (((x : E)⁻¹ : E) : Q.adicCompletion E)) ≤ 1
    split_ifs with h1 h2
    · simp
    · simp
    · exact valued_v_coe_inv_le_one_of_not_mem Q h2
  have hcf : ∀ Q, Valued.v (cf Q) ≤ 1 := by
    intro Q
    show Valued.v (if Q = P then 0 else if x ∈ Q.asIdeal then (((y : E)⁻¹ : E) : Q.adicCompletion E) else 0) ≤ 1
    split_ifs with h1 h2
    · simp
    · exact valued_v_coe_inv_le_one_of_not_mem Q (hy Q h1 h2)
    · simp
  let b : FiniteAdeleRing (𝓞 E) E := Subtype.mk bf (Filter.Eventually.of_forall hbf)
  let c : FiniteAdeleRing (𝓞 E) E := Subtype.mk cf (Filter.Eventually.of_forall hcf)
  refine ⟨x, hxP, y, hyP, b, c, hbf, hcf, ?_⟩
  ext1 Q
  show (1 : Q.adicCompletion E) - f Q = bf Q * ((x : E) : Q.adicCompletion E) + cf Q * ((y : E) : Q.adicCompletion E)
  by_cases hQ : Q = P
  · subst hQ
    simp [bf, cf, h1]
  · have hxQ' : ∀ hxQ : x ∉ Q.asIdeal, (x : E) ≠ 0 := fun hxQ h =>
      hxQ (by rw [show x = 0 from by exact_mod_cast h]; exact Q.asIdeal.zero_mem)
    by_cases hxQ : x ∈ Q.asIdeal
    · have hyQ := hy Q hQ hxQ
      have hy0 : (y : E) ≠ 0 := fun h =>
        hyQ (by rw [show y = 0 from by exact_mod_cast h]; exact Q.asIdeal.zero_mem)
      simp only [bf, cf, if_neg hQ, if_pos hxQ, h0 Q hQ, sub_zero, zero_mul, zero_add]
      exact (adicCompletion_coe_inv_mul_coe Q hy0).symm
    · simp only [bf, cf, if_neg hQ, if_neg hxQ, h0 Q hQ, sub_zero, zero_mul, add_zero]
      exact (adicCompletion_coe_inv_mul_coe Q (hxQ' hxQ)).symm

theorem mul_smul_mem_hat (D : D7) {n : ℕ} (I : Ideal (𝓞 D.host.E)) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    {a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (ha : a ∈ intAE D) {t : 𝓞 D.host.E} (ht : t ∈ I)
    {y : Fin n → GlobalTheory.AdLat.RA D.host.F D.host.E} (hy : y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E))) :
    (a * (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (t : D.host.E)) • y ∈
      GlobalTheory.AdLat.hat D.host.F ((I • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) := by
  unfold intAE at ha
  unfold GlobalTheory.AdLat.hat at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, x, hx, rfl⟩ := hz
    induction ha using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨c, hc, s, rfl⟩ := hw
      refine AddSubgroup.subset_closure ⟨c * b, fun v => mul_mem (hc v) (hb v),
        (s * t) • x, Submodule.smul_mem_smul (I.mul_mem_left s ht) hx, ?_⟩
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.smul_def,
        map_mul, ← RingOfIntegers.coe_eq_algebraMap]
    | zero => simp
    | add u w _ _ hu hw =>
      rw [add_mul, add_smul]
      exact AddSubgroup.add_mem _ hu hw
    | neg u _ hu =>
      rw [neg_mul, neg_smul]
      exact AddSubgroup.neg_mem _ hu
  | zero =>
    rw [smul_zero]
    exact AddSubgroup.zero_mem _
  | add u w _ _ hu hw =>
    rw [smul_add]
    exact AddSubgroup.add_mem _ hu hw
  | neg u _ hu =>
    rw [smul_neg]
    exact AddSubgroup.neg_mem _ hu

theorem one_sub_smul_mem : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (n : ℕ) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)),
    Formalism.L2.NTheta.IsIdemAt e P → ∀ y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)),
      (1 - finPart D e) • y ∈ GlobalTheory.AdLat.hat D.host.F ((P.asIdeal • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) := by
  intro D P e n L he y hy
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨-, h1, h0⟩ := GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ he
  obtain ⟨x, hx, x', hx', b, c, hb, hc, hbc⟩ := exists_comb P (Φ e) h1 h0
  obtain ⟨zb, -, hzb⟩ := hΦ.surj b
  obtain ⟨zc, -, hzc⟩ := hΦ.surj c
  have hzbi : finPart D zb ∈ intAE D := (hΦ.int zb).mpr fun Q => by rw [hzb]; exact hb Q
  have hzci : finPart D zc ∈ intAE D := (hΦ.int zc).mpr fun Q => by rw [hzc]; exact hc Q

  set s : AE D := (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 1) ⊗ₜ[D.host.F] (1 : D.host.E) with hs
  have hsi : infPart D s = 0 := by
    rw [hs]
    show Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA D.host.F) (AlgHom.id D.host.F D.host.E)
      ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 1) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    rw [Algebra.TensorProduct.map_tmul]
    exact TensorProduct.zero_tmul _ _
  have hsf : finPart D s = 1 := by
    rw [hs]
    show Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)
      ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 1) ⊗ₜ[D.host.F] (1 : D.host.E)) = 1
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    exact Algebra.TensorProduct.one_def.symm
  have hinc : ∀ z : D.host.E, finPart D (incA D z) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] z := by
    intro z
    show Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)
      ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ⊗ₜ[D.host.F] z) = _
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  have key : (1 - e) * s = (zb * incA D (x : D.host.E) + zc * incA D (x' : D.host.E)) * s := by
    apply hΦ.ext'
    · simp only [map_mul, hsi, mul_zero]
    · intro Q
      have hΦe : Φ ((1 - e) * s) = Φ ((zb * incA D (x : D.host.E) + zc * incA D (x' : D.host.E)) * s) := by
        simp only [map_mul, map_sub, map_one, map_add (f := _), hΦ.inc, hzb, hzc, hbc]
      rw [hΦe]
  have key' : 1 - finPart D e =
      finPart D zb * ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (x : D.host.E)) +
        finPart D zc * ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (x' : D.host.E)) := by
    have h := congrArg (finPart D) key
    simpa only [map_mul, map_sub, map_one, map_add (f := _), hsf, mul_one, hinc] using h
  rw [key', add_smul]
  exact AddSubgroup.add_mem _ (mul_smul_mem_hat D P.asIdeal L hzbi hx hy)
    (mul_smul_mem_hat D P.asIdeal L hzci hx' hy)

end GlobalTheory.ComplOffPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneSubIdempotentSmulMemCompletionPrimeMulStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_sub_idempotent_smul_mem_completion_prime_mul : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (n : ℕ) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)),
    Formalism.L2.NTheta.IsIdemAt e P → ∀ y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)),
      (1 - finPart D e) • y ∈ GlobalTheory.AdLat.hat D.host.F ((P.asIdeal • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) := by
  first | exact @GlobalTheory.ComplOffPlace.one_sub_smul_mem | exact GlobalTheory.ComplOffPlace.one_sub_smul_mem | (intros; apply GlobalTheory.ComplOffPlace.one_sub_smul_mem <;> assumption)
end
end
end
