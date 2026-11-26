module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeometricLemmaCellOneBlockSwapEquiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HtCard
public import Development.AutomorphicArithmetic.BlochKatoExtensions.PhtCmp
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamOfLadicRepSumRepAwayFromLHost
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLDirectSumPotSemistable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSstAtOfIsCrysAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardLeUnramifiedTwistsCuspidalSupportJacquet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicHodgePropertiesConjInvariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeSpacesOrthogonalOfClassSumInner

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugation
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugation
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PstConj

open TensorProduct Module GlobalTheory.Pst.EnlargeCoeff

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V V' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
  {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL ↥(GK K) V'}

theorem tensQ_tensQ (f : V →ₗ[ℚ_[l]] V') (g : V' →ₗ[ℚ_[l]] V) (hgf : ∀ v, g (f v) = v)
    (x : V ⊗[ℚ_[l]] Bst P) : tensQ P g (tensQ P f x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [hgf]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

def dpstUrCongr (e : V ≃ₗ[LL] V') (he : ∀ g x, e (ρ g x) = ρ' g (e x)) :
    DpstUr P ρ ≃ₗ[↥(MaximalUnramifiedExtension l)] DpstUr P ρ' :=
  let f : V →ₗ[ℚ_[l]] V' := (e : V →ₗ[LL] V').restrictScalars ℚ_[l]
  let g : V' →ₗ[ℚ_[l]] V := (e.symm : V' →ₗ[LL] V).restrictScalars ℚ_[l]
  have hf : ∀ s v, f (ρ s v) = ρ' s (f v) := he
  have hg : ∀ s v, g (ρ' s v) = ρ s (g v) := fun s v => by
    apply e.injective
    change e (e.symm (ρ' s v)) = e (ρ s (e.symm v))
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  { toFun := fun x => toUr P ρ' (dQ P hf ((toUr P ρ).symm x))
    invFun := fun x => toUr P ρ (dQ P hg ((toUr P ρ').symm x))
    map_add' := fun x y => by simp only [map_add (f := _)]
    map_smul' := fun c x => dQ_mulD P hf c _
    left_inv := fun x => Subtype.ext (tensQ_tensQ P f g (fun v => e.symm_apply_apply v) x.1)
    right_inv := fun x => Subtype.ext (tensQ_tensQ P g f (fun v => e.apply_symm_apply v) x.1) }

theorem isPst_congr (e : V ≃ₗ[LL] V') (he : ∀ g x, e (ρ g x) = ρ' g (e x)) (hV : IsPst P ρ) : IsPst P ρ' := by
  rw [IsPst, ← (dpstUrCongr P e he).rank_eq, hV]
  exact (e.restrictScalars ℚ_[l]).rank_eq

theorem main : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : GlobalTheory.Pst.Induces Bw) (r r' : ↥(Dec (F := E) A) →* GL (Fin a) (Qbar l)) (p : GL (Fin a) (Qbar l)), (∀ g, r' g = p * r g * p⁻¹) → IsPstAt P Bw r → IsPstAt P Bw r' ∧ wdAt P ι Bw h hj r' = wdAt P ι Bw h hj r := by
  intro E Ω _ _ _ _ _ l _ ι a P AI _ w A h O _ _ _ Bw hj r r' p hc hr
  have hr' : IsPstAt P Bw r' := by
    obtain ⟨L₁, r₁, h₁, hp⟩ := hr
    obtain ⟨L₂, hL, r₂, hm, e, he⟩ := GlobalTheory.ConjLocal.exists_conj_model p hc h₁
    exact ⟨L₂, r₂, hm, GlobalTheory.PstConj.isPst_congr P e he (GlobalTheory.PstExt.isPst_enlarge P Bw hL r₁ hp)⟩
  exact ⟨hr', GlobalTheory.ConjGal.wdAt_conj P ι Bw h hj r r' p hc hr hr'⟩

end GlobalTheory.PstConj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugationStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaineParameter_invariant_under_conjugation : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : GlobalTheory.Pst.Induces Bw) (r r' : ↥(Dec (F := E) A) →* GL (Fin a) (Qbar l)) (p : GL (Fin a) (Qbar l)), (∀ g, r' g = p * r g * p⁻¹) → IsPstAt P Bw r → IsPstAt P Bw r' ∧ wdAt P ι Bw h hj r' = wdAt P ι Bw h hj r := by
  first | exact @GlobalTheory.PstConj.main | exact GlobalTheory.PstConj.main | (intros; apply GlobalTheory.PstConj.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TieAutAndSplit
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AutomorphismSplitting

theorem isCSD_inv' {R : Ranks} {H : Host R} {χ : HChar H.E} (h : IsCSD H χ) : IsCSD H χ⁻¹ :=
  ⟨fun w w' hw k => congrArg (·⁻¹) (h.1 w w' hw k), fun k => congrArg (·⁻¹) (h.2 k)⟩

theorem hasInf_inv {L : Type} [Field L] [NumberField L] {I : Type} [Fintype I] {φ : I → L →+* ℂ} {χ : HChar L}
    (h : χ.HasInf φ (fun _ => 1)) : (χ⁻¹).HasInf φ (fun _ => -1) := by
  intro k
  have hk := h k
  show (((χ.inf k)⁻¹ : ℂˣ) : ℂ) = _
  rw [Units.val_inv_eq_inv_val, hk, ← Finset.prod_inv_distrib]
  simp

end GlobalTheory.AutomorphismSplitting
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCount
noncomputable section

namespace GlobalTheory.HtCardProof

open _root_.Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N _root_.Formalism.L2 Module

section Local

variable {l m : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {K LL : FinExt l}
  (r : ↥(GK K) →* GL (Fin m) ↥LL.1)


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
include T in
theorem exists_count (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) [FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) (vrep r) τ)] :
    ∃ M : Multiset ℤ, Multiset.card M = finrank ↥LL.1 ↥(DdRE (P.PD K) (vrep r) τ) ∧
      ∀ a, (M.count a : ℤ) = multV (P.PD K) (vrep r) τ a := by
  obtain ⟨lo, hlo⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_lo (P.PD K) (vrep r) τ
  obtain ⟨hi, hhi⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_hi (P.PD K) (vrep r) τ
  have anti := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_anti (P.PD K) (vrep r) τ
  haveI : ∀ a, FiniteDimensional ↥LL.1 ↥(FildR (P.PD K) (vrep r) τ a) := fun a =>
    Submodule.finiteDimensional_of_le (inf_le_left : FildR (P.PD K) (vrep r) τ a ≤ DdRE (P.PD K) (vrep r) τ)
  have nn : ∀ a, 0 ≤ multV (P.PD K) (vrep r) τ a := fun a => by
    have := Submodule.finrank_mono (anti (show a ≤ a + 1 by omega))
    unfold multV
    omega
  obtain ⟨lo₁, hl1, hl2⟩ : ∃ lo₁, lo₁ ≤ lo ∧ lo₁ ≤ hi := ⟨min lo hi, min_le_left _ _, min_le_right _ _⟩
  have zero : ∀ a, a ∉ Finset.Ico lo₁ hi → multV (P.PD K) (vrep r) τ a = 0 := fun a ha => by
    rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at ha
    have e : FildR (P.PD K) (vrep r) τ a = FildR (P.PD K) (vrep r) τ (a + 1) := by
      rcases ha with ha | ha
      · exact (hlo a (by omega)).trans (hlo (a + 1) (by omega)).symm
      · exact (hhi a ha).trans (hhi (a + 1) (by omega)).symm
    unfold multV
    rw [e, sub_self]
  refine ⟨∑ a ∈ Finset.Ico lo₁ hi, Multiset.replicate (multV (P.PD K) (vrep r) τ a).toNat a, ?_, fun b => ?_⟩
  · rw [Multiset.card_sum]
    simp only [Multiset.card_replicate]
    have hs : ∑ a ∈ Finset.Ico lo₁ hi, multV (P.PD K) (vrep r) τ a =
        (finrank ↥LL.1 ↥(FildR (P.PD K) (vrep r) τ lo₁) : ℤ) - finrank ↥LL.1 ↥(FildR (P.PD K) (vrep r) τ hi) :=
      Formalism.MainNotions.N.Pv.LocalLengthBound.rk_sum_multV _ _ _ _ _ hl2
    have e1 : finrank ↥LL.1 ↥(FildR (P.PD K) (vrep r) τ lo₁) = finrank ↥LL.1 ↥(DdRE (P.PD K) (vrep r) τ) := by
      rw [hlo lo₁ hl1]
    have e2 : finrank ↥LL.1 ↥(FildR (P.PD K) (vrep r) τ hi) = 0 := Submodule.finrank_eq_zero.2 (hhi hi le_rfl)
    rw [e1, e2] at hs
    have : ((∑ a ∈ Finset.Ico lo₁ hi, (multV (P.PD K) (vrep r) τ a).toNat : ℕ) : ℤ) =
        (finrank ↥LL.1 ↥(DdRE (P.PD K) (vrep r) τ) : ℤ) := by
      push_cast
      rw [Finset.sum_congr rfl fun a _ => Int.toNat_of_nonneg (nn a), hs]
      simp
    exact_mod_cast this
  · rw [Multiset.count_sum']
    simp only [Multiset.count_replicate]
    rw [Finset.sum_ite_eq']
    by_cases hb : b ∈ Finset.Ico lo₁ hi
    · rw [if_pos hb, Int.toNat_of_nonneg (nn b)]
    · rw [if_neg hb, zero b hb]
      rfl

end Local

theorem htCard : GlobalTheory.HeightCounting.HtCard := GlobalTheory.PhtCompare.phtCmp

end GlobalTheory.HtCardProof

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceParahoricSubgroupCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceParahoricSubgroupCharacter
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ParaLevel

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem trivOutside_one (T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) :
    TrivOutside T (1 : GAf L n) := by
  intro w _
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem detDD_one (s : SplitPlace L) (r : ℕ) :
    NG.detDD s r (1 : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) = 1 := by
  unfold NG.detDD
  have : (Matrix.of fun a b : {x : Fin n // r ≤ x.val} =>
      ((1 : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a.1 b.1) = 1 := by
    ext a b
    simp [Matrix.one_apply, Subtype.ext_iff]
  rw [this, Matrix.det_one]

theorem continuous_detDD (s : SplitPlace L) (r : ℕ) :
    Continuous (NG.detDD (n := n) s r) := by
  unfold NG.detDD
  refine Continuous.matrix_det ?_
  refine continuous_pi fun a => continuous_pi fun b => ?_
  exact (Units.continuous_val (M := Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))).matrix_elem a.1 b.1

section main
variable (s : SplitPlace L) (r : ℕ) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ)
  (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ)

def paraSub (hP : NG.LevelPara J χ s r ξ) :
    Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) where
  carrier := {g | NG.ParaRT s r g}
  one_mem' := by
    have h := (hP.mem 1 (trivOutside_one _)).1 J.one_mem
    change NG.ParaRT s r 1
    rw [map_one] at h
    exact h
  mul_mem' := by
    intro g h hg hh
    obtain ⟨x, hx, rfl⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g
    obtain ⟨y, hy, rfl⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s h
    have hxy := GlobalTheory.SatInd.CosetFin.trivOutside_mul hx hy
    rw [← map_mul]
    exact (hP.mem _ hxy).1 (J.mul_mem ((hP.mem x hx).2 hg) ((hP.mem y hy).2 hh))
  inv_mem' := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g
    have hi := GlobalTheory.SatInd.CosetFin.trivOutside_inv hx
    show NG.ParaRT s r (s.loc n x)⁻¹
    rw [← map_inv]
    exact (hP.mem _ hi).1 (J.inv_mem ((hP.mem x hx).2 hg))

end main
end GlobalTheory.ParaLevel

namespace GlobalTheory.ParaLevel
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
section main2
variable {s : SplitPlace L} {r : ℕ} {J : Subgroup (GAf L n)} {χ : J →* ℂˣ}
  {ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ}

def lift (s : SplitPlace L) (g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : GAf L n :=
  (GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g).choose

theorem lift_triv (g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
    TrivOutside {s.v} (lift s g) :=
  (GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g).choose_spec.1

theorem loc_lift (g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
    s.loc n (lift s g) = g :=
  (GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g).choose_spec.2

theorem lift_mem (hP : NG.LevelPara J χ s r ξ) (g : paraSub s r J χ ξ hP) : lift s g.1 ∈ J :=
  (hP.mem _ (lift_triv g.1)).2 (by rw [loc_lift]; exact g.2)

def thetaFun (hP : NG.LevelPara J χ s r ξ) (g : paraSub s r J χ ξ hP) : ℂˣ :=
  χ ⟨lift s g.1, lift_mem hP g⟩

theorem chi_eq (hP : NG.LevelPara J χ s r ξ) (κ : GAf L n) (hκ : TrivOutside {s.v} κ) (hJ : κ ∈ J)
    (h : s.loc n κ ∈ paraSub s r J χ ξ hP) : χ ⟨κ, hJ⟩ = thetaFun hP ⟨s.loc n κ, h⟩ := by
  unfold thetaFun
  set κ₀ := lift s (s.loc n κ) with hκ₀
  have h0 : κ₀ ∈ J := lift_mem hP ⟨s.loc n κ, h⟩
  have ht : TrivOutside {s.v} (κ * κ₀⁻¹) :=
    GlobalTheory.SatInd.CosetFin.trivOutside_mul hκ (GlobalTheory.SatInd.CosetFin.trivOutside_inv (lift_triv _))
  have hl : s.loc n (κ * κ₀⁻¹) = 1 := by
    rw [map_mul, map_inv, hκ₀, loc_lift, mul_inv_cancel]
  have hδ : κ * κ₀⁻¹ ∈ J := J.mul_mem hJ (J.inv_mem h0)
  have hc : χ ⟨κ * κ₀⁻¹, hδ⟩ = 1 := by
    rw [hP.chr _ hδ ht 1 (by rw [hl, detDD_one]; rfl), map_one]
  have hprod : (⟨κ, hJ⟩ : J) = ⟨κ * κ₀⁻¹, hδ⟩ * ⟨κ₀, h0⟩ := by
    apply Subtype.ext; simp
  rw [hprod, map_mul, hc, one_mul]

def theta (hP : NG.LevelPara J χ s r ξ) : paraSub s r J χ ξ hP →* ℂˣ where
  toFun := thetaFun hP
  map_one' := by
    have h1 : s.loc n (1 : GAf L n) ∈ paraSub s r J χ ξ hP := by rw [map_one]; exact (paraSub s r J χ ξ hP).one_mem
    have := chi_eq hP 1 (trivOutside_one _) J.one_mem h1
    have e : (⟨s.loc n 1, h1⟩ : paraSub s r J χ ξ hP) = 1 := by apply Subtype.ext; simp
    rw [e] at this
    rw [← this]
    exact map_one χ
  map_mul' := by
    intro g h
    set x := lift s g.1
    set y := lift s h.1
    have hx := lift_mem hP g
    have hy := lift_mem hP h
    have hxy : TrivOutside {s.v} (x * y) :=
      GlobalTheory.SatInd.CosetFin.trivOutside_mul (lift_triv _) (lift_triv _)
    have hm : s.loc n (x * y) ∈ paraSub s r J χ ξ hP := by
      rw [map_mul, loc_lift, loc_lift]; exact (g * h).2
    have := chi_eq hP (x * y) hxy (J.mul_mem hx hy) hm
    have e : (⟨s.loc n (x * y), hm⟩ : paraSub s r J χ ξ hP) = g * h := by
      apply Subtype.ext; simp [x, y, loc_lift]
    rw [e] at this
    rw [← this]
    have e2 : (⟨x * y, J.mul_mem hx hy⟩ : J) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [e2, map_mul]
    rfl

end main2
end GlobalTheory.ParaLevel

namespace GlobalTheory.ParaLevel

theorem exists_parahoric_char : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (r : ℕ) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.LevelPara J χ s r ξ → (∃ N : ℕ, ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) → ∃ (K : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) (θ : K →* ℂˣ), (∀ g, g ∈ K ↔ NG.ParaRT s r g) ∧ (∀ g (h : g ∈ K) (d : (s.v.adicCompletion (maximalRealSubfield L))ˣ), (d : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r g → θ ⟨g, h⟩ = ξ d) ∧ (∀ g ∈ K, g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) ∧ IsOpen (θ.ker : Set K) ∧ ∀ κ, TrivOutside {s.v} κ → ∀ (hJ : κ ∈ J) (h : s.loc n κ ∈ K), χ ⟨κ, hJ⟩ = θ ⟨s.loc n κ, h⟩ := by
  intro L _ _ _ n s r J χ ξ hP hξ
  obtain ⟨N, hN⟩ := hξ
  refine ⟨paraSub s r J χ ξ hP, theta hP, fun g => Iff.rfl, ?_, fun g hg => hg.1, ?_, ?_⟩
  · intro g h d hd
    show χ ⟨lift s g, lift_mem hP ⟨g, h⟩⟩ = ξ d
    exact hP.chr _ _ (lift_triv g) d (by rw [loc_lift]; exact hd)
  · apply Subgroup.isOpen_of_mem_nhds
    have hc : Continuous fun g : paraSub s r J χ ξ hP => NG.detDD s r g.1 :=
      (continuous_detDD s r).comp continuous_subtype_val
    have h1 : NG.detDD s r ((1 : paraSub s r J χ ξ hP) : GL (Fin n) _) = 1 := detDD_one s r
    obtain ⟨π, hπ⟩ := s.v.valuation_exists_uniformizer (maximalRealSubfield L)
    set a : s.v.adicCompletion (maximalRealSubfield L) := ((π : maximalRealSubfield L) : s.v.adicCompletion (maximalRealSubfield L)) ^ N
    have ha : Valued.v a = WithZero.exp (-(N : ℤ)) := by
      simp only [a, map_pow, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ, ← WithZero.exp_nsmul]
      congr 1; simp
    have ha0 : (Valued.v a) ≠ 0 := by rw [ha]; simp
    have hnhds : {x : s.v.adicCompletion (maximalRealSubfield L) |
        Valued.v (x - 1) < WithZero.exp (-(N : ℤ))} ∈ nhds (1 : s.v.adicCompletion (maximalRealSubfield L)) := by
      refine Valued.mem_nhds.2 ⟨Units.mk0 (Valued.v.restrict a) (by rwa [ne_eq, Valuation.restrict_eq_zero_iff]), ?_⟩
      intro y hy
      simp only [Set.mem_setOf_eq, Units.val_mk0] at hy ⊢
      rw [← ha]
      exact (Valuation.restrict_lt_iff _).1 hy
    have hpre := hc.tendsto 1 (by rw [h1]; exact hnhds)
    refine Filter.mem_of_superset hpre ?_
    intro g hg
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hg
    have hne : NG.detDD s r g.1 ≠ 0 := by
      intro h0
      rw [h0, zero_sub, Valuation.map_neg, Valuation.map_one] at hg
      exact absurd hg (not_lt.2 (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega))
    have hθ : theta hP g = ξ (Units.mk0 _ hne) := by
      show χ ⟨lift s g.1, lift_mem hP g⟩ = _
      exact hP.chr _ _ (lift_triv g.1) _ (by rw [loc_lift]; rfl)
    show theta hP g = 1
    rw [hθ]
    exact hN _ (le_of_lt hg)
  · intro κ hκ hJ h
    exact chi_eq hP κ hκ hJ h

end GlobalTheory.ParaLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceParahoricSubgroupCharacterStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPlaceParahoric_subgroup_character : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (r : ℕ) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.LevelPara J χ s r ξ → (∃ N : ℕ, ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) → ∃ (K : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) (θ : K →* ℂˣ), (∀ g, g ∈ K ↔ NG.ParaRT s r g) ∧ (∀ g (h : g ∈ K) (d : (s.v.adicCompletion (maximalRealSubfield L))ˣ), (d : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r g → θ ⟨g, h⟩ = ξ d) ∧ (∀ g ∈ K, g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) ∧ IsOpen (θ.ker : Set K) ∧ ∀ κ, TrivOutside {s.v} κ → ∀ (hJ : κ ∈ J) (h : s.loc n κ ∈ K), χ ⟨κ, hJ⟩ = θ ⟨s.loc n κ, h⟩ := by
  first | exact @GlobalTheory.ParaLevel.exists_parahoric_char | exact GlobalTheory.ParaLevel.exists_parahoric_char | (intros; apply GlobalTheory.ParaLevel.exists_parahoric_char <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamWeightDirectSum
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.SumRepAdd
open Formalism.BasicNotions.Loc

theorem exists_model : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (a : ℕ) (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)),
    Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) →
    ∀ L₀ : FinExt l, ∃ (LL' : FinExt l) (_ : L₀.1 ≤ LL'.1) (ρ₁ : G D.host.E D.nd.Om →* GL (Fin a) ↥LL'.1),
      Continuous (fun g => ((ρ₁ g : GL (Fin a) ↥LL'.1) : Matrix (Fin a) (Fin a) ↥LL'.1)) ∧
      mapRep (algebraMap ↥LL'.1 (Qbar l)) ρ₁ = ρ := GlobalTheory.T.exists_continuous_ladicGalRep_model_finite_ext_host

theorem dsum_local : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O]
      [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (LL' : FinExt l) (a b : ℕ)
      (r₁ : ↥Gw →* GL (Fin a) ↥LL'.1) (r₂ : ↥Gw →* GL (Fin b) ↥LL'.1),
      (Bw.IsdRE P LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) ↔ Bw.IsdRE P LL' r₁ ∧ Bw.IsdRE P LL' r₂) ∧
      ∀ (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) (c : ℤ),
        Bw.multE P LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) τ' c = Bw.multE P LL' r₁ τ' c + Bw.multE P LL' r₂ τ' c := GlobalTheory.T.sumRep_deRham_iff_and_multiplicity_add

theorem exists_place : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (τ : D.host.E →+* Qbar l), ∃ w : PlE D.host,
    w ∈ placesOver D.host.E l ∧ ∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal := GlobalTheory.T.exists_finitePlace_over_l_of_hostEmbedding_qbar

theorem exists_ext : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (w : PlE D.host) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O),
    GlobalTheory.Pst.Induces Bw → ∀ τ : D.host.E →+* Qbar l, (∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal) →
    ∀ LL' : FinExt l, Bw.LL.1 ≤ LL'.1 → ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1, GlobalTheory.Pst.IsInduced Bw τ τ' := GlobalTheory.T.exists_completionEmbedding_inducing_hostEmbedding

theorem wdOf_sumRep_away : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a b : ℕ)
    (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) (ρ' : G D.host.E D.nd.Om →* GL (Fin b) (Qbar l))
    (w : PlE D.host) (hw : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal),
    Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) →
    Continuous (fun g => ((ρ' g : GL (Fin b) (Qbar l)) : Matrix (Fin b) (Fin b) (Qbar l))) →
    GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') =
      (GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι ρ).lpSum (GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι ρ') := GlobalTheory.T.weilDeligneParamOfLadicRep_sumRep_awayFrom_l_host

theorem wdAt_sumRep : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (ι : Om l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
      (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
      [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces Bw)
      (a b : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (r' : ↥(Dec (F := E) A) →* GL (Fin b) (Om l)),
      GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw r' → GlobalTheory.Pst.IsPstAt P Bw (Formalism.MainNotions.SumRepresentations.At.sumRep r r') →
      GlobalTheory.Pst.wdAt P ι Bw h hj (Formalism.MainNotions.SumRepresentations.At.sumRep r r') =
        (GlobalTheory.Pst.wdAt P ι Bw h hj r).lpSum (GlobalTheory.Pst.wdAt P ι Bw h hj r') := GlobalTheory.T.weilDeligneParamAboveL_directSum_potSemistable

theorem wdAt_bridge : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (ι : Om l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
      (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (O O' : Type) [CommRing O] [Algebra ℤ_[l] O]
      [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (Bw' : LocBridge l E Ω (Dec (F := E) A) O')
      (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw')
      (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)),
      Continuous (fun g => ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) →
      GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw' r →
      GlobalTheory.Pst.wdAt P ι Bw h hj r = GlobalTheory.Pst.wdAt P ι Bw' h hj' r := GlobalTheory.T.weilDeligneParamAbove_l_independent_localEmbedding

end GlobalTheory.SumRepAdd

namespace GlobalTheory.SumRepAdd
open Formalism.BasicNotions.Loc

section Gen
variable {Γ : Type} [Group Γ] {k k' : Type} [CommRing k] [CommRing k'] {a b : ℕ}

theorem sumRep_apply (r₁ : Γ →* GL (Fin a) k) (r₂ : Γ →* GL (Fin b) k) (g : Γ) (i j : Fin (a + b)) :
    ((Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂ g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) i j =
      Matrix.fromBlocks (r₁ g : Matrix (Fin a) (Fin a) k) 0 0 (r₂ g : Matrix (Fin b) (Fin b) k)
        (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) := rfl

theorem mapRep_sumRep (f : k →+* k') (r₁ : Γ →* GL (Fin a) k) (r₂ : Γ →* GL (Fin b) k) :
    mapRep f (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) = Formalism.MainNotions.SumRepresentations.At.sumRep (mapRep f r₁) (mapRep f r₂) := by
  ext g i j
  change f (((Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂ g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) i j) = _
  rw [sumRep_apply, sumRep_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp [mapRep]

theorem comp_sumRep {Δ : Type} [Group Δ] (φ : Δ →* Γ) (r₁ : Γ →* GL (Fin a) k) (r₂ : Γ →* GL (Fin b) k) :
    (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂).comp φ = Formalism.MainNotions.SumRepresentations.At.sumRep (r₁.comp φ) (r₂.comp φ) := by
  ext g i j
  rfl

theorem cont_sumRep [TopologicalSpace Γ] [TopologicalSpace k] (r₁ : Γ →* GL (Fin a) k) (r₂ : Γ →* GL (Fin b) k)
    (h₁ : Continuous fun g => ((r₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (h₂ : Continuous fun g => ((r₂ g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k)) :
    Continuous fun g => ((Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂ g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) := by
  refine continuous_matrix fun i j => ?_
  simp only [sumRep_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j
  · exact h₁.matrix_elem i j
  · exact continuous_const
  · exact continuous_const
  · exact h₂.matrix_elem i j
end Gen

end GlobalTheory.SumRepAdd

namespace GlobalTheory.SumRepAdd
open Formalism.BasicNotions.Loc

section W
variable (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)

theorem model_enlarge {a : ℕ} {L₁ L₂ : FinExt l} (h : L₁.1 ≤ L₂.1) (ρ₁ : G D.host.E D.nd.Om →* GL (Fin a) ↥L₁.1)
    (hc : Continuous (fun g => ((ρ₁ g : GL (Fin a) ↥L₁.1) : Matrix (Fin a) (Fin a) ↥L₁.1))) :
    Continuous (fun g => ((mapRep (IntermediateField.inclusion h).toRingHom ρ₁ g : GL (Fin a) ↥L₂.1) :
      Matrix (Fin a) (Fin a) ↥L₂.1)) ∧
    mapRep (algebraMap ↥L₂.1 (Qbar l)) (mapRep (IntermediateField.inclusion h).toRingHom ρ₁) =
      mapRep (algebraMap ↥L₁.1 (Qbar l)) ρ₁ := by
  refine ⟨continuous_matrix fun i j => continuous_induced_rng.2 ?_, ?_⟩
  · exact (continuous_subtype_val.comp (hc.matrix_elem i j)).congr fun g => rfl
  · ext g i j; rfl

theorem two_models {a b : ℕ} (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
    (ρ' : G D.host.E D.nd.Om →* GL (Fin b) (Qbar l))
    (hρ : Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))))
    (hρ' : Continuous (fun g => ((ρ' g : GL (Fin b) (Qbar l)) : Matrix (Fin b) (Fin b) (Qbar l))))
    (L₀ : FinExt l) :
    ∃ (LL' : FinExt l) (_ : L₀.1 ≤ LL'.1) (ρ₁ : G D.host.E D.nd.Om →* GL (Fin a) ↥LL'.1)
      (ρ₂ : G D.host.E D.nd.Om →* GL (Fin b) ↥LL'.1),
      Continuous (fun g => ((ρ₁ g : GL (Fin a) ↥LL'.1) : Matrix (Fin a) (Fin a) ↥LL'.1)) ∧
      Continuous (fun g => ((ρ₂ g : GL (Fin b) ↥LL'.1) : Matrix (Fin b) (Fin b) ↥LL'.1)) ∧
      mapRep (algebraMap ↥LL'.1 (Qbar l)) ρ₁ = ρ ∧ mapRep (algebraMap ↥LL'.1 (Qbar l)) ρ₂ = ρ' := by
  obtain ⟨L₁, h₁, ρ₁, c₁, e₁⟩ := exists_model D l a ρ hρ L₀
  obtain ⟨L₂, h₂, ρ₂, c₂, e₂⟩ := exists_model D l b ρ' hρ' L₁
  obtain ⟨c, e⟩ := model_enlarge D l h₂ ρ₁ c₁
  exact ⟨L₂, h₁.trans h₂, _, ρ₂, c, c₂, e.trans e₁, e₂⟩

theorem dR_sum {a b : ℕ} (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
    (ρ' : G D.host.E D.nd.Om →* GL (Fin b) (Qbar l))
    (hρ : Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))))
    (hρ' : Continuous (fun g => ((ρ' g : GL (Fin b) (Qbar l)) : Matrix (Fin b) (Fin b) (Qbar l))))
    (w : PlE D.host) (hw : w ∈ placesOver D.host.E l) :
    W.IsdRW l ι (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') w ↔ W.IsdRW l ι ρ w ∧ W.IsdRW l ι ρ' w := by
  obtain ⟨LL, Bw, hj, -⟩ := W.above l ι ρ w hw
  obtain ⟨LL', hL, ρ₁, ρ₂, c₁, c₂, rfl, rfl⟩ := two_models D l ρ ρ' hρ hρ' Bw.LL
  obtain ⟨-, H⟩ := W.loc l ι w hw _ Bw hj ((algebraMap ↥Bw.LL.1 (Om l)).comp Bw.toLL) (fun _ => rfl)
  rw [← mapRep_sumRep, (H LL' hL a ρ₁ c₁).2.1, (H LL' hL b ρ₂ c₂).2.1,
    (H LL' hL (a + b) _ (cont_sumRep ρ₁ ρ₂ c₁ c₂)).2.1, comp_sumRep]
  exact (dsum_local l (D.loc l) (D.locA l) ⟨D.locT l⟩ _ _ _ _ Bw LL' a b _ _).1

end W
end GlobalTheory.SumRepAdd

namespace GlobalTheory.SumRepAdd
open Formalism.BasicNotions.Loc

section W2
variable (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)

theorem jumps_sum {a b : ℕ} (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
    (ρ' : G D.host.E D.nd.Om →* GL (Fin b) (Qbar l))
    (hρ : Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))))
    (hρ' : Continuous (fun g => ((ρ' g : GL (Fin b) (Qbar l)) : Matrix (Fin b) (Fin b) (Qbar l))))
    (τ : D.host.E →+* Qbar l)
    (hτ : ∀ w : PlE D.host, (∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal) →
      W.IsdRW l ι ρ w ∧ W.IsdRW l ι ρ' w) :
    W.jumpsW l ι (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') τ = W.jumpsW l ι ρ τ + W.jumpsW l ι ρ' τ := by
  obtain ⟨w, hw, hτw⟩ := exists_place D l τ
  obtain ⟨d₁, d₂⟩ := hτ w hτw
  have d₃ := (dR_sum D T W l ι ρ ρ' hρ hρ' w hw).2 ⟨d₁, d₂⟩
  obtain ⟨LL, Bw, hj, -⟩ := W.above l ι ρ w hw
  obtain ⟨LL', hL, ρ₁, ρ₂, c₁, c₂, rfl, rfl⟩ := two_models D l ρ ρ' hρ hρ' Bw.LL
  obtain ⟨τ', hτ'⟩ := exists_ext D l w _ Bw hj τ hτw LL' hL
  obtain ⟨-, H⟩ := W.loc l ι w hw _ Bw hj ((algebraMap ↥Bw.LL.1 (Om l)).comp Bw.toLL) (fun _ => rfl)
  obtain ⟨-, dd₁, -, J₁⟩ := H LL' hL a ρ₁ c₁
  obtain ⟨-, dd₂, -, J₂⟩ := H LL' hL b ρ₂ c₂
  obtain ⟨-, dd₃, -, J₃⟩ := H LL' hL (a + b) _ (cont_sumRep ρ₁ ρ₂ c₁ c₂)
  rw [← mapRep_sumRep] at d₃ ⊢
  ext c
  have k₁ := (J₁ τ τ' hτ').2 (dd₁.1 d₁) c
  have k₂ := (J₂ τ τ' hτ').2 (dd₂.1 d₂) c
  have k₃ := (J₃ τ τ' hτ').2 (dd₃.1 d₃) c
  rw [comp_sumRep, (dsum_local l (D.loc l) (D.locA l) ⟨D.locT l⟩ _ _ _ _ Bw LL' a b _ _).2 τ' c, ← k₁, ← k₂] at k₃
  rw [Multiset.count_add]
  exact_mod_cast k₃

theorem wd_sum_away {a b : ℕ} (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
    (ρ' : G D.host.E D.nd.Om →* GL (Fin b) (Qbar l))
    (hρ : Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))))
    (hρ' : Continuous (fun g => ((ρ' g : GL (Fin b) (Qbar l)) : Matrix (Fin b) (Fin b) (Qbar l))))
    (w : PlE D.host) (hw : w ∉ placesOver D.host.E l) :
    W.wdOf l ι (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') w = D.naut.lpSum (W.wdOf l ι ρ w) (W.wdOf l ι ρ' w) := by
  apply (T.e w).injective
  rw [T.sum, W.away l ι _ w hw, W.away l ι ρ w hw, W.away l ι ρ' w hw]
  exact wdOf_sumRep_away D l ι a b ρ ρ' w hw hρ hρ'

theorem pst_of_dR (hB : GlobalTheory.Published.DeRhamPotSemistable) {m : ℕ} (r : G D.host.E D.nd.Om →* GL (Fin m) (Qbar l))
    (hr : Continuous (fun g => ((r g : GL (Fin m) (Qbar l)) : Matrix (Fin m) (Fin m) (Qbar l))))
    (w : PlE D.host) (hw : w ∈ placesOver D.host.E l) (hd : W.IsdRW l ι r w) {LL : FinExt l}
    (B : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) ↥(OL LL)) (hj : GlobalTheory.Pst.Induces B) :
    GlobalTheory.Pst.IsPstAt (D.loc l) B (GlobalTheory.Pst.resDec D.nd.plOm.1 r w) := by
  obtain ⟨LL', hL, r₁, c₁, rfl⟩ := exists_model D l m r hr B.LL
  obtain ⟨-, H⟩ := W.loc l ι w hw _ B hj ((algebraMap ↥B.LL.1 (Om l)).comp B.toLL) (fun _ => rfl)
  have hd' := (H LL' hL m r₁ c₁).2.1
  have hm : GlobalTheory.Pst.IsModel B (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (algebraMap ↥LL'.1 (Qbar l)) r₁) w) LL'
      (r₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) := ⟨hL, rfl⟩
  have hdR : GlobalTheory.Pst.IsdRAt (D.loc l) B (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (algebraMap ↥LL'.1 (Qbar l)) r₁) w) :=
    (hm.isdRAt_iff (D.loc l)).2 (hd'.1 hd)
  exact hB.isPstAt (D.locT l) B _ (hr.comp continuous_subtype_val) hdR

theorem wd_sum_above (hB : GlobalTheory.Published.DeRhamPotSemistable) {a b : ℕ} (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
    (ρ' : G D.host.E D.nd.Om →* GL (Fin b) (Qbar l))
    (hρ : Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))))
    (hρ' : Continuous (fun g => ((ρ' g : GL (Fin b) (Qbar l)) : Matrix (Fin b) (Fin b) (Qbar l))))
    (w : PlE D.host) (hw : w ∈ placesOver D.host.E l) (d₁ : W.IsdRW l ι ρ w) (d₂ : W.IsdRW l ι ρ' w) :
    W.wdOf l ι (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') w = D.naut.lpSum (W.wdOf l ι ρ w) (W.wdOf l ι ρ' w) := by
  have d₃ := (dR_sum D T W l ι ρ ρ' hρ hρ' w hw).2 ⟨d₁, d₂⟩
  have c₃ := cont_sumRep ρ ρ' hρ hρ'
  obtain ⟨p_power_smul_sub_sum, B1, j1, E1⟩ := W.above l ι ρ w hw
  obtain ⟨logJacobianTwoPoints, B2, j2, E2⟩ := W.above l ι ρ' w hw
  obtain ⟨ColumnLift, B3, j3, E3⟩ := W.above l ι (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') w hw
  have tie : Nonempty (LocTied l (D.loc l) (D.locA l)) := ⟨D.locT l⟩
  apply (T.e w).injective
  rw [T.sum, E1, E2, E3]
  have p31 := pst_of_dR D T W l ι hB _ c₃ w hw d₃ B1 j1
  have p33 := pst_of_dR D T W l ι hB _ c₃ w hw d₃ B3 j3
  have p11 := pst_of_dR D T W l ι hB _ hρ w hw d₁ B1 j1
  have p21 := pst_of_dR D T W l ι hB _ hρ' w hw d₂ B1 j1
  have p22 := pst_of_dR D T W l ι hB _ hρ' w hw d₂ B2 j2
  rw [wdAt_bridge l (D.loc l) (D.locA l) tie ι D.host.E D.nd.Om (D.nd.plOm.1 w) w _ _ B3 B1 (D.nd.plOm.2 w) j3 j1 (a + b) _
      (c₃.comp continuous_subtype_val) p33 p31,
    wdAt_bridge l (D.loc l) (D.locA l) tie ι D.host.E D.nd.Om (D.nd.plOm.1 w) w _ _ B2 B1 (D.nd.plOm.2 w) j2 j1 b _
      (hρ'.comp continuous_subtype_val) p22 p21]
  rw [GlobalTheory.Pst.resDec, comp_sumRep] at p31 ⊢
  exact wdAt_sumRep l (D.loc l) (D.locA l) tie ι D.host.E D.nd.Om (D.nd.plOm.1 w) w _ B1 (D.nd.plOm.2 w) j1 a b _ _ p11 p21 p31

end W2

end GlobalTheory.SumRepAdd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParahoricBlockTypeVectorCuspidalSupportTameChara
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParahoricBlockTypeVectorCuspidalSupportTameChara
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BlockSupp

theorem main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (v : π.V), GlobalTheory.SmGL.IsSmoothChar χ → GlobalTheory.SplitWeil.IsTame χ → v ≠ 0 → IsBlockVec χ π.π v → ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), GlobalTheory.SmGL.IsCuspSupport π.π d (fun a => (σ a).π) ∧ t ≤ Set.ncard {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (GlobalTheory.SmGL.detRep (Fin (d a)) (χ * GlobalTheory.SmGL.unrChar k α)))} := by
  intro hBZ hGL _ hDZ k _ _ _ _ r t χ π v hχs hχt hv hbv
  obtain ⟨s, d, σ, hsupp⟩ := GlobalTheory.T.exists_cuspidalSupport_irreducibleSmoothGL hBZ hGL k (r + t) π
  obtain ⟨e, x, hx, hxe⟩ := GlobalTheory.T.tame_block_vector_jacquet_nonzero hDZ k r t χ π v hχt hv hbv
  refine ⟨s, d, σ, hsupp, ?_⟩
  have h := GlobalTheory.T.card_le_unramifiedTwists_cuspidalSupport_jacquet hBZ hGL k (r + t) s (t + 1) χ π d σ _ e (Finset.univ.map (Fin.succEmb t)) x hχs hsupp
    (by intro j hj; obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj; rfl) hx
    (by intro j hj g hg; obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj; exact hxe i g hg)
  simpa using h

end GlobalTheory.BlockSupp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParahoricBlockTypeVectorCuspidalSupportTameCharaStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricBlockTypeVector_cuspidalSupport_tame_characters : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (v : π.V), GlobalTheory.SmGL.IsSmoothChar χ → GlobalTheory.SplitWeil.IsTame χ → v ≠ 0 → IsBlockVec χ π.π v → ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), GlobalTheory.SmGL.IsCuspSupport π.π d (fun a => (σ a).π) ∧ t ≤ Set.ncard {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (GlobalTheory.SmGL.detRep (Fin (d a)) (χ * GlobalTheory.SmGL.unrChar k α)))} := by
  first | exact @GlobalTheory.BlockSupp.main | exact GlobalTheory.BlockSupp.main | (intros; apply GlobalTheory.BlockSupp.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugatePlaceCompletionIsoTame
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypeBlockConj

theorem trivOutside_mul {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x y : GA L n}
    (hx : TrivOutside T x) (hy : TrivOutside T y) : TrivOutside T (x * y) := by
  intro w hw
  have : ((x * y).1 : Matrix (Fin n) (Fin n) (AL L)) =
      (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L)) := rfl
  rw [this, Matrix.map_mul, hx w hw, hy w hw, mul_one]

theorem trivOutside_inv {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x : GA L n}
    (hx : TrivOutside T x) : TrivOutside T x⁻¹ := by
  intro w hw
  have h1 : (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have h2 := congrArg (fun M => M.map (compAt L w)) h1
  simp only [Matrix.map_mul, hx w hw, mul_one] at h2
  rw [h2, Matrix.map_one _ (map_zero _) (map_one _)]

theorem rt_rt {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (a b : GAf L n) (f : GAf L n → W) (g : GAf L n) : NG.rt L n a (NG.rt L n b f) g = f (g * a * b) := rfl

end GlobalTheory.TypeBlockConj

namespace GlobalTheory.TypeBlockConj


end GlobalTheory.TypeBlockConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNhdsOnePrincipalCongruenceSplitPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitCongNbhd

theorem conjAL_entry (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (x : GAf L n) (i j : Fin n) :
    conjAL L (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j)
      = (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
  have hx : ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      conjT (conjAL L) ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := x.2
  have h3 : (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
    rw [← Units.val_mul]; simp
  have h2 : (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      conjT (conjAL L) ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) := by
    calc _ = (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
          (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
            conjT (conjAL L) ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))) := by
            rw [hx, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
  rw [h2]; simp [conjT, Matrix.transpose_apply, Matrix.map_apply]

theorem ringHom_one_apply {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (n : ℕ) (i j : Fin n) :
    f ((1 : Matrix (Fin n) (Fin n) R) i j) = (1 : Matrix (Fin n) (Fin n) S) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp

end GlobalTheory.SplitCongNbhd


open GlobalTheory.SplitCongNbhd in
theorem GlobalTheory.SplitCongNbhd.exists_nhds_one_cong (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (s : SplitPlace L) (N : ℕ) (hN : 0 < N) :
    ∃ U ∈ nhds (1 : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))),
      ∀ x : GAf L n, TrivOutside {s.v} x → s.loc n x ∈ U → NG.Cong L n N x := by
  set K := s.v.adicCompletion (maximalRealSubfield L)
  let U : Set (GL (Fin n) K) := {A | ∀ i j,
    Valued.v ((N : K)⁻¹ * ((A : Matrix (Fin n) (Fin n) K) i j - (1 : Matrix (Fin n) (Fin n) K) i j)) ≤ 1 ∧
    Valued.v ((N : K)⁻¹ * (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j -
      (1 : Matrix (Fin n) (Fin n) K) i j)) ≤ 1}
  refine ⟨U, ?_, ?_⟩
  · have hball : {t : K | Valued.v t ≤ 1} ∈ nhds (0 : K) :=
      (Valued.isOpen_integer K).mem_nhds (by simp [Valuation.mem_integer_iff])
    have key : ∀ f : GL (Fin n) K → K, Continuous f → f 1 = 0 →
        ∀ᶠ A in nhds (1 : GL (Fin n) K), Valued.v (f A) ≤ 1 := by
      intro f hf h1
      exact hf.continuousAt.preimage_mem_nhds (by rw [h1]; exact hball)
    have hc1 : ∀ i j, Continuous fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i j := fun i j =>
      Units.continuous_val.matrix_elem i j
    have hc2 : ∀ i j, Continuous fun A : GL (Fin n) K =>
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j := fun i j =>
      Units.continuous_coe_inv.matrix_elem i j
    have hij : ∀ i j, ∀ᶠ (A : GL (Fin n) K) in nhds 1,
        Valued.v ((N : K)⁻¹ * ((A : Matrix (Fin n) (Fin n) K) i j - (1 : Matrix (Fin n) (Fin n) K) i j)) ≤ 1 ∧
        Valued.v ((N : K)⁻¹ * (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j -
          (1 : Matrix (Fin n) (Fin n) K) i j)) ≤ 1 := fun i j =>
      (key _ (continuous_const.mul ((hc1 i j).sub continuous_const)) (by simp)).and
        (key _ (continuous_const.mul ((hc2 i j).sub continuous_const)) (by simp))
    exact Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hij i j
  · intro x hx hU
    obtain ⟨e, he1, he2⟩ := GlobalTheory.SplitSep.exists_sep L s
    have hN' : (N : L) ≠ 0 := by exact_mod_cast hN.ne'
    set c : AL L := ((N : L)⁻¹) ⊗ₜ[maximalRealSubfield L] (1 : AFplus L) with hc
    have hNc : (N : AL L) * c = 1 := by
      rw [hc, Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hN',
        one_mul]; rfl
    have hconjc : conjAL L c = c := by
      rw [hc, GlobalTheory.SplitLift.conjAL_tmul, map_inv₀, map_natCast]
    have hprojc : s.proj c = (N : K)⁻¹ := by
      rw [hc, GlobalTheory.SplitLift.proj_tmul, map_inv₀, map_natCast]; simp
    set M : Matrix (Fin n) (Fin n) (AL L) := ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) with hM
    have hy : ∀ i j, c * (M i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j) ∈ ALint L := by
      intro i j
      refine GlobalTheory.mem_ALint_of_supported_at_split L s e he1 he2 _ ?_ ?_ ?_
      · intro w hw
        have h1 := congrFun (congrFun (hx w (by simpa using hw)) i) j
        rw [Matrix.map_apply] at h1
        rw [map_mul, map_sub, h1, ringHom_one_apply, sub_self, mul_zero]
      · rw [map_mul, map_sub, hprojc, ringHom_one_apply]
        exact (hU i j).1
      · have hinv : s.proj ((((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) =
            ((((s.loc n x)⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) j i := by
          rw [← map_inv]; rfl
        have h1 : (1 : Matrix (Fin n) (Fin n) K) i j = (1 : Matrix (Fin n) (Fin n) K) j i := by
          simp [Matrix.one_apply, eq_comm]
        rw [map_mul, map_sub, hconjc, hM, conjAL_entry, ringHom_one_apply, map_mul, map_sub, hprojc, hinv,
          ringHom_one_apply, h1]
        exact (hU j i).2
    have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
      intro i j; rw [Matrix.one_apply]; split_ifs
      · exact (ALint L).one_mem
      · exact (ALint L).zero_mem
    have hz : ∀ i j, M i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j =
        (N : AL L) * (c * (M i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j)) := by
      intro i j; rw [← mul_assoc, hNc, one_mul]
    refine ⟨?_, fun i j => ⟨_, hy i j, hz i j⟩⟩
    show ∀ i j, M i j ∈ ALint L
    intro i j
    have : M i j = (N : AL L) * (c * (M i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j)) +
        (1 : Matrix (Fin n) (Fin n) (AL L)) i j := by rw [← hz, sub_add_cancel]
    rw [this]
    exact (ALint L).add_mem ((ALint L).mul_mem (natCast_mem _ _) (hy i j)) (hone i j)
end
