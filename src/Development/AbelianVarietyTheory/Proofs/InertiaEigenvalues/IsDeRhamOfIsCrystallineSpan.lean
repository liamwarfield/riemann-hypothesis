module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusSplitPlaces
public import Formalism.SharpRestriction.LevelLetterCocycles.TWSet
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Formalism.AdmissibleDesigns.RestrictedSevenEightOfFull
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1PeriodDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndepOfLinearIndependentDdRE
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankDdRFinsum
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CharIdem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.Per.CrisDR

section Abstract

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem mem_Dcris_iff (d : V ⊗[Qp] B) : d ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g d = d := by
  simp [Dcris, Submodule.mem_iInf, sub_eq_zero]

theorem mem_DdR_iff (d : V ⊗[Qp] BdR) : d ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g d = d := by
  simp [DdR, Submodule.mem_iInf, sub_eq_zero]

theorem act_mul_ι (g : G) (c : K) (d : V ⊗[Qp] B) :
    actVdR PD ρ g (mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c (ιV PD (LL := LL) (V := V) d)) =
      mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c (ιV PD (LL := LL) (V := V) (actVB PD ρ g d)) := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul v b => simp [actVdR, mulVdR, ιV, actVB, PD.ι_comm]

theorem mul_ι_mem (c : K) {d : V ⊗[Qp] B} (hd : d ∈ Dcris PD ρ) :
    mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c (ιV PD (LL := LL) (V := V) d) ∈ DdR PD ρ := by
  rw [mem_DdR_iff]
  intro g
  rw [act_mul_ι, (mem_Dcris_iff PD ρ d).1 hd g]

theorem coord_mul_ι {I : Type} [DecidableEq I] (b : Basis I Qp V) (j : I) (c : K) (d : V ⊗[Qp] B) :
    equivFinsuppOfBasisLeft b
      (mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c (ιV PD (LL := LL) (V := V) d)) j =
      algebraMap K BdR c * PD.ι (equivFinsuppOfBasisLeft b d j) := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), Finsupp.add_apply, ha, hb, mul_add]
  | tmul v y =>
    have h : ∀ q : Qp, PD.ι (q • y) = q • PD.ι y := fun q =>
      (PD.ι.toLinearMap.restrictScalars Qp).map_smul q y
    simp [mulVdR, ιV, h]

theorem eq_zero_of_sum {m : ℕ} (x : Fin m → K)
    (hx : ∀ b : Fin m → B, ∑ i, algebraMap K BdR (x i) * PD.ι (b i) = 0 → ∀ i, b i = 0)
    (d : Fin m → V ⊗[Qp] B)
    (h : ∑ i, mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (x i) (ιV PD (LL := LL) (V := V) (d i)) = 0)
    (i : Fin m) : d i = 0 := by
  classical
  let b := Basis.ofVectorSpace Qp V
  apply (equivFinsuppOfBasisLeft (N := B) b).injective
  ext j
  rw [map_zero, Finsupp.zero_apply]
  refine hx (fun i => equivFinsuppOfBasisLeft b (d i) j) ?_ i
  have := congrArg (fun z => equivFinsuppOfBasisLeft b z j) h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finsupp.finsetSum_apply, coord_mul_ι, map_zero, Finsupp.zero_apply] at this
  exact this

def cmpMap {m : ℕ} (x : Fin m → K) : (Fin m → ↥(Dcris PD ρ)) →ₗ[LL] ↥(DdR PD ρ) :=
  LinearMap.codRestrict (DdR PD ρ)
    (∑ i, (mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (x i)) ∘ₗ (ιV PD (LL := LL) (V := V)) ∘ₗ
      (Dcris PD ρ).subtype ∘ₗ LinearMap.proj i)
    (fun d => by
      rw [LinearMap.sum_apply]
      exact Submodule.sum_mem _ fun i _ => mul_ι_mem PD ρ (x i) (d i).2)

theorem cmpMap_apply {m : ℕ} (x : Fin m → K) (d : Fin m → ↥(Dcris PD ρ)) :
    (cmpMap PD ρ x d : V ⊗[Qp] BdR) =
      ∑ i, mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (x i) (ιV PD (LL := LL) (V := V) (d i)) := by
  simp [cmpMap, LinearMap.sum_apply]

theorem abstract_cmp
    (hT : ∀ (m : ℕ) (x : Fin m → K), LinearIndependent K₀ x →
      ∀ b : Fin m → B, ∑ i, algebraMap K BdR (x i) * PD.ι (b i) = 0 → ∀ i, b i = 0)
    (hfd : FiniteDimensional LL ↥(DdR PD ρ))
    (hle : finrank LL ↥(DdR PD ρ) ≤ finrank Qp K * finrank LL V)
    (hc : IsCrys PD ρ) :
    finrank LL ↥(DdR PD ρ) = finrank Qp K * finrank LL V ∧
      ∀ y ∈ DdR PD ρ, ∃ (m : ℕ) (c : Fin m → K) (d : Fin m → V ⊗[Qp] B), (∀ i, d i ∈ Dcris PD ρ) ∧
        y = ∑ i, mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (c i) (ιV PD (LL := LL) (V := V) (d i)) := by
  haveI := PD.finK
  haveI : FiniteDimensional K₀ K := Module.Finite.of_restrictScalars_finite Qp K₀ K
  let x := Module.finBasis K₀ K
  have hinj : Function.Injective (cmpMap PD ρ x) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro d hd
    funext i
    apply Subtype.ext
    refine eq_zero_of_sum PD (LL := LL) x (hT _ x x.linearIndependent) (fun i => (d i : V ⊗[Qp] B)) ?_ i
    rw [← cmpMap_apply, hd]
    rfl
  haveI hfdS : FiniteDimensional LL (Fin (finrank K₀ K) → ↥(Dcris PD ρ)) :=
    FiniteDimensional.of_injective _ hinj
  have hpos : 0 < finrank K₀ K := finrank_pos
  haveI : FiniteDimensional LL ↥(Dcris PD ρ) :=
    Module.Finite.of_surjective
      (LinearMap.proj (R := LL) (φ := fun _ : Fin (finrank K₀ K) => ↥(Dcris PD ρ)) ⟨0, hpos⟩)
      (fun y => ⟨fun _ => y, rfl⟩)
  have hS : finrank LL (Fin (finrank K₀ K) → ↥(Dcris PD ρ)) = finrank Qp K * finrank LL V := by
    rw [finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    unfold IsCrys at hc
    rw [hc, ← finrank_mul_finrank Qp K₀ K]
    ring
  have hge := LinearMap.finrank_le_finrank_of_injective hinj
  have heq : finrank LL ↥(DdR PD ρ) = finrank Qp K * finrank LL V := le_antisymm hle (hS ▸ hge)
  refine ⟨heq, fun y hy => ?_⟩
  have hsurj : Function.Surjective (cmpMap PD ρ x) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hS.trans heq.symm)).1 hinj
  obtain ⟨d, hd⟩ := hsurj ⟨y, hy⟩
  refine ⟨_, x, fun i => d i, fun i => (d i).2, ?_⟩
  rw [← cmpMap_apply, hd]

end Abstract

theorem isDR_of_isCrys : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → IsDR (P.PD K) ρ ∧ ∀ y ∈ DdR (P.PD K) ρ, ∃ (m : ℕ) (c : Fin m → ↥K.1) (d : Fin m → V ⊗[ℚ_[l]] P.R.B), (∀ i, d i ∈ Dcris (P.PD K) ρ) ∧ y = ∑ i, mulVdR (K := ↥K.1) (BdR := P.R.BdR) (V := V) (LL := ↥LL.1) (c i) (ιV (P.PD K) (LL := ↥LL.1) (V := V) (d i)) := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ hc
  obtain ⟨hfd, hle⟩ := GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL V ρ
  refine abstract_cmp (P.PD K) ρ (fun m x hx b hb => GlobalTheory.T.injective_tensor_Bcris_to_BdR l P AI T K m x hx b ?_) hfd hle hc
  simpa only [P.PD_ι] using hb

end GlobalTheory.Per.CrisDR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpanStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDeRham_of_isCrystalline_span : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → IsDR (P.PD K) ρ ∧ ∀ y ∈ DdR (P.PD K) ρ, ∃ (m : ℕ) (c : Fin m → ↥K.1) (d : Fin m → V ⊗[ℚ_[l]] P.R.B), (∀ i, d i ∈ Dcris (P.PD K) ρ) ∧ y = ∑ i, mulVdR (K := ↥K.1) (BdR := P.R.BdR) (V := V) (LL := ↥LL.1) (c i) (ιV (P.PD K) (LL := ↥LL.1) (V := V) (d i)) := by
  first | exact @GlobalTheory.Per.CrisDR.isDR_of_isCrys | exact GlobalTheory.Per.CrisDR.isDR_of_isCrys | (intros; apply GlobalTheory.Per.CrisDR.isDR_of_isCrys <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NBasisLoc
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL


set_option maxHeartbeats 1600000 in
theorem N_basis_loc {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ) :
    Nonempty (Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T)) (AA K LL) ↥((H.W K s LL h).N T)) := by
  obtain ⟨_, -, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  haveI := (P.PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hproj := H.W_proj K s LL h T
  generalize H.W K s LL h = W at hproj ⊢
  obtain ⟨hfree, hrk⟩ := W.DD_free T
  rw [← hrk]
  haveI : Module.Finite (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(W.N T) :=
    Module.Finite.iff_fg.mpr (W.N_fg T)
  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h0
    have := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h0
    simp [(Fact.out : l.Prime).ne_zero] at this
  refine GlobalTheory.WachFree.basis_of_regular (ι := ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (O := ↥(OL LL))
    (N := ↥(W.N T)) (E := W.EE) (D := W.DD T) W.EE_inj (W.N T).subtype (W.N_base T hT)
    ((l : ℕ) : ↥(OL LL)) hl0 hl ?_ ?_
  · intro x y hxy
    have h1 : (letπ : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) • (x : W.DD T) =
        (letπ : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) • (y : W.DD T) :=
      congrArg Subtype.val hxy
    rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE letπ (y : W.DD T)] at h1
    exact Subtype.ext (W.EE_π.smul_left_cancel.mp h1)
  · intro x y hxy
    have e1 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) (PowerSeries.C ((l : ℕ) : ℤ_[l])) =
        fun _ => PowerSeries.C ((l : ℕ) : ↥(OL LL)) := by
      funext i
      simp
    have e2 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) PowerSeries.X = fun _ => PowerSeries.X := by
      funext i
      simp [zlA]
    exact GlobalTheory.HWL.mem_smul_of_projective_comp _ hproj ((l : ℕ) : ℤ_[l])
      (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) e1 e2 x y hxy

theorem N_basis : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let _E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → Nonempty (Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T)) (AA K LL) ↥(W.N T)) :=
  fun _ HW _ l _ K s LL h T hT => N_basis_loc (HW l) K s LL h T hT

end GlobalTheory.NL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfIsConjPl
noncomputable section

open GlobalTheory.TwSys Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.ConjugatePlaceSplitting

theorem isSplitPl_of_isConjPl {D : D7} {P P' : PlE D.host} (hs : IsSplitPl D.host P)
    (hc : IsConjPl D.host P P') : IsSplitPl D.host P' := by
  obtain ⟨x, hx, hy⟩ := hs
  have hc' := GlobalTheory.TwistDet.isConjPl_iff.1 hc
  have h1 : GlobalTheory.TwistDet.conjInt D x ∈ P'.asIdeal := (hc' x).1 hx
  have h2 : x ∉ P'.asIdeal := fun h => hy (GlobalTheory.TwistDet.conjInt D x) rfl
    ((hc' (GlobalTheory.TwistDet.conjInt D x)).2 (by rwa [GlobalTheory.TwistDet.conjInt_conjInt]))
  refine ⟨GlobalTheory.TwistDet.conjInt D x, h1, fun y hy' => ?_⟩
  have : y = x := by
    rw [← GlobalTheory.TwistDet.conjInt_conjInt x]
    exact RingOfIntegers.ext hy'
  rwa [this]

end GlobalTheory.ConjugatePlaceSplitting
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionLocalAbove
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionLocalAbove
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section

namespace GlobalTheory.JumpWin

theorem finset_of_rat (F : Finset ℚ) (n N : ℕ) (P : ℤ → Prop) (hF : F.card ≤ n)
    (hP : ∀ a, P a → (a : ℚ) ∈ F ∧ -(N : ℤ) ≤ a ∧ a ≤ N) :
    ∃ U : Finset ℤ, U.card ≤ n ∧ (∀ u ∈ U, -(N : ℤ) ≤ u ∧ u ≤ N) ∧ ∀ a, P a → a ∈ U := by
  classical
  refine ⟨(F.image fun q => ⌊q⌋).filter (fun u => -(N : ℤ) ≤ u ∧ u ≤ N), ?_, ?_, ?_⟩
  · exact (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans hF)
  · intro u hu
    exact (Finset.mem_filter.1 hu).2
  · intro a ha
    obtain ⟨h1, h2⟩ := hP a ha
    refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨(a : ℚ), h1, Int.floor_intCast a⟩, h2⟩

variable {D : D7}

open AdmissibleParameterJ

theorem JW_sub_JJ (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : JW D up j ρ ⊆ JJ D up j ρ := by
  intro q hq
  cases up <;> simp only [JW, cloudT, lowT, JJ, Jp, Jm, reflS, Bool.false_eq_true, if_true, if_false,
    Set.mem_union, Set.mem_setOf_eq] at hq ⊢ <;> tauto

theorem exists_finset_JW (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) :
    ∃ F : Finset ℚ, F.card ≤ D.R.r ∧ ∀ q ∈ JW D up j ρ, q ∈ F := by
  classical
  let cl : Finset ℚ := Finset.univ.image (fun a : Fin (D.R.k - 1) => sz D j ρ + (D.hc ρ).v a + c0 D)
  let lw : Finset ℚ := Finset.univ.image (fun a : Fin D.R.m => sz D j ρ - (D.hc ρ).b a + c0 D)
  have hcard : (cl ∪ lw).card ≤ D.R.r := by
    have h1 : cl.card ≤ D.R.k - 1 := Finset.card_image_le.trans (by simp)
    have h2 : lw.card ≤ D.R.m := Finset.card_image_le.trans (by simp)
    have hk := D.R.m_add_three_le_k
    have : (cl ∪ lw).card ≤ cl.card + lw.card := Finset.card_union_le _ _
    simp only [Ranks.r]
    omega
  have hmem : ∀ q, q ∈ cloudJ D j ρ ∪ lowJ D j ρ → q ∈ cl ∪ lw := by
    intro q hq
    rcases hq with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)
  cases up
  · refine ⟨(cl ∪ lw).image (AdmissibleParameterJ.refl D), Finset.card_image_le.trans hcard, ?_⟩
    intro q hq
    have hq' : AdmissibleParameterJ.refl D q ∈ cloudJ D j ρ ∪ lowJ D j ρ := by
      simpa only [JW, cloudT, lowT, reflS, Bool.false_eq_true, if_false, Set.mem_union,
        Set.mem_setOf_eq] using hq
    refine Finset.mem_image.2 ⟨AdmissibleParameterJ.refl D q, hmem _ hq', ?_⟩
    simp only [AdmissibleParameterJ.refl]; ring
  · refine ⟨cl ∪ lw, hcard, ?_⟩
    intro q hq
    exact hmem q (by simpa only [JW, cloudT, lowT, if_true] using hq)

theorem zero_not_mem_JW (L : SizeData₂ D) (hc : jcCondition L) (up : Bool) (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ D.R.m)
    (ρ : D.what₂.Tau) : (0 : ℚ) ∉ JW D up j ρ := by
  obtain ⟨hlow, -, hcl, h0⟩ := hc j hj1 hj2 ρ
  cases up
  · intro h
    simp only [JW, cloudT, lowT, reflS, Bool.false_eq_true, if_false, Set.mem_union,
      Set.mem_setOf_eq] at h
    have ht : (0 : ℚ) ≤ (D.R.t : ℚ) := Nat.cast_nonneg _
    rcases h with h | h
    · have := hcl _ h
      simp only [AdmissibleParameterJ.refl] at this
      linarith
    · rcases hlow _ h with ⟨-, h'⟩ | ⟨h', -⟩
      · simp only [AdmissibleParameterJ.refl] at h'
        linarith
      · simp only [AdmissibleParameterJ.refl] at h'
        linarith
  · simpa only [JW, cloudT, lowT, if_true] using h0

theorem natAbs_le_of_mem_JJ (L : SizeData₂ D) (he : JumpAbsoluteBound L) (up : Bool) (j : ℕ) (hj1 : 1 ≤ j)
    (hj2 : j ≤ D.R.m) (ρ : D.what₂.Tau) (a : ℤ) (ha : (a : ℚ) ∈ JJ D up j ρ) :
    a.natAbs ≤ ⌊2 * L.sc.b⌋₊ := by
  have h1 := he.1 j hj1 hj2 ρ up _ ha
  have h2 : |((a : ℚ) : ℝ)| ≤ 2 * L.sc.b := by
    have := he.2.1; have := he.2.2.2; linarith
  apply Nat.le_floor
  have : ((a.natAbs : ℕ) : ℝ) = |((a : ℚ) : ℝ)| := by
    rw [Nat.cast_natAbs]; push_cast; rfl
  rw [this]; exact h2

end GlobalTheory.JumpWin


open GlobalTheory.JumpWin AdmissibleParameterJ in
theorem GlobalTheory.jumps_WpO_T2O_window : ∀ (D : D7) (L : SizeData₂ D) (ep : Bool), AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep → AdmissibleParameterJ.CloudCentreDistance L → AdmissibleParameterJ.jcCondition L → AdmissibleParameterJ.JumpAbsoluteBound L → AdmissibleParameterJ.DualCloudSizes L → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1), ∀ M : GE D.nd →* Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i), (M = WpO D.nd i ρ π ∨ M = T2O D.nd i ρ π) → (∃ U : Finset ℤ, U.card ≤ D.R.r ∧ (∀ u ∈ U, -((⌊2 * L.sc.b⌋₊ + 1 : ℕ) : ℤ) ≤ u ∧ u ≤ (⌊2 * L.sc.b⌋₊ + 1 : ℕ)) ∧ ∀ a, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ a → a ∈ U) ∧ ¬ IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ 0 := by
  intro D L ep hA _hb hc he hf i r ρ π hr hπ hdec w hw C τ M hM
  classical
  obtain ⟨g, ρ', -, -, hT⟩ := hA i r hr w hw C τ
  have hj := D.nd.j_range i
  have hW := hT ρ π hπ hdec
  generalize decide (TypeU D ep g) = up at hW
  obtain ⟨F, hFc, hFm⟩ := exists_finset_JW up (D.nd.j i) ρ'
  rcases hM with rfl | rfl
  · refine ⟨finset_of_rat F D.R.r (⌊2 * L.sc.b⌋₊ + 1) _ hFc ?_, ?_⟩
    · intro a ha
      have hq := ((hW a).1).1 ha
      have hn := natAbs_le_of_mem_JJ L he up _ hj.1 hj.2 ρ' a (JW_sub_JJ up _ ρ' hq)
      refine ⟨hFm _ hq, ?_, ?_⟩ <;> push_cast <;> omega
    · intro h0
      have := ((hW 0).1).1 h0
      exact zero_not_mem_JW L hc up _ hj.1 hj.2 ρ' (by simpa using this)
  · refine ⟨finset_of_rat (F.image fun q => -q - 1) D.R.r (⌊2 * L.sc.b⌋₊ + 1) _
      (Finset.card_image_le.trans hFc) ?_, ?_⟩
    · intro a ha
      have hq : -(a : ℚ) - 1 ∈ JW D up (D.nd.j i) ρ' := ((hW a).2.2.1).1 ha
      have hq' : (((-a - 1 : ℤ)) : ℚ) ∈ JW D up (D.nd.j i) ρ' := by push_cast; exact hq
      have hn := natAbs_le_of_mem_JJ L he up _ hj.1 hj.2 ρ' _ (JW_sub_JJ up _ ρ' hq')
      refine ⟨Finset.mem_image.2 ⟨_, hFm _ hq, by ring⟩, ?_, ?_⟩ <;> push_cast <;> omega
    · intro h0
      have := ((hW 0).2.2.1).1 h0
      exact (hf _ hj.1 hj.2 ρ').2.2.1 up (by simpa using this)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionLocalAboveStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decomposition_local_above : ∀ (D : D7) (L : SizeData₂ D) (ep : Bool), AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep → AdmissibleParameterJ.CloudCentreDistance L → AdmissibleParameterJ.jcCondition L → AdmissibleParameterJ.JumpAbsoluteBound L → AdmissibleParameterJ.DualCloudSizes L → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1), ∀ M : GE D.nd →* Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i), (M = WpO D.nd i ρ π ∨ M = T2O D.nd i ρ π) → (∃ U : Finset ℤ, U.card ≤ D.R.r ∧ (∀ u ∈ U, -((⌊2 * L.sc.b⌋₊ + 1 : ℕ) : ℤ) ≤ u ∧ u ≤ (⌊2 * L.sc.b⌋₊ + 1 : ℕ)) ∧ ∀ a, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ a → a ∈ U) ∧ ¬ IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ 0 := by
  first | exact @GlobalTheory.jumps_WpO_T2O_window | exact GlobalTheory.jumps_WpO_T2O_window | (intros; apply GlobalTheory.jumps_WpO_T2O_window <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OfShortExact
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineInequalityDcrisFiniteConcreteRingsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaine_inequality_dcris_finite_concrete_rings : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K LL : FinExt l, FontaineLe (P.PD K) ↥LL.1 ∧ ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), FiniteDimensional ↥LL.1 ↥(Dcris (P.PD K) ρ) := by
  intro l _ P AI T K LL
  have key : ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
      [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V),
      Module.Finite ↥LL.1 (Dcris (P.PD K) ρ) ∧
        Module.finrank ↥LL.1 (Dcris (P.PD K) ρ) ≤ Module.finrank ℚ_[l] ↥(K0 K) * Module.finrank ↥LL.1 V := by
    intro V _ _ _ _ _ ρ
    have := GlobalTheory.Per.FontaineBound.isDomain_cris (PD := P.PD K) (GlobalTheory.Per.FontaineBound.isField_of_tied T)
    have := (P.PD K).finK₀
    have := LL.2
    refine GlobalTheory.Per.FontaineBound.finite_finrank_le (P.PD K).actB (fun b b' hb h => GlobalTheory.Per.FracInv.tied_frac_invariant l P AI T K b' b hb fun g hg => ?_) ρ
    have h1 := h ⟨g, hg⟩
    rw [P.PD_actB, P.PD_actB] at h1
    rw [mul_comm, h1, mul_comm]
  exact ⟨fun V _ _ _ _ _ ρ => (key V ρ).2, fun V _ _ _ _ _ ρ => (key V ρ).1⟩
end

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.FontCmp

namespace GlobalTheory.Per.CrysSubQuot

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V₀ : Type} [AddCommGroup V₀] [Module LL V₀] [Module Qp V₀] [IsScalarTower Qp LL V₀]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem of_shortExact [FiniteDimensional LL V]
    {ρ₀ : Representation LL G V₀} {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    {i : V₀ →ₗ[LL] V} {p : V →ₗ[LL] V'} (hi : IsEquivariant ρ₀ ρ i) (hp : IsEquivariant ρ ρ' p)
    (h1 : Function.Injective i) (h2 : Function.Exact i p) (h3 : Function.Surjective p)
    [Module.Finite LL ↥(Dcris PD ρ)] [Module.Finite LL ↥(Dcris PD ρ')]
    (a : finrank LL ↥(Dcris PD ρ₀) ≤ finrank Qp K₀ * finrank LL V₀)
    (c : finrank LL ↥(Dcris PD ρ') ≤ finrank Qp K₀ * finrank LL V')
    (h : IsCrys PD ρ) :
    IsCrys PD ρ₀ ∧ IsCrys PD ρ' ∧ Function.Surjective (DcrisMap PD hp) := by
  obtain ⟨e1, e2⟩ := GlobalTheory.RegularRing.left_exact PD hi hp h1 h2 h3
  have h4 := (DcrisMap PD hp).finrank_range_add_finrank_ker
  rw [e2.linearMap_ker_eq, LinearMap.finrank_range_of_inj e1] at h4
  have h5 := p.finrank_range_add_finrank_ker
  rw [h2.linearMap_ker_eq, LinearMap.finrank_range_of_inj h1, LinearMap.range_eq_top.2 h3, finrank_top] at h5
  have h6 := (LinearMap.range (DcrisMap PD hp)).finrank_le
  unfold IsCrys at h ⊢
  rw [← h5, mul_add] at h
  refine ⟨by omega, by omega, ?_⟩
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  omega

end Generic

theorem crys_sub_quot : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (f : V →ₗ[↥LL.1] V'), (∀ g x, f (ρ g x) = ρ' g (f x)) → (Function.Injective f → IsCrys (P.PD K) ρ' → IsCrys (P.PD K) ρ) ∧ (Function.Surjective f → IsCrys (P.PD K) ρ → IsCrys (P.PD K) ρ' ∧ ∀ y ∈ Dcris (P.PD K) ρ', ∃ x ∈ Dcris (P.PD K) ρ, AlgebraTensorModule.map f (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B) x = y) := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' f hf
  obtain ⟨hle, hfin⟩ := GlobalTheory.T.fontaine_inequality_dcris_finite_concrete_rings l P AI T K LL
  have he : IsEquivariant ρ ρ' f := hf
  have := hfin V ρ
  have := hfin V' ρ'
  refine ⟨fun hi h => ?_, fun hs h => ?_⟩
  · have hst : ∀ g, LinearMap.range f ≤ (LinearMap.range f).comap (ρ' g) := by
      rintro g _ ⟨v, rfl⟩
      exact ⟨ρ g v, hf g v⟩
    have hq : IsEquivariant ρ' (ρ'.quotient (LinearMap.range f) hst) (LinearMap.range f).mkQ :=
      fun g v => rfl
    have := hfin _ (ρ'.quotient (LinearMap.range f) hst)
    exact (of_shortExact (P.PD K) he hq hi (LinearMap.exact_map_mkQ_range f)
      (LinearMap.range f).mkQ_surjective (hle V ρ) (hle _ _) h).1
  · have hst : ∀ g, LinearMap.ker f ≤ (LinearMap.ker f).comap (ρ g) := by
      intro g v hv
      rw [Submodule.mem_comap, LinearMap.mem_ker, hf, LinearMap.mem_ker.1 hv, map_zero]
    have hq : IsEquivariant (ρ.subrepresentation (LinearMap.ker f) hst) ρ (LinearMap.ker f).subtype :=
      fun g v => rfl
    obtain ⟨-, h1, h2⟩ := of_shortExact (P.PD K) hq he (LinearMap.ker f).injective_subtype
      (LinearMap.exact_subtype_ker_map f) hs (hle _ _) (hle V' ρ') h
    refine ⟨h1, fun y hy => ?_⟩
    obtain ⟨x, hx⟩ := h2 ⟨y, hy⟩
    exact ⟨x.1, x.2, congrArg Subtype.val hx⟩

end GlobalTheory.Per.CrysSubQuot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateFinitenessAllOfLocalTateDuality
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateFinitenessAllOfLocalTateDuality
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory

theorem finAll_of_localTateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.FinAll D := by
  intro hT D i w hw C
  exact Formalism.MainNotions.LargeLevelLemmas.tate_h1_finite_of_all_coefficients _ _ _
    (GlobalTheory.T.finite_H1_period_datum hT (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw)
    (GlobalTheory.T.padicIntegers_finiteExt_goodCoefficientRing (D.nd.l i) C.LL)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateFinitenessAllOfLocalTateDualityStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateFinitenessAll_of_localTateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.FinAll D := by
  first | exact @GlobalTheory.finAll_of_localTateDuality | exact GlobalTheory.finAll_of_localTateDuality | (intros; apply GlobalTheory.finAll_of_localTateDuality <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisLetterDeRhamComponentEqDim
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisLetterDeRhamComponentEqDim
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.LetterDim

theorem card_le_of_idem {R : Type} [CommRing R] {e : R} (he : e * e = e) (he0 : e ≠ 0)
    {ι κ : Type} [Fintype ι] [Fintype κ] (a : ι → κ → R)
    (h : ∀ r : ι → R, (∀ j, ∑ i, r i * a i j = 0) → ∀ i, e * r i = 0) :
    Fintype.card ι ≤ Fintype.card κ := by
  let I : Ideal R := Ideal.span {1 - e}
  have hI : ∀ x, x ∈ I ↔ e * x = 0 := by
    intro x
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, rfl⟩
      linear_combination (-c) * he
    · intro hx
      exact ⟨x, by linear_combination -hx⟩
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 (by
    intro hT
    have : (1 : R) ∈ I := by rw [hT]; trivial
    rw [hI, mul_one] at this
    exact he0 this)
  have hli : LinearIndependent (R ⧸ I) (fun i j => Ideal.Quotient.mk I (a i j)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose r hr using fun i => Ideal.Quotient.mk_surjective (g i)
    rw [← hr, Ideal.Quotient.eq_zero_iff_mem, hI, ← he, mul_assoc]
    refine h (fun i => e * r i) (fun j => ?_) i
    have := congrFun hg j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, ← hr, ← map_mul,
      ← map_sum] at this
    rw [Ideal.Quotient.eq_zero_iff_mem, hI, Finset.mul_sum] at this
    simpa only [mul_assoc] using this
  simpa using hli.fintype_card_le_finrank

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V]


open GlobalTheory.DRFil in
theorem component_le [FiniteDimensional Qp K] [CharZero Qp] (hF : IsField F) (ρ : Representation LL G V)
    (τ : K →ₐ[Qp] LL) [FiniteDimensional LL ↥(DdRE PD ρ τ)] :
    finrank LL ↥(DdRE PD ρ τ) ≤ finrank LL V := by
  haveI := nontrivial_dR PD
  let b := Module.finBasis LL ↥(DdRE PD ρ τ)
  let v := Module.finBasis LL V
  have hli : LinearIndependent LL (fun i => (b i : V ⊗[Qp] F)) :=
    b.linearIndependent.map' (DdRE PD ρ τ).subtype (Submodule.ker_subtype _)
  have h := indep_of_linearIndependent_DdRE PD ρ τ _ hF (fun i => (b i).2) hli
  have := card_le_of_idem (idem_mul_idem (F := F) τ) (idem_ne_zero (F := F) τ)
    (fun i j => ext Qp F (v.coord j) (b i : V ⊗[Qp] F)) (fun r hr => h r (by
      rw [eq_sum_basis v (∑ i, sm Qp F LL V (r i) (b i : V ⊗[Qp] F))]
      refine Finset.sum_eq_zero fun j _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [ext_sm, sm_self]
      rw [hr j, map_zero, LinearMap.zero_apply]))
  simpa using this

theorem component_eq [CharZero Qp] (hF : IsField F) (ρ : Representation LL G V)
    (hc : Nat.card (K →ₐ[Qp] LL) = finrank Qp K) (h : IsDR PD ρ) (τ : K →ₐ[Qp] LL) :
    finrank LL ↥(DdRE PD ρ τ) = finrank LL V := by
  haveI := PD.finK
  haveI := (GlobalTheory.Per.FontaineBound.ddR_finite_le PD hF ρ).1
  haveI : ∀ τ, FiniteDimensional LL ↥(DdRE PD ρ τ) := fun τ =>
    Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ) inf_le_left
  rw [Nat.card_eq_fintype_card] at hc
  have hs := (GlobalTheory.DeRhamSplit.finrank_DdR PD ρ hc 0).1
  unfold IsDR at h
  refine (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (g := fun _ => finrank LL V)
    fun τ _ => component_le PD hF ρ τ).1 ?_ τ (Finset.mem_univ τ)
  rw [← hs, h, Finset.sum_const, Finset.card_univ, hc, smul_eq_mul]


omit [FiniteDimensional Qp LL] in
theorem finite_Dcris (ρ : Representation LL G V) (h : IsCrys PD ρ) : Module.Finite LL ↥(Dcris PD ρ) := by
  haveI := PD.finK₀
  rcases Nat.eq_zero_or_pos (finrank LL V) with h0 | h0
  · haveI : Subsingleton V := finrank_zero_iff.1 h0
    infer_instance
  · exact FiniteDimensional.of_finrank_pos (by
      unfold IsCrys at h
      rw [h]
      exact Nat.mul_pos finrank_pos h0)


omit [FiniteDimensional Qp LL] in
open GlobalTheory.RegularRing in
theorem letter_eq [IsDomain B] (ρ : Representation LL G V)
    (hc : Nat.card (K₀ →ₐ[Qp] LL) = finrank Qp K₀) (h : IsCrys PD ρ) (τ : K₀ →ₐ[Qp] LL) :
    finrank LL ↥(DcrisL PD ρ τ) = finrank LL V := by
  haveI := PD.finK₀
  haveI := finite_Dcris PD ρ h
  have hle : ∀ (n : ℕ) (τ τ' : K₀ →ₐ[Qp] LL), (∀ c, τ' c = τ (PD.σ^[n] c)) →
      finrank LL ↥(DcrisL PD ρ τ') ≤ finrank LL ↥(DcrisL PD ρ τ) := by
    intro n
    induction n with
    | zero =>
      intro τ τ' h
      rw [show τ' = τ from AlgHom.ext h]
    | succ n ih =>
      intro τ τ' h
      exact (ih (τ.comp PD.σ) τ' fun c => by rw [h, Function.iterate_succ_apply']; rfl).trans
        (letter_le PD (LL := LL) ρ τ _ fun _ => rfl)
  have heq : ∀ τ', finrank LL ↥(DcrisL PD ρ τ') = finrank LL ↥(DcrisL PD ρ τ) := fun τ' => by
    obtain ⟨n, hn⟩ := exists_pow_sigma PD LL hc τ τ'
    obtain ⟨n', hn'⟩ := exists_pow_sigma PD LL hc τ' τ
    exact le_antisymm (hle n _ _ hn) (hle n' _ _ hn')
  rw [Nat.card_eq_fintype_card] at hc
  have hs : finrank LL ↥(Dcris PD ρ) = ∑ τ', finrank LL ↥(DcrisL PD ρ τ') :=
    GlobalTheory.DeRhamSplit.finrank_eq_sum hc (GlobalTheory.DeRhamSplit.mulHom Qp K₀ B LL V) (Dcris PD ρ)
      fun a x hx => (GlobalTheory.FontCmp.mK PD ρ a ⟨x, hx⟩).2
  simp only [heq, Finset.sum_const, Finset.card_univ, smul_eq_mul, hc] at hs
  unfold IsCrys at h
  exact Nat.eq_of_mul_eq_mul_left finrank_pos (hs.symm.trans h)

end General

theorem tied_letter_component_finrank : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), (Nat.card (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥(K0 K) → IsCrys (P.PD K) ρ → ∀ τ, Module.finrank ↥LL.1 ↥(DcrisL (P.PD K) ρ τ) = Module.finrank ↥LL.1 V) ∧ (Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 → IsDR (P.PD K) ρ → ∀ τ, Module.finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) = Module.finrank ↥LL.1 V) := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ
  haveI := LL.2
  haveI := GlobalTheory.RegularRing.isDomain_of_tied T K
  exact ⟨letter_eq (P.PD K) ρ, component_eq (P.PD K) (GlobalTheory.RegularRing.isField_of_tied T) ρ⟩

end GlobalTheory.Per.LetterDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisLetterDeRhamComponentEqDimStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_dcrisLetter_deRhamComponent_eq_dim : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), (Nat.card (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥(K0 K) → IsCrys (P.PD K) ρ → ∀ τ, Module.finrank ↥LL.1 ↥(DcrisL (P.PD K) ρ τ) = Module.finrank ↥LL.1 V) ∧ (Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 → IsDR (P.PD K) ρ → ∀ τ, Module.finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) = Module.finrank ↥LL.1 V) := by
  first | exact @GlobalTheory.Per.LetterDim.tied_letter_component_finrank | exact GlobalTheory.Per.LetterDim.tied_letter_component_finrank | (intros; apply GlobalTheory.Per.LetterDim.tied_letter_component_finrank <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SimpleRepCentralIdempotentIsCentralIdempotent
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SimpleRepCentralIdempotentIsCentralIdempotent
open Formalism.IrreducibleCountingLemmas.TYPES (zIdem)
open Formalism.L2.NT
open Polynomial CategoryTheory

namespace GlobalTheory.SerOSys

theorem zIdem_eq_charIdem {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) :
    zIdem τ = PI.CharIdem.charIdem τ := by
  unfold zIdem PI.CharIdem.charIdem
  rfl

theorem zIdem_centralIdempotent : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ), Simple τ →
    zIdem τ * zIdem τ = zIdem τ ∧ ∀ a, zIdem τ * a = a * zIdem τ := by
  intro Γ _ _ τ hτ
  have h := orthogonalCentral Γ τ τ hτ hτ
  rw [zIdem_eq_charIdem]
  exact ⟨h.2.2.1, h.2.2.2.1⟩

end GlobalTheory.SerOSys
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SimpleRepCentralIdempotentIsCentralIdempotentStatement
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simpleRepCentralIdempotent_isCentralIdempotent : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ), Simple τ → zIdem τ * zIdem τ = zIdem τ ∧ ∀ a, zIdem τ * a = a * zIdem τ := by
  first | exact @GlobalTheory.SerOSys.zIdem_centralIdempotent | exact GlobalTheory.SerOSys.zIdem_centralIdempotent | (intros; apply GlobalTheory.SerOSys.zIdem_centralIdempotent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSumOfIsCrys
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndepOfFracInv
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.TiedIndep

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]


omit [Field K₀] [Algebra Qp K₀] [Algebra K₀ B] [IsScalarTower Qp K₀ B] in
theorem comm_smul (b : B) (w : B ⊗[Qp] V) :
    TensorProduct.comm Qp B V (b • w) =
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp b)
        (TensorProduct.comm Qp B V w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul c v => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

end Generic

end GlobalTheory.Per.TiedIndep
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.TiedSpan

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem exists_sum_of_isCrys [IsDomain B] (hf : GlobalTheory.RegularRing.FracInv PD)
    (hu : GlobalTheory.RegularRing.LineUnit PD) [FiniteDimensional Qp LL] [FiniteDimensional LL V]
    (ρ : Representation LL G V) (h : IsCrys PD ρ) (y : V ⊗[Qp] B) :
    ∃ (m : ℕ) (b : Fin m → B) (d : Fin m → V ⊗[Qp] B), (∀ i, d i ∈ Dcris PD ρ) ∧
      y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp (b i)) (d i) := by
  have hs := (GlobalTheory.RegularRing.isCrys_iff_span PD hf hu ρ).1 h
  have hy : (TensorProduct.comm Qp B V).symm y ∈
      Submodule.span B (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.DcrisK₀ PD ρ : Set (B ⊗[Qp] V)) := hs ▸ Submodule.mem_top
  obtain ⟨m, b, e, he⟩ := Submodule.mem_span_set'.1 hy
  refine ⟨m, b, fun i => TensorProduct.comm Qp B V (e i : B ⊗[Qp] V), fun i => (e i).2, ?_⟩
  have h2 := congrArg (TensorProduct.comm Qp B V) he
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearEquiv.apply_symm_apply, map_sum] at h2
  rw [← h2]
  exact Finset.sum_congr rfl fun i _ => GlobalTheory.Per.TiedIndep.comm_smul (LL := LL) _ _

end Generic

theorem tied_crisSpan : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → (∀ (K : FinExt l) (b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, ∃ x : ℚ_[l], P.actQ g b = x • b) → IsUnit b) → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → ∀ y : V ⊗[ℚ_[l]] P.R.B, ∃ (m : ℕ) (b : Fin m → P.R.B) (d : Fin m → V ⊗[ℚ_[l]] P.R.B), (∀ i, d i ∈ Dcris (P.PD K) ρ) ∧ y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[↥LL.1] V) (LinearMap.mulLeft ℚ_[l] (b i)) (d i) := by
  intro l _ P AI T hreg K LL V _ _ _ _ _ ρ h y
  have : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T K
  have := LL.2
  have e : ∀ (g : ↥(GK K)) z, (P.PD K).actB g z = P.actQ g z := fun g z => P.PD_actB K g z
  refine exists_sum_of_isCrys (P.PD K) ?_ ?_ ρ h y
  · intro x y hx h
    refine GlobalTheory.Per.FracInv.tied_frac_invariant l P AI T K y x hx fun g hg => ?_
    have h1 := h ⟨g, hg⟩
    rw [e, e] at h1
    rw [mul_comm, h1, mul_comm]
  · intro b hb h
    refine hreg K b hb fun g hg => ?_
    obtain ⟨x, hx⟩ := h ⟨g, hg⟩
    rw [e] at hx
    exact ⟨x, by rw [Algebra.smul_def]; exact hx⟩

end GlobalTheory.Per.TiedSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineInequalityDcrisFiniteConcreteRings
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

namespace GlobalTheory.Per.FontaineBound

theorem dcris_finite_le_of_tied {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) :
    Module.Finite ↥LL.1 (Dcris (P.PD K) ρ) ∧
      finrank ↥LL.1 (Dcris (P.PD K) ρ) ≤ finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 V := by
  have := isDomain_cris (P.PD K) (isField_of_tied T)
  have := (P.PD K).finK₀
  have := LL.2
  refine finite_finrank_le (P.PD K).actB (fun b b' hb h => GlobalTheory.T.ratio_invariant_in_K0 l P AI T K b' b hb fun g hg => ?_) ρ
  have h1 := h ⟨g, hg⟩
  rw [P.PD_actB, P.PD_actB] at h1
  rw [mul_comm, h1, mul_comm]

theorem fontaineLe_of_tied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ K LL : FinExt l, FontaineLe (P.PD K) ↥LL.1 ∧
      ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
        [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V),
        FiniteDimensional ↥LL.1 ↥(Dcris (P.PD K) ρ) :=
  fun _ _ _ _ T K LL => ⟨fun V _ _ _ _ _ ρ => (dcris_finite_le_of_tied T K LL V ρ).2,
    fun V _ _ _ _ _ ρ => (dcris_finite_le_of_tied T K LL V ρ).1⟩

end GlobalTheory.Per.FontaineBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleParametersOfLargeScale
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleParamsOfRoomy
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem admissible_params_of_roomy {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) (h : Roomy L 100) :
    (L.etaSz + D.R.t + L.Sc + 2 < L.sc.w'' D.R.n ∧ L.sc.w'' D.R.n ≤ L.sc.b' ∧ 100 * L.sc.b' ≤ L.sc.b ∧
      (∀ t, (L.bT t : ℝ) + L.sc.b' / L.sc.x ≤ 3 / 2 * L.sc.b') ∧ (D.R.t : ℝ) ≤ L.etaSz) ∧
      L.Sc + L.etaSz + D.R.t + 2 ≤ L.sc.b := by
  obtain ⟨-, h1, h2, h3, h4, h5⟩ := h
  have he := L.etaSz_pos
  have hS := L.Sc_pos
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hL : (0 : ℝ) ≤ (D.host.Lw : ℝ) := by positivity
  have hb : (0 : ℝ) ≤ L.sc.b' := by linarith
  have hm : (0 : ℝ) ≤ (D.host.Lw : ℝ) * L.sc.b' := mul_nonneg hL hb
  have h6 : 100 * L.sc.b' ≤ L.sc.b := by nlinarith
  refine ⟨⟨by linarith, h3, h6, h4, P.t_le_eta⟩, by linarith⟩

theorem admissible_params_large : ∀ eps A : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L), L.sc.eps = eps → P.CLw ≤ A → x0 ≤ L.sc.x → (L.etaSz + D.R.t + L.Sc + 2 < L.sc.w'' D.R.n ∧ L.sc.w'' D.R.n ≤ L.sc.b' ∧ 100 * L.sc.b' ≤ L.sc.b ∧ (∀ t, (L.bT t : ℝ) + L.sc.b' / L.sc.x ≤ 3 / 2 * L.sc.b') ∧ (D.R.t : ℝ) ≤ L.etaSz) ∧ L.Sc + L.etaSz + D.R.t + 2 ≤ L.sc.b := by
  intro eps A heps
  obtain ⟨x0, hx0⟩ := GlobalTheory.T.roomy_of_large_scale eps 100 A heps le_rfl
  exact ⟨x0, fun D L P h1 h2 h3 => admissible_params_of_roomy L P (hx0 D L P h1 h2 h3)⟩

end GlobalTheory.HTW
end

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.HTW

theorem admissibleParameters_of_large_scale : ∀ eps A : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L), L.sc.eps = eps → P.CLw ≤ A → x0 ≤ L.sc.x → AdmissibleParameterJ.AdmPar L ∧ EmbeddingTypeJumps.ParametersPolynomiallyBounded L := by
  intro eps A heps
  obtain ⟨x0, hx0⟩ := admissible_params_large eps A heps
  refine ⟨x0, fun D L P h1 h2 h3 => ?_⟩
  obtain ⟨⟨hw, hwb, hbb, hT, ht⟩, hS⟩ := hx0 D L P h1 h2 h3
  have he := L.etaSz_pos
  have hSc := L.Sc_pos
  have htt : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  refine ⟨⟨by linarith, by linarith, fun tt => by linarith [hT tt], ht⟩, hS⟩

end GlobalTheory.HTW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDegreeSum
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.Proof.LocalDegreeSum

theorem sum_locDeg : ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] [Fintype {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}], ∑ v : {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}, ReciprocityTheory.Gal.locDeg v.1 = Module.finrank ℚ F := by
  intro F _ _ l hl _
  classical

  set p : Ideal ℤ := Ideal.span {(l : ℤ)} with hp
  have hpmax : p.IsMaximal := Int.ideal_span_isMaximal_of_prime l
  have : p.IsPrime := hpmax.isPrime
  have hp0 : p ≠ 0 := by
    rw [hp, Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.out.ne_zero

  have key : ∀ v : HeightOneSpectrum (𝓞 F),
      ((l : ℕ) : 𝓞 F) ∈ v.asIdeal ↔ v.asIdeal ∣ Ideal.map (algebraMap ℤ (𝓞 F)) p := by
    intro v
    rw [Ideal.dvd_iff_le, hp, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_le_iff_mem]
    simp

  let e := (Equiv.subtypeEquivRight key).trans (HeightOneSpectrum.equivPrimesOver (𝓞 F) hp0)
  rw [← NumberField.RingOfIntegers.rank, ← Ideal.sum_ramification_inertia_eq_finrank p (𝓞 F)]
  exact Fintype.sum_equiv e _ _ (fun v => by rfl)

end GlobalTheory.Proof.LocalDegreeSum
end
