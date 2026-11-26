module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdelicExtensionOfAlgebraicWeightDefiniteUn
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassNumberAll
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryVolumeEqRankMassAllSignatures

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DefiniteUnitaryRealApproxAndFiniteInfiniteSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DefiniteUnitaryRealApproxAndFiniteInfiniteSplit
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open scoped Pointwise

noncomputable section

namespace GlobalTheory.UnitarySplit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def finPart : UA E n →* finU (E := E) (n := n) :=
  ((((finGL E n).comp (GeneralLinearGroup.map (pFin E))).comp (UA E n).subtype).codRestrict (UA E n)
    fun g => GlobalTheory.DefU.ClassFin.finGL_mem_UA _ (GlobalTheory.DefU.ClassFin.cT_pFin g)).codRestrict (finU (E := E) (n := n))
    fun _ => pInf_finGL _

def infPart : UA E n →* infU E n :=
  (((infGL E n).comp cInf).codRestrict (UA E n)
    fun g => by
      have h := (UA E n).mul_mem g.2 ((UA E n).inv_mem (finPart g).1.2)
      have e : (finPart g).1.1 = finGL E n (GeneralLinearGroup.map (pFin E) g.1) := rfl
      rw [e] at h
      nth_rewrite 1 [← infGL_mul_finGL g.1] at h
      rw [mul_inv_cancel_right] at h
      exact h).codRestrict (infU E n)
    fun _ => pFin_infGL _

theorem finPart_val (g : UA E n) : (finPart g).1.1 = finGL E n (GeneralLinearGroup.map (pFin E) g.1) := rfl

theorem infPart_val (g : UA E n) : (infPart g).1.1 = infGL E n (GeneralLinearGroup.map (pInf E) g.1) := rfl

theorem continuous_finPart : Continuous (finPart (E := E) (n := n)) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  exact GlobalTheory.DefU.ClassFin.continuous_finGL.comp
    ((Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))).comp
      continuous_subtype_val)

theorem continuous_infPart : Continuous (infPart (E := E) (n := n)) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  exact GlobalTheory.DefU.continuous_infGL.comp GlobalTheory.DefU.continuous_cInf

theorem finPart_mul_infPart (g : UA E n) : g = (finPart g).1 * (infPart g).1 := by
  rw [GlobalTheory.DefU.fin_mul_inf (finPart g).2 (infPart g).2]
  exact Subtype.ext (infGL_mul_finGL g.1).symm

theorem cInf_infPart (g : UA E n) : cInf (infPart g).1 = cInf g := pInf_infGL _

theorem finPart_fin (g : finU (E := E) (n := n)) : finPart g.1 = g :=
  Subtype.ext (Subtype.ext (GlobalTheory.CuspRep.ga_ext ((pInf_finGL _).trans g.2.symm) (pFin_finGL _)))

theorem infPart_inf (k : infU E n) : infPart k.1 = k :=
  Subtype.ext (Subtype.ext (GlobalTheory.CuspRep.ga_ext (pInf_infGL _) ((pFin_infGL _).trans k.2.symm)))

theorem finPart_inf (k : infU E n) : finPart k.1 = 1 := by
  refine Subtype.ext (Subtype.ext ?_)
  have h : GeneralLinearGroup.map (pFin E) k.1.1 = 1 := k.2
  rw [finPart_val, h, map_one]
  rfl

theorem infPart_fin (g : finU (E := E) (n := n)) : infPart g.1 = 1 := by
  refine Subtype.ext (Subtype.ext ?_)
  have h : GeneralLinearGroup.map (pInf E) g.1.1 = 1 := g.2
  rw [infPart_val, h, map_one]
  rfl

theorem dense_rat_inf : Dense {k : infU E n | ∃ γ ∈ ratU E n, cInf k.1 = cInf γ} := by
  intro k
  rw [← infPart_inf k]
  refine closure_mono ?_ (image_closure_subset_closure_image continuous_infPart
    ⟨k.1, GlobalTheory.WeightRealExt.dense_rat_fin k.1, rfl⟩)
  rintro _ ⟨_, ⟨γ, hγ, g, hg, rfl⟩, rfl⟩
  refine ⟨γ, hγ, ?_⟩
  have hg' : cInf g = 1 := hg
  rw [cInf_infPart, map_mul, hg', mul_one]

theorem dense_and_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), Dense ((ratU E n : Set (UA E n)) * (finU (E := E) (n := n) : Set (UA E n))) ∧ Dense {k : infU E n | ∃ γ ∈ ratU E n, cInf k.1 = cInf γ} ∧ (∀ k : infU E n, ∀ g ∈ finU (E := E) (n := n), k.1 * g = g * k.1) ∧ ∃ (a : UA E n →* finU (E := E) (n := n)) (b : UA E n →* infU E n), Continuous a ∧ Continuous b ∧ (∀ x, x = (a x).1 * (b x).1) ∧ ∀ (g : finU (E := E) (n := n)) (k : infU E n), a (g.1 * k.1) = g ∧ b (g.1 * k.1) = k := by
  intro E _ _ _ n
  refine ⟨GlobalTheory.WeightRealExt.dense_rat_fin, dense_rat_inf, fun k g hg => (GlobalTheory.DefU.fin_mul_inf hg k.2).symm,
    finPart, infPart, continuous_finPart, continuous_infPart, finPart_mul_infPart, fun g k => ⟨?_, ?_⟩⟩
  · rw [map_mul, finPart_fin, finPart_inf, mul_one]
  · rw [map_mul, infPart_fin, infPart_inf, one_mul]

end GlobalTheory.UnitarySplit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DefiniteUnitaryRealApproxAndFiniteInfiniteSplitStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitary_realApprox_and_finite_infinite_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), Dense ((ratU E n : Set (UA E n)) * (finU (E := E) (n := n) : Set (UA E n))) ∧ Dense {k : infU E n | ∃ γ ∈ ratU E n, cInf k.1 = cInf γ} ∧ (∀ k : infU E n, ∀ g ∈ finU (E := E) (n := n), k.1 * g = g * k.1) ∧ ∃ (a : UA E n →* finU (E := E) (n := n)) (b : UA E n →* infU E n), Continuous a ∧ Continuous b ∧ (∀ x, x = (a x).1 * (b x).1) ∧ ∀ (g : finU (E := E) (n := n)) (k : infU E n), a (g.1 * k.1) = g ∧ b (g.1 * k.1) = k := by
  first | exact @GlobalTheory.UnitarySplit.dense_and_split | exact GlobalTheory.UnitarySplit.dense_and_split | (intros; apply GlobalTheory.UnitarySplit.dense_and_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassCountBoundParamsLambdaConstructedPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberClosed
namespace GlobalTheory.ColClassNumber

open Formalism.MainNotions

theorem classNumber_closed (𝒞 : FamClass) :
    Closed 𝒞 fun Fm _ => ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), StandardLattice.ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun Fm _ _ _ x hx i => classNumber_all (Fm.D x i) (Fm.ex x hx i).lev⟩⟩

end GlobalTheory.ColClassNumber
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScaleOneLeA
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory

theorem scale_one_le_a (s : Scale) : 1 ≤ s.a := by
  have hx : 1 < s.x := s.one_lt_alt
  have hL : 0 ≤ s.L := by
    unfold Scale.L
    exact Real.rpow_nonneg (by linarith) _
  have hb : 1 ≤ s.b := by
    unfold Scale.b
    exact Real.one_le_exp hL
  unfold Scale.a
  exact one_le_mul_of_one_le_of_one_le hx.le hb

theorem famP_La_nonneg : ∀ (eps : ℝ) (Fm : FamP eps), ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x,
    0 ≤ (Fm.L x i).La := by
  intro eps Fm x hx i
  obtain ⟨-, -, -, -, -, -, hQD, -⟩ := Fm.sizes x hx i
  obtain ⟨-, -, -, -, -, -, hrd, -⟩ := hQD
  unfold SizeData₂.La
  exact Real.log_nonneg (one_le_mul_of_one_le_of_one_le (scale_one_le_a _) hrd)

end GlobalTheory
end

namespace GlobalTheory.Fc.R0

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem.Top GlobalTheory.Fc

theorem h_la_all (𝒜 : FamClass) : H_la 𝒜 :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun Fm _ _ _ => ⟨Fm.x1 + 1, fun x hx i => GlobalTheory.famP_La_nonneg _ Fm x (by linarith) i⟩⟩⟩

theorem classCountBound_all_classes (𝒜 : FamClass) : ClassCountBoundAllPoints 𝒜 :=
  GlobalTheory.ColClassNumber.classNumber_closed (W1 𝒜)

theorem classCountBound_paramsLambda_constructedPoints : ∀ (Bd : BdT) (Q : V4.Slot) (Lk : LkT Bd), R0.ClassCountBoundAtConstructedPoints Q Lk ∧ R0.LambdaConditionAtConstructedPoints Q Lk := by
  intro Bd Q Lk
  refine ⟨?_, ?_⟩
  · apply Row.of_sel
    intros
    exact classCountBound_all_classes _
  · apply Row.of_sel
    intros
    exact h_la_all _

end GlobalTheory.Fc.R0
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowHInstROfHU
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolumeSignatureIndepAndClassNumberItems
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianClassNumberItemsAllRanks
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberFiniteAndGenusMass
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumInvCardStabEq
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeightedDoubleCoset

def stabConjEquiv {G : Type} [Group G] (Γ K : Subgroup G) (g : G) (γ₀ : Γ) (k : K) :
    Unfold.stab Γ K ((γ₀ : G) * g * k) ≃ Unfold.stab Γ K g where
  toFun δ := ⟨γ₀⁻¹ * δ.1 * γ₀, by
    have h := K.mul_mem (K.mul_mem k.2 δ.2) (K.inv_mem k.2)
    simp only [Unfold.stab, Set.mem_setOf_eq, Subgroup.coe_mul, Subgroup.coe_inv] at h ⊢
    convert h using 1; group⟩
  invFun δ := ⟨γ₀ * δ.1 * γ₀⁻¹, by
    have h := K.mul_mem (K.mul_mem (K.inv_mem k.2) δ.2) k.2
    simp only [Unfold.stab, Set.mem_setOf_eq, Subgroup.coe_mul, Subgroup.coe_inv] at h ⊢
    convert h using 1; group⟩
  left_inv δ := by ext; simp [mul_assoc]
  right_inv δ := by ext; simp [mul_assoc]

theorem card_stab_eq {G : Type} [Group G] (Γ K : Subgroup G) (g : G) (γ₀ : Γ) (k : K) :
    Nat.card (Unfold.stab Γ K ((γ₀ : G) * g * k)) = Nat.card (Unfold.stab Γ K g) :=
  Nat.card_congr (stabConjEquiv Γ K g γ₀ k)

theorem sum_inv_card_stab_eq : ∀ (G : Type) [Group G] (Γ K : Subgroup G) (n m : ℕ) (g : Fin n → G) (g' : Fin m → G), (∀ x : G, ∃ i, ∃ γ : Γ, ∃ k : K, x = (γ : G) * g i * k) → (∀ i j (γ γ' : Γ) (k k' : K), (γ : G) * g i * k = (γ' : G) * g j * k' → i = j) → (∀ x : G, ∃ i, ∃ γ : Γ, ∃ k : K, x = (γ : G) * g' i * k) → (∀ i j (γ γ' : Γ) (k k' : K), (γ : G) * g' i * k = (γ' : G) * g' j * k' → i = j) → ∑ i, ((Nat.card (Unfold.stab Γ K (g i)) : ℝ))⁻¹ = ∑ j, ((Nat.card (Unfold.stab Γ K (g' j)) : ℝ))⁻¹ := by
  intro G _ Γ K n m g g' hcov hdisj hcov' hdisj'
  choose e γe ke he using fun i => hcov' (g i)
  choose f γf kf hf using fun j => hcov (g' j)
  have hfe : ∀ i, f (e i) = i := by
    intro i
    symm
    refine hdisj i (f (e i)) 1 (γe i * γf (e i)) 1 (kf (e i) * ke i) ?_
    have h1 := he i
    rw [hf (e i)] at h1
    simp only [OneMemClass.coe_one, one_mul, mul_one, Subgroup.coe_mul]
    simpa only [mul_assoc] using h1
  have hef : ∀ j, e (f j) = j := by
    intro j
    symm
    refine hdisj' j (e (f j)) 1 (γf j * γe (f j)) 1 (ke (f j) * kf j) ?_
    have h1 := hf j
    rw [he (f j)] at h1
    simp only [OneMemClass.coe_one, one_mul, mul_one, Subgroup.coe_mul]
    simpa only [mul_assoc] using h1
  let σ : Fin n ≃ Fin m := ⟨e, f, hfe, hef⟩
  refine Fintype.sum_equiv σ _ _ (fun i => ?_)
  show ((Nat.card (Unfold.stab Γ K (g i)) : ℝ))⁻¹ = ((Nat.card (Unfold.stab Γ K (g' (e i))) : ℝ))⁻¹
  rw [he i, card_stab_eq]

end GlobalTheory.WeightedDoubleCoset
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberFiniteAndGenusMass
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClassNumberMass

theorem classFin_and_classMass : ∀ D : D7, ClassFin D ∧ ClassMass D := by
  intro D
  refine ⟨fun W hW hsig => ?_, fun W hW hsig n g hcov hdisj => ?_⟩
  · obtain ⟨n, g, hcov, hdisj, _⟩ := GlobalTheory.T.lattice_stabilizer_doubleCosets_classRest_mass D W hW hsig
    exact ⟨n, g, hcov, hdisj⟩
  · obtain ⟨m, g', hcov', hdisj', hsum⟩ := GlobalTheory.T.lattice_stabilizer_doubleCosets_classRest_mass D W hW hsig
    rw [← hsum]
    exact GlobalTheory.WeightedDoubleCoset.sum_inv_card_stab_eq _ _ _ n m g g' hcov hdisj hcov' hdisj'

end GlobalTheory.ClassNumberMass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberFiniteAndGenusMassStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classNumber_finite_and_genusMass : ∀ D : D7, ClassFin D ∧ ClassMass D := by
  first | exact @GlobalTheory.ClassNumberMass.classFin_and_classMass | exact GlobalTheory.ClassNumberMass.classFin_and_classMass | (intros; apply GlobalTheory.ClassNumberMass.classFin_and_classMass <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianClassNumberItemsAllRanks
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem classItemsAt_all : ∀ (D : D7) (n : ℕ), ClassItemsAt D n := fun D n =>
  have h := GlobalTheory.T.classNumber_finite_and_genusMass D
  ⟨genusMassAt_of D (GlobalTheory.genusMassStd_all D) n, classFinAt_of D h.1 n, classMassAt_of D h.2 n⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianClassNumberItemsAllRanksStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianClassNumberItems_all_ranks : ∀ (D : D7) (n : ℕ), ClassItemsAt D n := by
  first | exact @GlobalTheory.classItemsAt_all | exact GlobalTheory.classItemsAt_all | (intros; apply GlobalTheory.classItemsAt_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolumeSignatureIndepAndClassNumberItems
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Glob

theorem volSigIndep_and_classItemsAt_of_massRatioUnderVolume (hU : ∀ D : D7, Formalism.MainNotions.RT.MassRatioUnderVolume D) :
    ∀ D : D7, VolSigIndep D ∧ ClassItemsAt D (D.sp.Y 0).rank := by
  intro D
  refine ⟨?_, GlobalTheory.T.hermitianClassNumberItems_all_ranks D _⟩
  have key := GlobalTheory.T.adelicQuotientVolume_eq_of_signature_rank_indep (fun D hT W W₀ P Q P₀ Q₀ hW hW₀ hs hs₀ hr => by
    have h2 : Conclusion2 D := volumeMass_of_unfolding D (hU D hT)
    rw [GlobalTheory.T.unitary_volume_eq_rank_mass_all_signatures D hT h2 W P Q hW hs, GlobalTheory.T.unitary_volume_eq_rank_mass_all_signatures D hT h2 W₀ P₀ Q₀ hW₀ hs₀]
    have e1 := Formalism.BasicNotions.sig_sum W hW D.host.φ₀
    have e2 := Formalism.BasicNotions.sig_sum W₀ hW₀ D.host.φ₀
    rw [hs] at e1
    rw [hs₀] at e2
    simp only at e1 e2
    rw [e1, e2, hr])
  exact key D

end GlobalTheory.Glob
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolumeSignatureIndepAndClassNumberItemsStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_signature_indep_and_classNumberItems : (∀ D : D7, Formalism.MainNotions.RT.MassRatioUnderVolume D) → ∀ D : D7, VolSigIndep D ∧ ClassItemsAt D (D.sp.Y 0).rank := by
  first | exact @GlobalTheory.Glob.volSigIndep_and_classItemsAt_of_massRatioUnderVolume | exact GlobalTheory.Glob.volSigIndep_and_classItemsAt_of_massRatioUnderVolume | (intros; apply GlobalTheory.Glob.volSigIndep_and_classItemsAt_of_massRatioUnderVolume <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory

theorem row_hInstR_of_hU (hU : ∀ D : D7, MassRatioUnderVolume D) : ∀ (Bd : BdT) (Q : V4.Slot) (Lk : LkT Bd), ClassTwoEntries.InstanceRankAtConstructedPoints Q Lk :=
  fun _ Q Lk => Row0.row (Row0.of_all (Q := Q) fun _ => by
    intro eps Fm _ x _ i
    exact GlobalTheory.T.volume_signature_indep_and_classNumberItems hU (Fm.D x i)) Lk

end GlobalTheory
end
