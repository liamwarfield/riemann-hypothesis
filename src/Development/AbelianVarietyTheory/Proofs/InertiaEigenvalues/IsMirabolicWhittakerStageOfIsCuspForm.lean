module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeDefiniteOfCmDatumRecLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeLaterClausesHold
public import Formalism.LocalToGlobal.IndefiniteReal.SmExpSmulContDiff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLatticeIdempotentPositionInvolutionStable
public import Formalism.SharpRestriction.LevelLetterCocycles.SaturationPullbackOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorLevelsUnramifiedStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.WachFrobeniusLatticeUnramifiedFunctor
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangeEveryTheory

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageOfIsCuspForm
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageOfIsCuspForm
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def blkIxEquiv (r : ℕ) : UnipotentBlockColumnIndex a r (a - 1) ≃ BlockIx a r where
  toFun p := ⟨p.1, p.2.1, p.2.2.1⟩
  invFun p := ⟨p.1, p.2.1, p.2.2, by have := p.1.2.isLt; omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem blkU_comp_equiv {R : Type} [CommRing R] (r : ℕ) (x : BlockIx a r → R) :
    blkU (fun t => x (blkIxEquiv r t)) = unip x := by
  apply Units.ext
  change 1 + posM Subtype.val (fun t => x (blkIxEquiv r t)) = 1 + nilM x
  congr 1
  have e1 : posM Subtype.val (fun t => x (blkIxEquiv r t)) =
      ∑ s : BlockIx a r, Matrix.single s.1.1 s.1.2 (x s) :=
    Equiv.sum_comp (blkIxEquiv r) (fun s : BlockIx a r => Matrix.single s.1.1 s.1.2 (x s))
  rw [e1]
  ext i j
  simp only [Matrix.sum_apply, Matrix.single_apply, nilM, Matrix.of_apply]
  split_ifs with h
  · rw [Fintype.sum_eq_single ⟨(i, j), h⟩]
    · simp
    · intro s hs
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hs (Subtype.ext (Prod.ext h1 h2))
  · refine Finset.sum_eq_zero fun s _ => if_neg ?_
    rintro ⟨h1, h2⟩
    apply h
    rw [← h1, ← h2]
    exact s.2

def blkIxHomeo (r : ℕ) : (BlockIx a r → Ad E) ≃ₜ+ (UnipotentBlockColumnIndex a r (a - 1) → Ad E) where
  toFun x t := x (blkIxEquiv r t)
  invFun y s := y ((blkIxEquiv r).symm s)
  left_inv x := funext fun s => by simp
  right_inv y := funext fun t => by simp
  map_add' _ _ := rfl
  continuous_toFun := continuous_pi fun t => continuous_apply _
  continuous_invFun := continuous_pi fun s => continuous_apply _

theorem blkIxHomeo_mem (r : ℕ) (x : BlockIx a r → Ad E) :
    blkIxHomeo r x ∈ ratV E (UnipotentBlockColumnIndex a r (a - 1)) ↔ x ∈ ratN E a r := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun s => c ((blkIxEquiv r).symm s), funext fun s => ?_⟩
    have := congrFun hc ((blkIxEquiv r).symm s)
    simpa [blkIxHomeo] using this
  · rintro ⟨c, rfl⟩
    exact ⟨fun t => c (blkIxEquiv r t), rfl⟩

theorem good_of_isCuspForm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (ψ : AddChar (Ad E) ℂ) (φ : Sm E a), IsCuspForm φ → Good ψ (a - 1) φ.1 := by
  intro E _ _ _ a ψ φ h
  have hcont : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ h.1.level
  refine ⟨hcont, fun γ _ g => h.1.left γ g, ?_, ?_⟩
  · intro k hk y g
    have he : IsEmpty (UnipotentBlockColumnIndex a k k) := ⟨fun t => by have := t.1.2.isLt; have := t.2; omega⟩
    have hy : y = 0 := Subsingleton.elim _ _
    subst hy
    have hd : dot (eLast a k) (0 : UnipotentBlockColumnIndex a k k → Ad E) = 0 := by simp [dot]
    rw [hd, AddChar.map_zero_eq_one, one_mul]
    unfold blkU
    rw [posU_zero, one_mul]
  · intro r hr hra g
    have hra' : r < a := by omega
    have hper := per_blk (E := E) (r := r) (m := a - 1) hcont (fun c g => h.1.left _ g) g
    have hper2 : Per (ratN E a r) (fun x => φ.1 (blkU (blkIxHomeo r x) * g)) :=
      ⟨hper.1.comp (blkIxHomeo r).continuous, fun γ hγ x => by
        simp only [map_add (f := _)]
        exact hper.2 _ ((blkIxHomeo_mem r γ).2 hγ) _⟩
    have key := GlobalTheory.T.quotientAverage_map_lattice_equiv _ _ (ratN E a r) (ratV E _) (isCoLat_ratV E (BlockIx a r))
      (isCoLat_ratV E _) (blkIxHomeo r) (blkIxHomeo_mem r) _ hper
    rw [← key]
    have hfun : (fun x => φ.1 (blkU (blkIxHomeo r x) * g)) = fun x => φ.1 (unip x * g) :=
      funext fun x => by rw [← blkU_comp_equiv]; rfl
    rw [hfun] at hper2 ⊢
    letI : MeasurableSpace (BlockIx a r → Ad E) := borel _
    haveI : BorelSpace (BlockIx a r → Ad E) := ⟨rfl⟩
    obtain ⟨μ, 𝓕, hμ, hF, h1⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice _ (ratN E a r) (isCoLat_ratV E (BlockIx a r))
    obtain ⟨-, -, -, hint⟩ := GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average _ _ (isCoLat_ratV E (BlockIx a r)) μ 𝓕 hμ hF _ hper2
    have hc := h.2 r hr hra' μ 𝓕 hμ hF g
    rw [hint, h1] at hc
    simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at hc
    exact hc

end GlobalTheory.CuspGeneric
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageOfIsCuspFormStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ψ : AddChar (Ad E) ℂ) (φ : Sm E a), IsCuspForm φ → Good ψ (a - 1) φ.1 := by
  first | exact @GlobalTheory.CuspGeneric.good_of_isCuspForm | exact GlobalTheory.CuspGeneric.good_of_isCuspForm | (intros; apply GlobalTheory.CuspGeneric.good_of_isCuspForm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleLocalConclusionsUsedForms
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleLocalConclusionsUsedForms
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.NL

theorem usedLocalConclusion_and_prvE : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), DeltaInvariantLattices.UsedLocalConclusion D HW F Cm ∧ DeltaInvariantLattices.ConclusionE D HW F := by
  intro D HW F Cm
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, c2, a, b, c, d, l3, hE⟩ := GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm
  refine ⟨⟨fun l _ K s LL g => ⟨p1 l K s LL g, p2 l K s LL g, p3 l K s LL g, p4 l K s LL g, p5 l K s LL g,
    p6 l K s LL g, p7 l K s LL g, p8 l K s LL g, p9 l K s LL g, p10 l K s LL g⟩, c2,
    (DeltaInvariantLattices.herr_prop_two_iff D HW F).2 ⟨a, b, c, d⟩, l3⟩, hE⟩

end GlobalTheory.NL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleLocalConclusionsUsedFormsStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachModuleLocalConclusions_usedForms : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), DeltaInvariantLattices.UsedLocalConclusion D HW F Cm ∧ DeltaInvariantLattices.ConclusionE D HW F := by
  first | exact @GlobalTheory.NL.usedLocalConclusion_and_prvE | exact GlobalTheory.NL.usedLocalConclusion_and_prvE | (intros; apply GlobalTheory.NL.usedLocalConclusion_and_prvE <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteRationalConjMemBoundedCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteRationalConjMemBoundedCompact
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

open scoped TensorProduct

namespace GlobalTheory.StabFin

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem norm_entry_le_one {g : GL (Fin n) L} (hg : g ∈ GQ0 L n) (φ : L →+* ℂ) (i j : Fin n) :
    ‖φ ((g : Matrix (Fin n) (Fin n) L) i j)‖ ≤ 1 := by
  have h0 : (g : Matrix (Fin n) (Fin n) L) * conjT (IsCMField.complexConj L : L →+* L) g = 1 := hg
  have h1 := congrFun (congrFun h0 i) i
  simp only [Matrix.mul_apply, conjT, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply_eq] at h1
  have h2 := congrArg φ h1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_one] at h2
  have h3 : ∑ k, ((‖φ ((g : Matrix (Fin n) (Fin n) L) i k)‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h2]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := IsCMField.complexEmbedding_complexConj L φ ((g : Matrix (Fin n) (Fin n) L) i k)
    rw [show ((IsCMField.complexConj L : L →+* L) ((g : Matrix (Fin n) (Fin n) L) i k)) =
      IsCMField.complexConj L ((g : Matrix (Fin n) (Fin n) L) i k) from rfl, this, Complex.mul_conj', Complex.ofReal_pow]
  have h4 : ∑ k, ‖φ ((g : Matrix (Fin n) (Fin n) L) i k)‖ ^ 2 = 1 := by exact_mod_cast h3
  have h5 : ‖φ ((g : Matrix (Fin n) (Fin n) L) i j)‖ ^ 2 ≤ 1 := by
    rw [← h4]
    exact Finset.single_le_sum (f := fun k => ‖φ ((g : Matrix (Fin n) (Fin n) L) i k)‖ ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  nlinarith [norm_nonneg (φ ((g : Matrix (Fin n) (Fin n) L) i j))]

theorem exists_common_denom {ι : Type} [Fintype ι] (x : ι → AL L) :
    ∃ D : ℕ, 0 < D ∧ ∀ a, (D : AL L) * x a ∈ ALint L := by
  classical
  choose d hd0 hd using fun a => Formalism.IndefR.principalLevelFrame.cong_nat_denom (x a)
  refine ⟨∏ a, d a, Finset.prod_pos fun a _ => hd0 a, fun a => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), Nat.cast_mul, mul_comm ((d a : ℕ) : AL L), mul_assoc]
  exact Subring.mul_mem _ (natCast_mem _ _) (hd a)

theorem exists_rat (γ : GQ L n) : ∃ g : GL (Fin n) L, g ∈ GQ0 L n ∧
    ∀ i j, (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j =
      ((g : Matrix (Fin n) (Fin n) L) i j) ⊗ₜ[NumberField.maximalRealSubfield L] (1 : AFplus L) := by
  have h : ((γ : GAf L n) : GL (Fin n) (AL L)) ∈ (GQ0 L n).map (Matrix.GeneralLinearGroup.map
      (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L)) := Subgroup.mem_subgroupOf.1 γ.2
  obtain ⟨g, hg, he⟩ := Subgroup.mem_map.1 h
  refine ⟨g, hg, fun i j => ?_⟩
  rw [← he]
  rfl

theorem isIntegral_of_mem (z : L) (hz : z ⊗ₜ[NumberField.maximalRealSubfield L] (1 : AFplus L) ∈ ALint L) :
    IsIntegral ℤ z := by
  have hle : ALint L ≤ Formalism.MainNotions.S.IntAf (NumberField.maximalRealSubfield L) L := by
    rw [ReciprocityTheory.Aut.ALint, Subring.closure_le]
    rintro x (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨⟨(y : L), y, rfl⟩, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  exact Formalism.UG.P.csGlob_int (F := NumberField.maximalRealSubfield L) z (hle hz)

end GlobalTheory.StabFin

open scoped TensorProduct

namespace GlobalTheory.StabFin

theorem finite_conj_mem : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J : Subgroup (GAf L n)),
    IsBounded J → ∀ t : GAf L n, Finite {γ : GQ L n // t⁻¹ * (γ : GAf L n) * t ∈ J} := by
  intro L _ _ _ n J hJ t
  classical
  obtain ⟨F, hF⟩ := hJ
  let M : GAf L n → Matrix (Fin n) (Fin n) (AL L) := fun a => ((a : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))
  obtain ⟨D, hD0, hD⟩ := exists_common_denom (L := L) (ι := (F × Fin n × Fin n) ⊕ (Fin n × Fin n))
    (fun a => match a with
      | .inl ⟨f, i, k⟩ => M (t * f) i k
      | .inr ⟨l, j⟩ => M t⁻¹ l j)
  have key : ∀ γ : GQ L n, t⁻¹ * (γ : GAf L n) * t ∈ J → ∀ i j, ((D : AL L) * D) * M γ i j ∈ ALint L := by
    intro γ hγ i j
    obtain ⟨f, hf, hu⟩ := hF _ hγ
    have hu' : ∀ a b, M (f⁻¹ * (t⁻¹ * (γ : GAf L n) * t)) a b ∈ ALint L := hu
    have e : (γ : GAf L n) = (t * f) * (f⁻¹ * (t⁻¹ * (γ : GAf L n) * t)) * t⁻¹ := by group
    have eM : M γ = M (t * f) * M (f⁻¹ * (t⁻¹ * (γ : GAf L n) * t)) * M t⁻¹ := by
      conv_lhs => rw [e]
      simp only [M, Subgroup.coe_mul, Units.val_mul]
    rw [eM, Matrix.mul_apply, Finset.mul_sum]
    refine Subring.sum_mem _ fun l _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine Subring.sum_mem _ fun k _ => ?_
    have e2 : ((D : AL L) * D) * (M (t * f) i k * M (f⁻¹ * (t⁻¹ * (γ : GAf L n) * t)) k l * M t⁻¹ l j) =
        ((D : AL L) * M (t * f) i k) * M (f⁻¹ * (t⁻¹ * (γ : GAf L n) * t)) k l * ((D : AL L) * M t⁻¹ l j) := by ring
    rw [e2]
    exact Subring.mul_mem _ (Subring.mul_mem _ (hD (.inl ⟨⟨f, hf⟩, i, k⟩)) (hu' k l)) (hD (.inr ⟨l, j⟩))
  set T : Set L := {z : L | IsIntegral ℤ z ∧ ∀ φ : L →+* ℂ, ‖φ z‖ ≤ ((D * D : ℕ) : ℝ)} with hT
  have hTfin : T.Finite := NumberField.Embeddings.finite_of_norm_le L ℂ _
  have : Finite T := hTfin.to_subtype
  choose gs hgs0 hgs using exists_rat (L := L) (n := n)
  have hmem : ∀ x : {γ : GQ L n // t⁻¹ * (γ : GAf L n) * t ∈ J}, ∀ i j,
      ((D * D : ℕ) : L) * (gs x.1 : Matrix (Fin n) (Fin n) L) i j ∈ T := by
    intro x i j
    refine ⟨isIntegral_of_mem _ ?_, fun φ => ?_⟩
    · have e : (((D * D : ℕ) : L) * (gs x.1 : Matrix (Fin n) (Fin n) L) i j) ⊗ₜ[NumberField.maximalRealSubfield L] (1 : AFplus L) =
          ((D : AL L) * D) * M x.1 i j := by
        simp only [M]
        rw [hgs, ← Algebra.TensorProduct.includeLeftRingHom_apply, ← Algebra.TensorProduct.includeLeftRingHom_apply,
          map_mul, map_natCast]
        push_cast; ring
      rw [e]
      exact key x.1 x.2 i j
    · rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) (norm_entry_le_one (hgs0 x.1) φ i j)
  refine Finite.of_injective (fun x => fun i j => (⟨_, hmem x i j⟩ : T)) ?_
  intro x y hxy
  have hD' : ((D * D : ℕ) : L) ≠ 0 := by exact_mod_cast (Nat.mul_pos hD0 hD0).ne'
  have hg : ∀ i j, (gs x.1 : Matrix (Fin n) (Fin n) L) i j = (gs y.1 : Matrix (Fin n) (Fin n) L) i j := by
    intro i j
    have := congrArg Subtype.val (congrFun (congrFun hxy i) j)
    exact mul_left_cancel₀ hD' this
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [hgs x.1 i j, hgs y.1 i j, hg i j]

end GlobalTheory.StabFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteRationalConjMemBoundedCompactStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_rational_conj_mem_boundedCompact : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J : Subgroup (GAf L n)), IsBounded J → ∀ t : GAf L n, Finite {γ : GQ L n // t⁻¹ * (γ : GAf L n) * t ∈ J} := by
  first | exact @GlobalTheory.StabFin.finite_conj_mem | exact GlobalTheory.StabFin.finite_conj_mem | (intros; apply GlobalTheory.StabFin.finite_conj_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalAbsorptionLengthBoundOfBlochKato
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalAbsorptionLengthBoundOfBlochKato
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.ClosingStatement

theorem main : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      BlochKatoDuality.Conclusion1 D ∧ BlochKatoDuality.Conclusion2 D := by
  intro hBK hTD hEC D _ _ _
  have h5 : Formalism.MainNotions.LocalSituation.Conclusion5 D := GlobalTheory.T.blochKatoLocal_all_of_tateDuality_eulerChar hBK hTD hEC D
  have a1 : BlochKatoDuality.adm1 D := dimension_input_one_of_bloch_kato D h5
  have a2 : BlochKatoDuality.adm2 D := dimension_input_two_of_bloch_kato D h5
  have a3 : BlochKatoDuality.adm3 D := fun l _ K => GlobalTheory.T.tate_H2_period_datum hTD l (D.loc l) K
  have a5 : BlochKatoDuality.adm5 D := fun l _ K => GlobalTheory.T.finite_H1_period_datum hTD l (D.loc l) K
  have a6 : BlochKatoDuality.adm6 D := fun l _ K => (GlobalTheory.T.tateDual_deRham_and_filZero_dim_all D l K).1
  exact ⟨BlochKatoDuality.ramification_two_and_conjugation_at_q_and_d D a1 a2 a6, BlochKatoDuality.second_proposition_every_localisation D a1 a2 a3 a5 a6⟩

end GlobalTheory.ClosingStatement
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalAbsorptionLengthBoundOfBlochKatoStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_absorption_length_bound_of_blochKato : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), BlochKatoDuality.Conclusion1 D ∧ BlochKatoDuality.Conclusion2 D := by
  first | exact @GlobalTheory.ClosingStatement.main | exact GlobalTheory.ClosingStatement.main | (intros; apply GlobalTheory.ClosingStatement.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerCoefficientRationalMirabolicMul
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerCoefficientRationalMirabolicMul
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

namespace MirCol

section ColAct

variable {R : Type} [CommRing R] {a k : ℕ}

def colAct (M : Matrix (Fin a) (Fin a) R) (x : UnipotentBlockColumnIndex a k k → R) : UnipotentBlockColumnIndex a k k → R :=
  fun t => ∑ s, M t.1.1 s.1.1 * x s

theorem posM_col_apply (x : UnipotentBlockColumnIndex a k k → R) (t : UnipotentBlockColumnIndex a k k) :
    posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) x t.1.1 t.1.2 = x t := by
  simp only [posM, Matrix.sum_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single t]
  · simp
  · intro s _ hne
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hne (Subtype.ext (Prod.ext h1 h2))
  · simp

theorem posM_col_mul (M : Matrix (Fin a) (Fin a) R)
    (hM : ∀ i l : Fin a, k ≤ (i : ℕ) → M i l = (1 : Matrix (Fin a) (Fin a) R) i l) (x : UnipotentBlockColumnIndex a k k → R) :
    posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) x * M = posM Subtype.val x := by
  simp only [posM, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single t.1.2]
  · rw [hM _ _ t.2.2.1]
    simp only [Matrix.single_apply, Matrix.one_apply]
    by_cases h1 : t.1.1 = i <;> by_cases h2 : t.1.2 = j <;> simp [h1, h2]
  · intro l _ hl
    rw [Matrix.single_apply, if_neg (fun h => hl h.2.symm), zero_mul]
  · simp

theorem mul_posM_col (M : Matrix (Fin a) (Fin a) R)
    (hM : ∀ i l : Fin a, k ≤ (i : ℕ) → M i l = (1 : Matrix (Fin a) (Fin a) R) i l) (x : UnipotentBlockColumnIndex a k k → R) :
    M * posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) x = posM Subtype.val (colAct M x) := by
  ext i j
  have hL : (M * posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) x) i j =
      ∑ s : UnipotentBlockColumnIndex a k k, if s.1.2 = j then M i s.1.1 * x s else 0 := by
    simp only [Matrix.mul_apply, posM, Matrix.sum_apply, Matrix.single_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_eq_single s.1.1]
    · simp
    · intro l _ hl
      rw [if_neg (fun h => hl h.1.symm), mul_zero]
    · simp
  rw [hL]
  simp only [posM, Matrix.sum_apply, Matrix.single_apply]
  by_cases hi : (i : ℕ) < k
  · by_cases hj : (j : ℕ) = k
    · symm
      rw [Finset.sum_eq_single (⟨(i, j), hi, hj.ge, hj.le⟩ : UnipotentBlockColumnIndex a k k)]
      · rw [if_pos (And.intro rfl rfl)]
        simp only [colAct]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [if_pos]
        have h1 := s.2.2
        exact Fin.ext (by omega)
      · intro t _ hne
        rw [if_neg]
        rintro ⟨h1, h2⟩
        exact hne (Subtype.ext (Prod.ext h1 h2))
      · simp
    · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
      · intro t _
        rw [if_neg]
        rintro ⟨_, h2⟩
        have h1 := t.2.2
        rw [← h2] at hj
        omega
      · intro t _
        rw [if_neg]
        intro h2
        have h1 := t.2.2
        rw [← h2] at hj
        omega
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro t _
      rw [if_neg]
      rintro ⟨h1, _⟩
      have h2 := t.2.1
      rw [h1] at h2
      exact hi h2
    · intro s _
      have h2 := s.2.1
      rw [hM i _ (by omega), Matrix.one_apply_ne (fun h => by rw [h] at hi; exact hi h2)]
      simp

theorem colAct_colAct {M N : Matrix (Fin a) (Fin a) R}
    (hM : ∀ i l : Fin a, k ≤ (i : ℕ) → M i l = (1 : Matrix (Fin a) (Fin a) R) i l)
    (hN : ∀ i l : Fin a, k ≤ (i : ℕ) → N i l = (1 : Matrix (Fin a) (Fin a) R) i l)
    (h : M * N = 1) (x : UnipotentBlockColumnIndex a k k → R) : colAct M (colAct N x) = x := by
  funext t
  rw [← posM_col_apply (colAct M (colAct N x)) t, ← mul_posM_col M hM, ← mul_posM_col N hN, ← Matrix.mul_assoc, h,
    Matrix.one_mul, posM_col_apply]

theorem inv_rows (γ : GL (Fin a) R)
    (hγ : ∀ i l : Fin a, k ≤ (i : ℕ) → γ.val i l = (1 : Matrix (Fin a) (Fin a) R) i l) :
    ∀ i l : Fin a, k ≤ (i : ℕ) → (γ⁻¹).val i l = (1 : Matrix (Fin a) (Fin a) R) i l := by
  intro i l hi
  have h : γ.val * (γ⁻¹).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 := congrFun (congrFun h i) l
  rw [Matrix.mul_apply] at h2
  simp only [hγ i _ hi, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h2
  simpa [Matrix.one_apply] using h2

theorem blkU_mul (γ : GL (Fin a) R)
    (hγ : ∀ i l : Fin a, k ≤ (i : ℕ) → γ.val i l = (1 : Matrix (Fin a) (Fin a) R) i l) (x : UnipotentBlockColumnIndex a k k → R) :
    blkU x * γ = γ * blkU (colAct (γ⁻¹).val x) := by
  apply Units.ext
  change (1 + posM Subtype.val x) * γ.val = γ.val * (1 + posM Subtype.val (colAct (γ⁻¹).val x))
  have h : γ.val * (γ⁻¹).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [← mul_posM_col _ (inv_rows γ hγ), add_mul, mul_add, posM_col_mul _ hγ, ← Matrix.mul_assoc, h]
  simp

end ColAct

section Rat

variable {E : Type} [Field E] [NumberField E] {a k : ℕ}

theorem ratGL_val_apply (γ : GL (Fin a) E) (i l : Fin a) :
    (ratGL E a γ).val i l = algebraMap E (Ad E) (γ.val i l) := rfl

theorem ratGL_rows (γ : GL (Fin a) E)
    (hγ : ∀ i l : Fin a, k ≤ (i : ℕ) → γ.val i l = (1 : Matrix (Fin a) (Fin a) E) i l) :
    ∀ i l : Fin a, k ≤ (i : ℕ) → (ratGL E a γ).val i l = (1 : Matrix (Fin a) (Fin a) (Ad E)) i l := by
  intro i l hi
  rw [ratGL_val_apply, hγ i l hi, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem colAct_rat (γ : GL (Fin a) E) (c : UnipotentBlockColumnIndex a k k → E) :
    colAct (ratGL E a γ).val (fun t => algebraMap E (Ad E) (c t)) =
      fun t => algebraMap E (Ad E) (colAct γ.val c t) := by
  funext t
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [colAct, ratGL_val_apply, map_sum, map_mul]

theorem continuous_colAct (M : Matrix (Fin a) (Fin a) (Ad E)) :
    Continuous (colAct M : (UnipotentBlockColumnIndex a k k → Ad E) → UnipotentBlockColumnIndex a k k → Ad E) :=
  continuous_pi fun _ => continuous_finsetSum _ fun s _ => continuous_const.mul (continuous_apply s)

def colEquiv (γ : GL (Fin a) E)
    (hγ : ∀ i l : Fin a, k ≤ (i : ℕ) → γ.val i l = (1 : Matrix (Fin a) (Fin a) E) i l) :
    (UnipotentBlockColumnIndex a k k → Ad E) ≃ₜ+ (UnipotentBlockColumnIndex a k k → Ad E) where
  toFun := colAct (ratGL E a γ).val
  invFun := colAct (ratGL E a γ⁻¹).val
  left_inv x := colAct_colAct (ratGL_rows _ (inv_rows γ hγ)) (ratGL_rows _ hγ)
    (by rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]) x
  right_inv x := colAct_colAct (ratGL_rows _ hγ) (ratGL_rows _ (inv_rows γ hγ))
    (by rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]) x
  map_add' x y := by
    funext t
    simp only [colAct, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  continuous_toFun := continuous_colAct _
  continuous_invFun := continuous_colAct _

theorem colEquiv_mem (γ : GL (Fin a) E)
    (hγ : ∀ i l : Fin a, k ≤ (i : ℕ) → γ.val i l = (1 : Matrix (Fin a) (Fin a) E) i l)
    (x : UnipotentBlockColumnIndex a k k → Ad E) : colAct (ratGL E a γ).val x ∈ ratV E (UnipotentBlockColumnIndex a k k) ↔ x ∈ ratV E (UnipotentBlockColumnIndex a k k) := by
  have key : ∀ (δ : GL (Fin a) E) (y : UnipotentBlockColumnIndex a k k → Ad E), y ∈ ratV E (UnipotentBlockColumnIndex a k k) →
      colAct (ratGL E a δ).val y ∈ ratV E (UnipotentBlockColumnIndex a k k) := by
    rintro δ _ ⟨c, rfl⟩
    exact ⟨colAct δ.val c, (colAct_rat δ c).symm⟩
  refine ⟨fun h => ?_, key γ x⟩
  have h2 := key γ⁻¹ _ h
  rwa [colAct_colAct (ratGL_rows _ (inv_rows γ hγ)) (ratGL_rows _ hγ)
    (by rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one])] at h2

theorem dot_colAct (γ : GL (Fin a) E) (ξ : UnipotentBlockColumnIndex a k k → E) (y : UnipotentBlockColumnIndex a k k → Ad E) :
    dot ξ (colAct (ratGL E a γ).val y) = dot (fun t => ∑ s : UnipotentBlockColumnIndex a k k, ξ s * γ.val s.1.1 t.1.1) y := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dot, colAct, ratGL_val_apply, Finset.mul_sum, map_sum, Finset.sum_mul, map_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

end Rat

end MirCol

open MirCol

theorem coefF_ratGL_mul : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ (m : ℕ)
    (f : GA E a → ℂ), Continuous f → (∀ γ : GL (Fin a) E, IsMir (m + 1) γ → ∀ g, f (ratGL E a γ * g) = f g) →
    ∀ γ : GL (Fin a) E, IsMir (m + 1) γ → ∀ (ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E) (g : GA E a),
    coefF ψ (m + 1) ξ f (ratGL E a γ * g) =
      coefF ψ (m + 1) (fun t => ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), ξ s * γ.val s.1.1 t.1.1) f g := by
  intro E _ _ a ψ hψ m f hf hl γ hγ ξ g
  have hr : ∀ i l : Fin a, m + 1 ≤ (i : ℕ) → γ.val i l = (1 : Matrix (Fin a) (Fin a) E) i l :=
    fun i l h => hγ i l (Or.inl h)
  have hri := inv_rows γ hr
  have hper := per_coef hψ (fun t => ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), ξ s * γ.val s.1.1 t.1.1) hf
    (fun c g => hl _ (isMir_blkU c) g) g
  have hmem : ∀ x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E,
      colEquiv γ⁻¹ hri x ∈ ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1)) ↔ x ∈ ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1)) :=
    fun x => colEquiv_mem γ⁻¹ hri x
  have key := GlobalTheory.T.quotientAverage_map_lattice_equiv _ _ (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1)))
    (isCoLat_ratV E _) (isCoLat_ratV E _) (colEquiv γ⁻¹ hri) hmem _ hper
  change avg _ _ = avg _ _
  rw [← key]
  congr 1
  funext x
  have hx : colAct (ratGL E a γ).val (colEquiv γ⁻¹ hri x) = x :=
    colAct_colAct (ratGL_rows _ hr) (ratGL_rows _ hri)
      (by rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]) x
  have hd : dot (fun t => ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), ξ s * γ.val s.1.1 t.1.1) (colEquiv γ⁻¹ hri x) = dot ξ x := by
    rw [← dot_colAct, hx]
  have hu : blkU x * (ratGL E a γ * g) = ratGL E a γ * (blkU (colEquiv γ⁻¹ hri x) * g) := by
    rw [← mul_assoc, blkU_mul (ratGL E a γ) (ratGL_rows _ hr), mul_assoc, ← map_inv]
    rfl
  beta_reduce
  rw [hd, hu, hl γ hγ]

end GlobalTheory.CuspGeneric
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerCoefficientRationalMirabolicMulStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittakerCoefficient_rationalMirabolic_mul : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ (m : ℕ) (f : GA E a → ℂ), Continuous f → (∀ γ : GL (Fin a) E, IsMir (m + 1) γ → ∀ g, f (ratGL E a γ * g) = f g) → ∀ γ : GL (Fin a) E, IsMir (m + 1) γ → ∀ (ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E) (g : GA E a), coefF ψ (m + 1) ξ f (ratGL E a γ * g) = coefF ψ (m + 1) (fun t => ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), ξ s * γ.val s.1.1 t.1.1) f g := by
  first | exact @GlobalTheory.CuspGeneric.coefF_ratGL_mul | exact GlobalTheory.CuspGeneric.coefF_ratGL_mul | (intros; apply GlobalTheory.CuspGeneric.coefF_ratGL_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteStableLatticesDifferenceTermNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteStableLatticesDifferenceTermNeZero
noncomputable section
namespace GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma Polynomial Classical

theorem isIntegral_trace_of_isIntegral'
    (U L Ω : Type) [CommRing U] [Field L] [CommRing Ω] [Algebra U L] [Algebra L Ω] [Algebra U Ω]
    [IsScalarTower U L Ω] [Module.Finite L Ω] (ω : Ω) (h : IsIntegral U ω) :
    IsIntegral U (Algebra.trace L Ω ω) := by
  classical
  let b := Module.finBasis L Ω
  let A := AlgebraicClosure L
  let f : Ω →ₐ[U] Matrix (Fin (Module.finrank L Ω)) (Fin (Module.finrank L Ω)) A :=
    (((Algebra.ofId L A).mapMatrix).comp (Algebra.leftMulMatrix b)).restrictScalars U
  have hM : IsIntegral U (f ω) := h.map f
  have htr : algebraMap L A (Algebra.trace L Ω ω) = (f ω).trace := by
    rw [Algebra.trace_eq_matrix_trace b]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, Matrix.diag, map_sum]
    rfl
  rw [← isIntegral_algebraMap_iff (A := L) (B := A) , htr,
    Matrix.trace_eq_sum_roots_charpoly]
  refine IsIntegral.multiset_sum fun μ hμ => ?_
  have hroot : IsRoot (f ω).charpoly μ := (mem_roots'.1 hμ).2
  have hspec : μ ∈ spectrum A (f ω) := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  obtain ⟨p, hp, hp0⟩ := hM
  refine ⟨p, hp, ?_⟩
  have h1 := spectrum.subset_polynomial_aeval (f ω) (p.map (algebraMap U A)) ⟨μ, hspec, rfl⟩
  have h2 : aeval (f ω) (p.map (algebraMap U A)) = 0 := by
    rw [aeval_map_algebraMap]; simpa [aeval_def] using hp0
  have : Nontrivial (Matrix (Fin (Module.finrank L Ω)) (Fin (Module.finrank L Ω)) A) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [spectrum.of_subsingleton] at hspec
    exact hspec
  rw [h2, spectrum.zero_eq, Set.mem_singleton_iff] at h1
  simpa [eval_map] using h1

variable {K : UQ} (B : InvAlg K)

theorem trace_mem_of_isIntegral (x : B.A) (hx : IsIntegral K.O x) :
    Algebra.trace K.E B.A x ∈ (algebraMap K.O K.E).range :=
  IsIntegrallyClosed.isIntegral_iff.1 (isIntegral_trace_of_isIntegral' K.O K.E B.A x hx)

theorem trace_idem_ne_zero (e : B.A) (he : IsIdempotentElem e) (h0 : e ≠ 0) :
    Algebra.trace K.E B.A e ≠ 0 := by
  rw [Algebra.trace_apply]
  have hid : IsIdempotentElem (Algebra.lmul K.E B.A e) := by
    unfold IsIdempotentElem; ext y; simp [← mul_assoc, he.eq]
  intro h
  have := (LinearMap.IsIdempotentElem.trace_eq_zero_iff hid).1 h
  apply h0
  have h1 := LinearMap.congr_fun this 1
  simpa using h1

theorem exists_lb (a : K.O) (ha : K.Small a) (T : K.E) (hT : T ≠ 0) :
    ∃ L : ℤ, ∀ n : ℤ, al K a ^ n * T ∈ (algebraMap K.O K.E).range → L ≤ n := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := K.O) T
  have hy0 : algebraMap K.O K.E y ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  have hx0 : x ≠ 0 := by rintro rfl; simp at hT
  have hα : al K a ≠ 0 := by
    simpa [al] using (IsFractionRing.injective K.O K.E).ne ha.1
  have hinf := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal K.O)
    (IsLocalRing.maximalIdeal.isMaximal K.O).ne_top
  obtain ⟨m0, hm0⟩ : ∃ m : ℕ, x ∉ IsLocalRing.maximalIdeal K.O ^ m := by
    by_contra h
    push_neg at h
    apply hx0
    rw [← Ideal.mem_bot, ← hinf, Ideal.mem_iInf]
    exact h
  refine ⟨1 - m0, fun n hn => ?_⟩
  by_contra hlt
  push_neg at hlt
  obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat (show n ≤ 0 by omega)
  obtain ⟨o, ho⟩ := hn
  have hinv : al K a ^ (-(m : ℤ)) * al K a ^ m = 1 := by
    rw [zpow_neg, zpow_natCast]; exact inv_mul_cancel₀ (pow_ne_zero _ hα)
  have hxe : algebraMap K.O K.E x = algebraMap K.O K.E (o * y * a ^ m) := by
    rw [map_mul, map_mul, ho, map_pow]
    have e1 : al K a ^ (-(m : ℤ)) * (algebraMap K.O K.E x / algebraMap K.O K.E y) * algebraMap K.O K.E y *
        al K a ^ m = (al K a ^ (-(m : ℤ)) * al K a ^ m) * algebraMap K.O K.E x := by
      field_simp
    simp only [al] at e1 hinv ⊢
    rw [e1, hinv, one_mul]
  have hxm : x = o * y * a ^ m := IsFractionRing.injective K.O K.E hxe
  apply hm0
  have : x ∈ IsLocalRing.maximalIdeal K.O ^ m := by
    rw [hxm]; exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow ha.2.1 m)
  exact Ideal.pow_le_pow_right (by omega) this

theorem exists_int_mul (a : K.O) (ha : K.Small a) (y : B.A) :
    ∃ c : ℕ, IsIntegral K.O (al K a ^ (c : ℤ) • y) := by
  have hyE : IsIntegral K.E y := Algebra.IsIntegral.isIntegral y
  obtain ⟨⟨m, hm⟩, hmi⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (nonZeroDivisors K.O) (Rₘ := K.E) y hyE
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  obtain ⟨n, u, hmu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hm0 hϖ
  have ha' : a ∈ Ideal.span {ϖ} := hϖ.maximalIdeal_eq ▸ ha.2.1
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 ha'
  refine ⟨n, ?_⟩
  have hc : a ^ n = (((u⁻¹ : K.Oˣ) : K.O) * b ^ n) * m := by
    rw [hmu, ← hb, mul_pow]
    calc b ^ n * ϖ ^ n = ((u⁻¹ : K.Oˣ) : K.O) * u * (b ^ n * ϖ ^ n) := by simp
      _ = _ := by ring
  have h1 : al K a ^ (n : ℤ) • y = (((u⁻¹ : K.Oˣ) : K.O) * b ^ n) • (m • y) := by
    rw [zpow_natCast, smul_smul, ← hc]
    simp only [al, ← map_pow, algebraMap_smul]
  have h2 : (m • y) = (⟨m, hm⟩ : nonZeroDivisors K.O) • y := rfl
  rw [h1, Algebra.smul_def, h2]
  exact (isIntegral_algebraMap).mul hmi

end GlobalTheory.UnitLemma.Desc

noncomputable section
namespace GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma Polynomial Classical

variable {K : UQ} (B : InvAlg K)

theorem exists_ub (a : K.O) (ha : K.Small a) (e : B.A) (he : IsIdempotentElem e) (he0 : e ≠ 0)
    (y : B.A) : ∃ H : ℤ, IsUnit y → ∀ n : ℤ, IsIntegral K.O (al K a ^ (-n) • (e * y)) → n ≤ H := by
  by_cases hy : IsUnit y
  swap
  · exact ⟨0, fun h => absurd h hy⟩
  have hα : al K a ≠ 0 := by
    simpa [al] using (IsFractionRing.injective K.O K.E).ne ha.1
  obtain ⟨w, hw⟩ := hy.exists_right_inv
  obtain ⟨c, hc⟩ := exists_int_mul B a ha w
  obtain ⟨L, hL⟩ := exists_lb a ha _ (trace_idem_ne_zero B e he he0)
  refine ⟨c - L, fun _ n hn => ?_⟩
  have hi := hn.mul hc
  have heq : al K a ^ (-n) • (e * y) * (al K a ^ (c : ℤ) • w) = al K a ^ (-n + c) • e := by
    rw [smul_mul_smul_comm, mul_assoc, hw, mul_one, ← zpow_add₀ hα]
  rw [heq] at hi
  have ht := trace_mem_of_isIntegral B _ hi
  rw [map_smul, smul_eq_mul] at ht
  have := hL _ ht
  omega

theorem exists_lb' (a : K.O) (ha : K.Small a) (e : B.A) (he : IsIdempotentElem e) (he0 : e ≠ 0) (N : ℕ)
    (s : B.A) : ∃ L0 : ℤ, IsUnit s → ∀ (M : Submodule K.O B.A) (n : ℤ),
      (∀ r : B.A, IsIntegral K.O r → al K a ^ (n + N) • (e * r) ∈ M) → InDual B s M → L0 ≤ n := by
  by_cases hs : IsUnit s
  swap
  · exact ⟨0, fun h => absurd h hs⟩
  have hα : al K a ≠ 0 := by
    simpa [al] using (IsFractionRing.injective K.O K.E).ne ha.1
  obtain ⟨w, hw⟩ := hs.exists_right_inv
  obtain ⟨c, hc⟩ := exists_int_mul B a ha w
  obtain ⟨L, hL⟩ := exists_lb a ha _ (trace_idem_ne_zero B e he he0)
  refine ⟨L - N - c, fun _ M n hM hD => ?_⟩
  have hz := hD _ (hM _ hc)
  have heq : s * (al K a ^ (n + N) • (e * (al K a ^ (c : ℤ) • w))) = al K a ^ (n + N + c) • e := by
    rw [mul_smul_comm, mul_smul_comm, mul_smul_comm, smul_smul, ← zpow_add₀ hα, mul_left_comm, hw, mul_one]
  rw [heq, map_smul, smul_eq_mul] at hz
  have := hL _ hz
  omega

theorem small_card (K : UQ) : K.Small (Nat.card (IsLocalRing.ResidueField K.O) : K.O) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h' : ((Nat.card (IsLocalRing.ResidueField K.O) : ℕ) : K.E) = 0 := by
      rw [← map_natCast (algebraMap K.O K.E), h, map_zero]
    rw [Nat.cast_eq_zero] at h'
    exact (Nat.card_pos (α := IsLocalRing.ResidueField K.O)).ne' h'
  · rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    haveI := Fintype.ofFinite (IsLocalRing.ResidueField K.O)
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  · rw [map_natCast, map_natCast]

theorem finite_term_ne_zero : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι),
    B.P.Separable → IsFrame B e π S → ∀ (I I' : Finset ι), I ⊆ S → I' ⊆ S → ∀ u s : B.A, IsUnit u → IsUnit s →
    {M ∈ B.Lin | term B π I I' u s M ≠ 0}.Finite := by
  intro K B ι _ e π S hsep hF I I' hI hI' u s hu hs
  set a : K.O := (Nat.card (IsLocalRing.ResidueField K.O) : K.O)
  have ha : K.Small a := small_card K
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_lattice_idempotent_position_involution_stable K B ι e π S a hsep ha hF
  obtain ⟨C, hC⟩ := GlobalTheory.T.card_lattices_idempotent_position_bounded K B ι e π S a hsep ha hF N
  have he : ∀ i, IsIdempotentElem (e i) := fun i => hF.1.1.idem i
  have he0 : ∀ i, e i ≠ 0 := by
    intro i
    obtain ⟨f, hf, hf0, -, hS, hnS⟩ := hF.1.2 i
    by_cases hi : i ∈ S
    · rw [(hS hi).1]; exact hf0
    · obtain ⟨h1, h2⟩ := hnS hi
      intro h
      apply hf0
      have : f * e i = f := by rw [h2, mul_add, hf.eq, h1, add_zero]
      rw [h, mul_zero] at this
      exact this.symm
  have hπ : ∀ J ⊆ S, IsUnit (∏ j ∈ J, π j) := fun J hJ =>
    Finset.prod_induction _ IsUnit (fun _ _ h1 h2 => h1.mul h2) isUnit_one
      (fun j hj => (hF.2 j (hJ hj)).1.1)
  choose H hH using fun i y => exists_ub B a ha (e i) (he i) (he0 i) y
  choose Lo hLo using fun i t => exists_lb' B a ha (e i) (he i) (he0 i) N t
  let Ys := I.powerset.image (fun J => (∏ j ∈ J, π j) * u)
  let Ss := I'.powerset.image (fun J => (∏ j ∈ J, π j) * s)
  let P : Set (ι → ℤ) := ⋃ y ∈ (Ys : Set B.A), ⋃ t ∈ (Ss : Set B.A),
    Set.pi Set.univ (fun i => Set.Icc (Lo i t) (H i y))
  have hP : P.Finite := Set.Finite.biUnion Ys.finite_toSet fun y _ =>
    Set.Finite.biUnion Ss.finite_toSet fun t _ => Set.Finite.pi (fun i => Set.finite_Icc _ _)
  refine (hP.biUnion fun p _ => (hC p).1).subset ?_
  rintro M ⟨hML, hMt⟩
  obtain ⟨p, hp⟩ := hN M hML
  have h1 : dlt π I (indM B M) u ≠ 0 := left_ne_zero_of_mul hMt
  have h2 : dlt π I' (indD B M) s ≠ 0 := right_ne_zero_of_mul hMt
  obtain ⟨J, hJ, hJ0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  obtain ⟨J', hJ', hJ0'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
  have hyM : (∏ j ∈ J, π j) * u ∈ M := by
    by_contra h; apply hJ0; simp [indM, h]
  have htD : InDual B ((∏ j ∈ J', π j) * s) M := by
    by_contra h; apply hJ0'; simp [indD, h]
  have hyU : IsUnit ((∏ j ∈ J, π j) * u) :=
    (hπ J ((Finset.mem_powerset.1 hJ).trans hI)).mul hu
  have htU : IsUnit ((∏ j ∈ J', π j) * s) :=
    (hπ J' ((Finset.mem_powerset.1 hJ').trans hI')).mul hs
  refine Set.mem_biUnion (x := p) ?_ hp
  refine Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hJ))
    (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hJ')) ?_)
  intro i _
  exact ⟨hLo i _ htU M (p i) (hp i).1 htD, hH i _ hyU (p i) ((hp i).2 _ hyM)⟩

end GlobalTheory.UnitLemma.Desc
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteStableLatticesDifferenceTermNeZeroStatement
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_stableLattices_differenceTerm_ne_zero : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι), B.P.Separable → IsFrame B e π S → ∀ (I I' : Finset ι), I ⊆ S → I' ⊆ S → ∀ u s : B.A, IsUnit u → IsUnit s → {M ∈ B.Lin | term B π I I' u s M ≠ 0}.Finite := by
  first | exact @GlobalTheory.UnitLemma.Desc.finite_term_ne_zero | exact GlobalTheory.UnitLemma.Desc.finite_term_ne_zero | (intros; apply GlobalTheory.UnitLemma.Desc.finite_term_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousUnipotentColumnWhittakerTransform
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousUnipotentColumnWhittakerTransform
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem continuous_colT_good : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ →
    ∀ (m : ℕ) (f : GA E a → ℂ), Good ψ (m + 1) f → Continuous (colT ψ (m + 1) f) := by
  intro E _ _ a ψ hψ m f hf
  have hl : ∀ (c : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E) g, f (ratGL E a (blkU c) * g) = f g :=
    fun c g => hf.left _ (isMir_blkU c) g
  have key := GlobalTheory.T.continuous_quotientAverage_periodic_family (UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1)))
    (isCoLat_ratV E _) (GA E a)
    (fun p => ψ (-dot (eLast a (m + 1)) p.2) * f (blkU p.2 * p.1)) ?_ ?_
  · exact key
  · refine (hψ.cont.comp ((continuous_dot _).neg.comp continuous_snd)).mul
      (hf.cont.comp (((continuous_posU _).comp continuous_snd).mul continuous_fst))
  · intro g γ hγ y
    exact (per_coef hψ (eLast a (m + 1)) hf.cont hl g).2 γ hγ y

end GlobalTheory.CuspGeneric
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousUnipotentColumnWhittakerTransformStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_unipotentColumnWhittakerTransform : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ (m : ℕ) (f : GA E a → ℂ), Good ψ (m + 1) f → Continuous (colT ψ (m + 1) f) := by
  first | exact @GlobalTheory.CuspGeneric.continuous_colT_good | exact GlobalTheory.CuspGeneric.continuous_colT_good | (intros; apply GlobalTheory.CuspGeneric.continuous_colT_good <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArcTheoremToolsOfWachModuleConclusions
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArcTheoremToolsOfWachModuleConclusions
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.ArcTools

theorem arc_tools_from_clauses :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      UnusedSlot80.SaturationArcLifting D HW F ∧ UnusedSlot80.SaturationEtale D HW F ∧ ArcLiftingSetup.SaturationFrobeniusPullback D HW F ∧ UnusedSlot80.GammaPreservesUniformiser D HW F ∧
      UnusedSlot80.KillerAtLevels D HW F ∧ UnusedSlot80.KillerBoundWithConstant D HW F 8 ∧ UnusedSlot80.KillerAtLevelsSecondForm D HW F ∧
      UnusedSlot80.FirstFiltrationArcLifting D HW F ∧ UnusedSlot80.FirstFiltrationEtale D HW F ∧ UnusedSlot80.SecondFiltrationArcLifting D HW F ∧ UnusedSlot80.SecondFiltrationEtale D HW F ∧
      UnusedSlot80.FiltrationPropertiesEtale D HW F Cm ∧ UnusedSlot80.H1fBaseChangeFree D := by
  intro D HW F Cm
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, c2, a, b, c, d, l3, pE⟩ := GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm
  have hNat : HerrComplexNaturality.HerrNaturality D HW F :=
    HerrComplexNaturality.herr_naturality_theorem_holds D HW F (GlobalTheory.HerrFull.herr_part_a_every_record D HW F)
  have sA : UnusedSlot80.SaturationArcLifting D HW F := UnusedSlot80.saturation_general_statement D HW F ⟨p1, p9⟩
  have sE : UnusedSlot80.SaturationEtale D HW F := UnusedSlot80.saturation_unramified_statement D HW F ⟨p1, p9⟩
  have sP : ArcLiftingSetup.SaturationFrobeniusPullback D HW F := UnusedSlot80.saturation_pullback_statement D HW F p9
  have pi : UnusedSlot80.GammaPreservesUniformiser D HW F := UnusedSlot80.gamma_uniformizer_divisible_statement D HW F p9
  have kL : UnusedSlot80.KillerAtLevels D HW F := UnusedSlot80.annihilator_levels_unramified_statement D HW F Cm ⟨p4, p9⟩
  have kA : UnusedSlot80.KillerBoundWithConstant D HW F 8 := UnusedSlot80.killer_first_theorem_holds D HW F (le_refl _) ⟨kL, pi⟩
  have kE : UnusedSlot80.KillerAtLevelsSecondForm D HW F := UnusedSlot80.killer_second_theorem_holds D HW F pi
  have f1A : UnusedSlot80.FirstFiltrationArcLifting D HW F := UnusedSlot80.firstFiltrationTheoremCaseA D HW F ⟨p2, p5, p9, a, hNat⟩
  have f1E : UnusedSlot80.FirstFiltrationEtale D HW F := UnusedSlot80.firstFiltrationTheoremEtale D HW F ⟨p2, p5, p9, a, hNat⟩
  have f2A : UnusedSlot80.SecondFiltrationArcLifting D HW F := UnusedSlot80.second_filtration_theorem_arc_lifting D HW F ⟨⟨p7, p9, b⟩, f1A⟩
  have f2E : UnusedSlot80.SecondFiltrationEtale D HW F := UnusedSlot80.cohomology_class_unramified_statement D HW F ⟨⟨p7, p9, b⟩, f1E⟩
  have tE : UnusedSlot80.FiltrationPropertiesEtale D HW F Cm := UnusedSlot80.tools_unramified_statement D HW F Cm ⟨p3, p4, p9⟩
  have bc : UnusedSlot80.H1fBaseChangeFree D := UnusedSlot80.base_change_statement D
  exact ⟨sA, sE, sP, pi, kL, kA, kE, f1A, f1E, f2A, f2E, tE, bc⟩

end GlobalTheory.ArcTools
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArcTheoremToolsOfWachModuleConclusionsStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcTheorem_tools_of_wachModuleConclusions : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.SaturationArcLifting D HW F ∧ UnusedSlot80.SaturationEtale D HW F ∧ ArcLiftingSetup.SaturationFrobeniusPullback D HW F ∧ UnusedSlot80.GammaPreservesUniformiser D HW F ∧ UnusedSlot80.KillerAtLevels D HW F ∧ UnusedSlot80.KillerBoundWithConstant D HW F 8 ∧ UnusedSlot80.KillerAtLevelsSecondForm D HW F ∧ UnusedSlot80.FirstFiltrationArcLifting D HW F ∧ UnusedSlot80.FirstFiltrationEtale D HW F ∧ UnusedSlot80.SecondFiltrationArcLifting D HW F ∧ UnusedSlot80.SecondFiltrationEtale D HW F ∧ UnusedSlot80.FiltrationPropertiesEtale D HW F Cm ∧ UnusedSlot80.H1fBaseChangeFree D := by
  first | exact @GlobalTheory.ArcTools.arc_tools_from_clauses | exact GlobalTheory.ArcTools.arc_tools_from_clauses | (intros; apply GlobalTheory.ArcTools.arc_tools_from_clauses <;> assumption)
end
end
