module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarOfComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubgroupAverageLinearTranslateConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareVolumeIntegrableOnCompactPuncturedPolydi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulHomInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddHaarLeftRightMulAdelicMatricesModule
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterEnvelopingAlgebraDirectSum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsCoefficientFieldChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsCoefficientFieldChange
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LawsFieldChange

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)

theorem goodOf_comp (σ' : c'.F →+* ℂ) :
    (goodOf c' σ').comp (incF c c' hle) = goodOf c (σ'.comp (incF c c' hle)) := by
  have h : GoodEmb c' σ' ↔ GoodEmb c (σ'.comp (incF c c' hle)) := Iff.rfl
  unfold goodOf
  by_cases hg : GoodEmb c' σ'
  · rw [if_pos hg, if_pos (h.1 hg)]
  · rw [if_neg hg, if_neg (fun h' => hg (h.2 h'))]
    rfl

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

theorem modelWt_unfBC (σ' : c'.F →+* ℂ) (G : WTZ E) :
    modelWt (unfBC hle U σ') G = modelWt (U (σ'.comp (incF c c' hle))) G := by
  have hr : relab c' σ' = relab c (σ'.comp (incF c c' hle)) := funext fun τ => RingHom.ext fun x => rfl
  unfold modelWt
  rw [hr]
  rfl

theorem petAt_unfBC (σ' : c'.F →+* ℂ) (x : ℝ) {D : D7} (V : HSp D)
    (dict : GA D V → Σ k, Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) (μ : Measure (AutQ V)) (G : WTZ E)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) :
    petAt (unfBC hle U σ') x V dict μ G (rulBC hle f) = petAt (U (σ'.comp (incF c c' hle))) x V dict μ G f := by
  have hrd := (rulBC_cusp E H Dw l Xo c c' hle r U a n f hf).1 σ'
  unfold petAt
  rw [hrd, modelWt_unfBC hle U σ' G]
  rfl

end

theorem laws_fieldChange : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j Xo c' (unfBC hle U) (fun σ => dict (σ.comp (incF c c' hle))) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f : cuspW Xo c U (wtZ a n), ∃ h : rulBC hle (f : Rul Xo c) ∈ cuspW Xo c' (unfBC hle U) (wtZ a n), ∀ σ : c'.F →+* ℂ, normW (unfBC hle U) (xiR D) (fun _ => D.sp.W j) (fun σ => dict (σ.comp (incF c c' hle))) (wtZ a n) σ ⟨_, h⟩ = normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) (σ.comp (incF c c' hle)) f := by
  intro D j H Dw l Xo c c' hle U dict hL
  refine ⟨?_, ?_⟩
  · exact
      { inR := hL.inR
        host := hL.host
        dat := hL.dat
        levA := hL.levA
        unf := fun σ' hσ' => GlobalTheory.OneMapAll.isUnf_unfExt hle σ' (fun _ => rfl) (hL.unf (σ'.comp (incF c c' hle)) hσ')
        chiTriv := fun σ' hσ' a n hd k γ hγ => by
          rw [laU_unfBC hle U σ' a n]
          exact hL.chiTriv (σ'.comp (incF c c' hle)) hσ' a n hd k γ hγ
        dictU := fun σ' hσ' => hL.dictU (σ'.comp (incF c c' hle)) hσ'
        modelW := fun σ' hσ' => hL.modelW (σ'.comp (incF c c' hle)) hσ' }
  · intro a n _ f
    have hf : (f : Rul Xo c) ∈ cusp Xo c U a n := (cuspW_wtZ (U := U) a n).le f.2
    have hsec : (f : Rul Xo c) ∈ sec Xo c a n := cusp_le_sec _ _ _ _ _ hf
    have hmem : rulBC hle (f : Rul Xo c) ∈ cuspW Xo c' (unfBC hle U) (wtZ a n) := by
      rw [cuspW_wtZ]
      exact (rulBC_cusp _ H Dw l Xo c c' hle D.R.r U a n _ hsec).2.2 hf
    refine ⟨hmem, fun σ' => ?_⟩
    have e1 : normW (unfBC hle U) (xiR D) (fun _ => D.sp.W j) (fun σ => dict (σ.comp (incF c c' hle))) (wtZ a n) σ'
        ⟨_, hmem⟩ = petAt (unfBC hle U (goodOf c' σ')) (xiR D) (D.sp.W j) (dict ((goodOf c' σ').comp (incF c c' hle)))
          (muQ1 (D.sp.W j)) (wtZ a n) (rulBC hle (f : Rul Xo c)) := rfl
    have e2 : normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) (σ'.comp (incF c c' hle)) f =
        petAt (U (goodOf c (σ'.comp (incF c c' hle)))) (xiR D) (D.sp.W j) (dict (goodOf c (σ'.comp (incF c c' hle))))
          (muQ1 (D.sp.W j)) (wtZ a n) (f : Rul Xo c) := rfl
    rw [e1, e2, petAt_unfBC hle U (goodOf c' σ') _ _ _ _ _ hsec]
    have key : ∀ τ τ' : c.F →+* ℂ, τ = τ' →
        petAt (U τ) (xiR D) (D.sp.W j) (dict τ) (muQ1 (D.sp.W j)) (wtZ a n) (f : Rul Xo c) =
        petAt (U τ') (xiR D) (D.sp.W j) (dict τ') (muQ1 (D.sp.W j)) (wtZ a n) (f : Rul Xo c) := by
      rintro τ _ rfl; rfl
    exact key _ _ (goodOf_comp hle σ')

end GlobalTheory.LawsFieldChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsCoefficientFieldChangeStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduliLaws_coefficientFieldChange : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j Xo c' (unfBC hle U) (fun σ => dict (σ.comp (incF c c' hle))) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f : cuspW Xo c U (wtZ a n), ∃ h : rulBC hle (f : Rul Xo c) ∈ cuspW Xo c' (unfBC hle U) (wtZ a n), ∀ σ : c'.F →+* ℂ, normW (unfBC hle U) (xiR D) (fun _ => D.sp.W j) (fun σ => dict (σ.comp (incF c c' hle))) (wtZ a n) σ ⟨_, h⟩ = normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) (σ.comp (incF c c' hle)) f := by
  first | exact @GlobalTheory.LawsFieldChange.laws_fieldChange | exact GlobalTheory.LawsFieldChange.laws_fieldChange | (intros; apply GlobalTheory.LawsFieldChange.laws_fieldChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactUnipotentInCompactSubgroup
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix GlobalTheory.InertSupp

namespace GlobalTheory.UnipCptSub

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem mem_grp_of_le {c : n → ℤ} {g : GL n k} (hg : g ∈ unipOf k c) {m M : ℕ} (hmM : m ≤ M)
    (h : g ∈ GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c m)) :
    g ∈ GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c M) := by
  have key : ∀ x : GL n k, x ∈ unipOf k c → (∀ i j, GlobalTheory.IwahoriInj.Deep ((m : ℤ) * (c i - c j)) (x.val i j)) →
      ∀ i j, GlobalTheory.IwahoriInj.Deep ((M : ℤ) * (c i - c j)) (x.val i j) := by
    intro x hx hd i j
    by_cases hij : c i < c j
    · refine (hd i j).mono ?_
      have : (m : ℤ) ≤ M := by exact_mod_cast hmM
      nlinarith
    · rw [mem_unipOf.1 hx i j hij]
      by_cases e : i = j
      · subst e
        simp [GlobalTheory.IwahoriInj.deep_zero_iff]
      · simp [one_apply_ne e, GlobalTheory.IwahoriInj.deep_zero]
  exact ⟨key g hg h.1, key g⁻¹ (inv_mem hg) h.2⟩

theorem isOpen_grp (c : n → ℤ) (m : ℕ) :
    IsOpen (GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c m) : Set (GL n k)) := by
  have e : (GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c m) : Set (GL n k)) =
      (⋂ i, ⋂ j, {g : GL n k | GlobalTheory.IwahoriInj.Deep ((m : ℤ) * (c i - c j)) (g.val i j)}) ∩
      ⋂ i, ⋂ j, {g : GL n k | GlobalTheory.IwahoriInj.Deep ((m : ℤ) * (c i - c j)) ((g⁻¹).val i j)} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [e]
  refine IsOpen.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
  · exact (GlobalTheory.SBUniform.isOpen_deep _).preimage (Units.continuous_val.matrix_elem i j)
  · exact (GlobalTheory.SBUniform.isOpen_deep _).preimage (Units.continuous_coe_inv.matrix_elem i j)

theorem unipB_eq_unipOf (N : ℕ) :
    unipB k (Fin N) = unipOf k (fun i : Fin N => ((i : ℕ) : ℤ)) := by
  ext g
  rw [mem_unipB, mem_unipOf]
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    have hji : j ≤ i := by
      rw [not_lt] at hij
      exact Fin.le_def.2 (by exact_mod_cast hij)
    rcases hji.lt_or_eq with h | h
    · rw [h1 i j h, one_apply_ne (ne_of_gt h)]
    · subst h; rw [h2 j, one_apply_eq]
  · intro h
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · have : ¬ ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by
        have := Fin.lt_def.1 hji
        omega
      rw [h i j this, one_apply_ne (ne_of_gt hji)]
    · rw [h i i (lt_irrefl _), one_apply_eq]

theorem exists_compact_subgroup_of_isCompact :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}
      (Q : Set (GL (Fin N) k)), IsCompact Q → Q ⊆ (unipB k (Fin N) : Set (GL (Fin N) k)) →
      ∃ U₀ : Subgroup (GL (Fin N) k), IsCompact (U₀ : Set (GL (Fin N) k)) ∧ Q ⊆ (U₀ : Set (GL (Fin N) k)) := by
  intro k _ _ _ _ N Q hQ hQU
  set c : Fin N → ℤ := fun i => ((i : ℕ) : ℤ)
  rw [unipB_eq_unipOf] at hQU
  let V : ℕ → Set (GL (Fin N) k) := fun m =>
    (GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c m) : Set (GL (Fin N) k)) ∪ (unipOf k c : Set _)ᶜ
  have hVo : ∀ m, IsOpen (V m) := fun m =>
    (isOpen_grp c m).union (GlobalTheory.UnipCompact.isClosed_unipOf c).isOpen_compl
  have hVmono : Monotone V := by
    intro m M hmM g hg
    rcases hg with hg | hg
    · by_cases hu : g ∈ unipOf k c
      · exact Or.inl (mem_grp_of_le hu hmM hg)
      · exact Or.inr hu
    · exact Or.inr hg
  have hcov : Q ⊆ ⋃ m, V m := fun g hg =>
    Set.mem_iUnion.2 (((GlobalTheory.UnipCompact.eventually_mem_grp (hQU hg)).exists).imp fun _ h => Or.inl h)
  obtain ⟨M, hM⟩ := hQ.elim_directed_cover V hVo hcov hVmono.directed_le
  refine ⟨GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c M) ⊓ unipOf k c, ?_, fun g hg => ?_⟩
  · rw [Subgroup.coe_inf]
    exact (GlobalTheory.IwahoriInj.isCompact_grp _).inter_right (GlobalTheory.UnipCompact.isClosed_unipOf c)
  · rcases hM hg with h | h
    · exact ⟨h, hQU hg⟩
    · exact absurd (hQU hg) h

end GlobalTheory.UnipCptSub
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryFinitePartMulInjectiveRange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryFinitePartMulInjectiveRange
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.FinPart

open GlobalTheory.DefU.ClassFin

section Ring

variable {R S : Type} [CommRing R] [CommRing S] {n : ℕ}

def tw (n : ℕ) (c : R →+* R) : GL (Fin n) R →* GL (Fin n) R := (invT n R).comp (GeneralLinearGroup.map c)

theorem tw_inv_val (c : R →+* R) (g : GL (Fin n) R) : ((tw n c g)⁻¹).val = cT c g.val := rfl

theorem tw_eq_iff (c : R →+* R) (g : GL (Fin n) R) : tw n c g = g ↔ cT c g.val * g.val = 1 := by
  rw [← tw_inv_val, ← Units.val_mul, Units.val_eq_one, inv_mul_eq_one]

theorem map_tw (p : R →+* S) (c : R →+* R) (d : S →+* S) (h : ∀ y, p (c y) = d (p y)) (g : GL (Fin n) R) :
    GeneralLinearGroup.map p (tw n c g) = tw n d (GeneralLinearGroup.map p g) := by
  apply Units.ext
  ext i j
  exact h _

end Ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def pU : finU (E := E) (n := n) →* GL (Fin n) (Af E) :=
  ((GeneralLinearGroup.map (pFin E)).comp (UA E n).subtype).comp (finU (E := E) (n := n)).subtype

theorem finGL_pU (k : finU (E := E) (n := n)) : finGL E n (pU k) = k.1.1 := finGL_pFin k

theorem pU_injective : Function.Injective (pU (E := E) (n := n)) := fun a b h =>
  Subtype.ext (Subtype.ext (by rw [← finGL_pU, h, finGL_pU]))

theorem tw_pU (k : finU (E := E) (n := n)) : tw n (conjFin (cc E)) (pU k) = pU k := (tw_eq_iff _ _).2 (cT_pFin k.1)

def sU (g : GL (Fin n) (Af E)) (h : tw n (conjFin (cc E)) g = g) : finU (E := E) (n := n) :=
  ⟨⟨finGL E n g, finGL_mem_UA _ ((tw_eq_iff _ _).1 h)⟩, pInf_finGL _⟩

theorem pU_sU (g : GL (Fin n) (Af E)) (h : tw n (conjFin (cc E)) g = g) : pU (sU g h) = g := pFin_finGL g

theorem ratF_tw (g : GL (Fin n) E) :
    ratF E n (tw n (cc E).toRingHom g) = tw n (conjFin (cc E)) (ratF E n g) :=
  map_tw _ _ _ (fun y => (conjFin_algebraMap (cc E) y).symm) g

theorem mem_UE (g : GL (Fin n) E) : g ∈ UE E n ↔ tw n (cc E).toRingHom g = g := by
  rw [tw_eq_iff]
  change cT _ g.val * 1 * g.val = 1 ↔ _
  rw [mul_one]

theorem ratF_injective : Function.Injective (ratF E n) := fun a b h => by
  apply Units.ext
  ext i j
  obtain ⟨w⟩ : Nonempty (HeightOneSpectrum (𝓞 E)) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 E)
    exact ⟨⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)⟩⟩
  haveI : Nontrivial (Af E) := (pLoc E w).domain_nontrivial
  have h' : (ratF E n a).val = (ratF E n b).val := congrArg Units.val h
  exact (algebraMap E (Af E)).injective (congrFun₂ h' i j)

theorem pU_finPt (γ : UE E n) : pU (finPt γ) = ratF E n γ.1 := by
  have h : tw n (conjFin (cc E)) (ratF E n γ.1) = ratF E n γ.1 := by rw [← ratF_tw, (mem_UE _).1 γ.2]
  have e : finPt γ = sU _ h := by
    have h1 : toSub (UA E n) (finGL E n (ratF E n γ.1)) = (sU _ h).1 := dif_pos (sU _ h).1.2
    rw [finPt, h1]
    exact dif_pos (sU _ h).2
  rw [e, pU_sU]

theorem mem_ratFinU (k : finU (E := E) (n := n)) : k ∈ ratFinU E n ↔ pU k ∈ (ratF E n).range := by
  constructor
  · rintro ⟨g, -, hg⟩
    exact ⟨g, (pFin_finGL _).symm.trans (congrArg (GeneralLinearGroup.map (pFin E)) hg)⟩
  · rintro ⟨g, hg⟩
    refine ⟨g, (mem_UE g).2 (ratF_injective ?_), (congrArg (finGL E n) hg).trans (finGL_pU k)⟩
    rw [ratF_tw, hg, tw_pU]

theorem finPt_props : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ a b : UE E n, finPt (a * b) = finPt a * finPt b) ∧ Function.Injective (finPt : UE E n → finU (E := E) (n := n)) ∧ ∀ x : finU (E := E) (n := n), x ∈ ratFinU E n ↔ ∃ γ : UE E n, finPt γ = x := by
  intro E _ _ _ n
  refine ⟨fun a b => pU_injective ?_, fun a b h => Subtype.ext (ratF_injective ?_), fun x => ?_⟩
  · rw [map_mul, pU_finPt, pU_finPt, pU_finPt, Subgroup.coe_mul, map_mul]
  · rw [← pU_finPt, ← pU_finPt, h]
  · rw [mem_ratFinU]
    constructor
    · rintro ⟨g, hg⟩
      have hU : g ∈ UE E n := (mem_UE g).2 (ratF_injective (by rw [ratF_tw, hg, tw_pU]))
      exact ⟨⟨g, hU⟩, pU_injective (by rw [pU_finPt, hg])⟩
    · rintro ⟨γ, rfl⟩
      exact ⟨γ.1, (pU_finPt γ).symm⟩

end GlobalTheory.BCT.FinPart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryFinitePartMulInjectiveRangeStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryFinitePart_mul_injective_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ a b : UE E n, finPt (a * b) = finPt a * finPt b) ∧ Function.Injective (finPt : UE E n → finU (E := E) (n := n)) ∧ ∀ x : finU (E := E) (n := n), x ∈ ratFinU E n ↔ ∃ γ : UE E n, finPt γ = x := by
  first | exact @GlobalTheory.BCT.FinPart.finPt_props | exact GlobalTheory.BCT.FinPart.finPt_props | (intros; apply GlobalTheory.BCT.FinPart.finPt_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupsIntegers
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupsIntegers
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.SBBox

theorem exists_nhds_zero_add_eq {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] {Y : Type}
    [Zero Y] {g : X → Y} (hg : IsLocallyConstant g) (hc : HasCompactSupport g) :
    ∃ N ∈ nhds (0 : X), ∀ y, ∀ u ∈ N, g (y + u) = g y := by
  classical
  have hW : ∀ x : X, ∃ W ∈ nhds (0 : X), ∀ a ∈ W, ∀ b ∈ W, g (x + (a + b)) = g x := by
    intro x
    have h1 : (fun u => x + u) ⁻¹' {y | g y = g x} ∈ nhds (0 : X) := by
      refine (hg.isOpen_fiber (g x)).preimage (continuous_const.add continuous_id) |>.mem_nhds ?_
      simp
    obtain ⟨W, hW, hWW⟩ := exists_nhds_zero_half h1
    exact ⟨W, hW, fun a ha b hb => hWW a ha b hb⟩
  choose W hW0 hWg using hW
  let V : X → Set X := fun x => W x ∩ Neg.neg ⁻¹' W x
  have hV0 : ∀ x, V x ∈ nhds (0 : X) := fun x => Filter.inter_mem (hW0 x) (neg_mem_nhds_zero X (hW0 x))
  have hcov : tsupport g ⊆ ⋃ x : X, (fun y => y - x) ⁻¹' interior (V x) := by
    intro x _
    refine Set.mem_iUnion.2 ⟨x, ?_⟩
    simp only [Set.mem_preimage, sub_self]
    exact mem_interior_iff_mem_nhds.2 (hV0 x)
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (fun x => (fun y => y - x) ⁻¹' interior (V x))
    (fun x => isOpen_interior.preimage (continuous_id.sub continuous_const)) hcov
  refine ⟨⋂ x ∈ t, V x, (Filter.biInter_finset_mem t).2 fun x _ => hV0 x, fun y u hu => ?_⟩
  have hu' : ∀ x ∈ t, u ∈ W x ∧ -u ∈ W x := fun x hx => by
    have := Set.mem_iInter₂.1 hu x hx
    exact ⟨this.1, this.2⟩
  have h0 : ∀ x, (0 : X) ∈ W x := fun x => mem_of_mem_nhds (hW0 x)
  by_cases hy : y ∈ tsupport g
  · obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hy)
    have hyx' : y - x ∈ W x := (interior_subset hyx : y - x ∈ V x).1
    have e1 : g (y + u) = g x := by
      have := hWg x (y - x) hyx' u (hu' x hx).1
      rwa [show x + (y - x + u) = y + u by abel] at this
    have e2 : g y = g x := by
      have := hWg x (y - x) hyx' 0 (h0 x)
      rwa [show x + (y - x + 0) = y by abel] at this
    rw [e1, e2]
  · by_cases hyu : y + u ∈ tsupport g
    · obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hyu)
      have hyx' : y + u - x ∈ W x := (interior_subset hyx : y + u - x ∈ V x).1
      have e1 : g y = g x := by
        have := hWg x (y + u - x) hyx' (-u) (hu' x hx).2
        rwa [show x + (y + u - x + -u) = y by abel] at this
      have e2 : g (y + u) = g x := by
        have := hWg x (y + u - x) hyx' 0 (h0 x)
        rwa [show x + (y + u - x + 0) = y + u by abel] at this
      rw [e1, e2]
    · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyu]

variable {F : Type} [Field F] [NumberField F]

def ballR (r : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) : AddSubgroup (v.adicCompletion F) :=
  Valued.v.leAddSubgroup (v.intValuation r)

theorem mem_ballR {r : 𝓞 F} {v : HeightOneSpectrum (𝓞 F)} {x : v.adicCompletion F} :
    x ∈ ballR r v ↔ Valued.v x ≤ v.intValuation r := Iff.rfl

theorem isOpen_ballR {r : 𝓞 F} (hr : r ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (ballR r v : Set (v.adicCompletion F)) := by
  set c : v.adicCompletion F := algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r)
  have hcv : Valued.v c = v.intValuation r := PI.UnipApproxD.IntegersDenseFiniteAdeles.val_R v r
  have hc : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hcv
    exact (v.intValuation_ne_zero r hr) hcv.symm
  have e : (ballR r v : Set (v.adicCompletion F)) =
      (fun x => x / c) ⁻¹' (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    ext x
    change Valued.v x ≤ v.intValuation r ↔ Valued.v (x / c) ≤ 1
    rw [map_div₀, ← hcv, div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hc))]
  rw [e]
  exact (Valued.isOpen_valuationSubring _).preimage (continuous_id.div_const c)

theorem ballR_subset (r : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    (ballR r v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F := fun x hx => by
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
  exact (mem_ballR.1 hx).trans (v.intValuation_le_one r)

theorem eventually_ballR_eq {r : 𝓞 F} (hr : r ≠ 0) :
    ∀ᶠ v in Filter.cofinite, (ballR r v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F := by
  have h : (Ideal.span {r} : Ideal (𝓞 F)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hr
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h).subset fun v hv => ?_)
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [← HeightOneSpectrum.intValuation_lt_one_iff_dvd]
  refine lt_of_le_of_ne (v.intValuation_le_one r) fun h1 => hv ?_
  ext x
  rw [SetLike.mem_coe, SetLike.mem_coe, mem_ballR, h1, HeightOneSpectrum.mem_adicCompletionIntegers]

end GlobalTheory.SBBox

namespace GlobalTheory.SBBox

theorem exists_box_invariant : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
    g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
    ∃ B : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F),
      (∀ v, IsOpen (B v : Set (v.adicCompletion F))) ∧
      (∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F) ∧
      (∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) ∧
      ∀ y u : κ → FiniteAdeleRing (𝓞 F) F, (∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v) → g (y + u) = g y := by
  intro F _ _ κ _ g hg
  classical
  obtain ⟨N, hN, hNg⟩ := exists_nhds_zero_add_eq hg.1 hg.2
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, -, t, ht, hIt⟩ := hN
  have hr : ∀ i, ∃ r : 𝓞 F, r ≠ 0 ∧ ∀ y : FiniteAdeleRing (𝓞 F) F,
      (∀ v : HeightOneSpectrum (𝓞 F), Valued.v (y v) ≤ v.intValuation r) → y ∈ t i :=
    fun i => GlobalTheory.OpenSubAdele.exists_small_of_mem_nhds (ht i)
  choose r hr0 hrt using hr
  set R : 𝓞 F := ∏ i, r i
  have hR0 : R ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hr0 i
  have hle : ∀ i (v : HeightOneSpectrum (𝓞 F)), v.intValuation R ≤ v.intValuation (r i) := by
    intro i v
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem r (Finset.mem_univ i)
    rw [show R = r i * c from hc, map_mul]
    exact mul_le_of_le_one_right' (v.intValuation_le_one c)
  refine ⟨ballR R, isOpen_ballR hR0, ballR_subset R, eventually_ballR_eq hR0, fun y u hu => ?_⟩
  refine hNg y u (hIt fun i _ => hrt i (u i) fun v => ?_)
  exact (mem_ballR.1 (hu i v)).trans (hle i v)

end GlobalTheory.SBBox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupsIntegersStatement
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_subgroups_integers : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
    g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
    ∃ B : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F),
      (∀ v, IsOpen (B v : Set (v.adicCompletion F))) ∧
      (∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F) ∧
      (∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) ∧
      ∀ y u : κ → FiniteAdeleRing (𝓞 F) F, (∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v) → g (y + u) = g y := by
  first | exact @GlobalTheory.SBBox.exists_box_invariant | exact GlobalTheory.SBBox.exists_box_invariant | (intros; apply GlobalTheory.SBBox.exists_box_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtPLoc
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw

variable (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)

theorem pLoc_ext {a b : FiniteAdeleRing (𝓞 E) E} (h : ∀ v, pLoc E v a = pLoc E v b) : a = b :=
  Subtype.ext (funext h)

theorem matrix_ext_pLoc {A B : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)}
    (h : ∀ v, A.map (pLoc E v) = B.map (pLoc E v)) : A = B := by
  refine Matrix.ext fun i j => ?_
  exact pLoc_ext E fun v => congrFun (congrFun (h v) i) j

end GlobalTheory.EulerTw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSrcMemOrb
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw.Comm

open GlobalTheory.EulerTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem thF_thF (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) : thF E n (thF E n g) = g :=
  GlobalTheory.ThetaPull.thetaGL_thetaGL _ GlobalTheory.ThetaPull.cFin_cFin g

theorem thF_ratF (g : GL (Fin n) E) : ratF E n (thE E n g) = thF E n (ratF E n g) :=
  GlobalTheory.ThetaPull.map_thetaGL _ _ _ (fun x => (conjFin_algebraMap (IsCMField.complexConj E).toRingEquiv x).symm) g

end GlobalTheory.EulerTw.Comm

namespace GlobalTheory.EulerTw

end GlobalTheory.EulerTw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMapGLSpl
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw

variable (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)

theorem continuous_sLoc_spl (v : Pl E) : Continuous (sLoc E v) := by
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (Pl E)) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion E → RestrictedProduct (fun u : Pl E => u.adicCompletion E)
      (fun u => (u.adicCompletionIntegers E : Set (u.adicCompletion E))) (Filter.principal {v}ᶜ) :=
    fun a => ⟨Pi.single v a, fun u hu => by
      rw [Set.mem_setOf_eq, Pi.single_eq_of_ne hu]; exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

theorem continuous_locGL_spl (w : Pl E) : Continuous (locGL E n w) :=
  Continuous.units_map _ (continuous_const.add (Continuous.matrix_map continuous_id (continuous_sLoc_spl E w)))

variable {E n}

end GlobalTheory.EulerTw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameConjugateGramInv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameConjugateGramInv
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WittFrame

theorem yx_eq_one : ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) * X = 1 := by
  intro D V r X Y hW
  have hσ : ∀ x : D.host.E, (D.sp.cm.sig : D.host.E →+* D.host.E) x = star x := fun _ => rfl
  have hJ : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram = V.gram := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hσ, Formalism.BasicNotions.HSpace.gram]
    exact V.herm.eq (V.frame j) (V.frame i)
  have hX : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X) = X := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hσ, star_star]
  have h := congrArg (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)) hW.xy
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hX, hJ, Formalism.UG.cT_one] at h
  rwa [Matrix.mul_assoc]

end GlobalTheory.WittFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameConjugateGramInvStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_frame_conjugate_gram_inv : ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) * X = 1 := by
  first | exact @GlobalTheory.WittFrame.yx_eq_one | exact GlobalTheory.WittFrame.yx_eq_one | (intros; apply GlobalTheory.WittFrame.yx_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnOffCoordinateHyperplanesOfPoincareBo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnOffCoordinateHyperplanesOfPoincareBo
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem integrableOn_offHyp_of_norm_le_poin {n : ℕ} (S : Finset (Fin n)) (U K : Set (V n)) (g : V n → ℂ) (C : ℝ)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (hs : ∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2)
    (hg : ContinuousOn g (offHyp S U)) (h0 : ∀ v ∈ offHyp S U, v ∉ K → g v = 0)
    (hb : ∀ v ∈ offHyp S U, v ∈ K → ‖g v‖ ≤ C * ∏ a, (poinWt S v a)⁻¹ ^ 2) :
    IntegrableOn g (offHyp S U) := by
  have hO : MeasurableSet (offHyp S U) := (isOpen_offHyp_of_isOpen S U hU).measurableSet
  have hv : IntegrableOn (fun v => C * ∏ a, (poinWt S v a)⁻¹ ^ 2) K :=
    (GlobalTheory.T.poincare_volume_integrableOn_compact_punctured_polydisc S K hK fun v hv => hs v (hKU hv)).const_mul C
  have hi : Integrable (K.indicator fun v => C * ∏ a, (poinWt S v a)⁻¹ ^ 2) :=
    (integrable_indicator_iff hK.measurableSet).2 hv
  refine Integrable.mono' hi.integrableOn (hg.aestronglyMeasurable hO) ?_
  refine (ae_restrict_iff' hO).2 (Eventually.of_forall fun v hvO => ?_)
  by_cases hvK : v ∈ K
  · rw [Set.indicator_of_mem hvK]
    exact hb v hvO hvK
  · rw [Set.indicator_of_notMem hvK, h0 v hvO hvK, norm_zero]

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnOffCoordinateHyperplanesOfPoincareBoStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_offCoordinateHyperplanes_of_poincareBound : ∀ {n : ℕ} (S : Finset (Fin n)) (U K : Set (V n)) (g : V n → ℂ) (C : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → ContinuousOn g (offHyp S U) → (∀ v ∈ offHyp S U, v ∉ K → g v = 0) → (∀ v ∈ offHyp S U, v ∈ K → ‖g v‖ ≤ C * ∏ a, (poinWt S v a)⁻¹ ^ 2) → IntegrableOn g (offHyp S U) := by
  first | exact @GlobalTheory.GoodTop.integrableOn_offHyp_of_norm_le_poin | exact GlobalTheory.GoodTop.integrableOn_offHyp_of_norm_le_poin | (intros; apply GlobalTheory.GoodTop.integrableOn_offHyp_of_norm_le_poin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdDFormUniformiserCons
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory

theorem formOrd_dForm_uniformiser_cons : ∀ {k K : Type} [Field k] [CharZero k] [Field K] (c : k →+* K) (n : ℕ) (E : Place c) (t : E.ring)
  (w : Fin n → E.ring), Irreducible t →
  (∀ P : MvPolynomial (Fin n) k, P ≠ 0 → IsUnit (MvPolynomial.eval₂ E.const w P)) →
  (∃ x : Fin (n + 1) → K, TrBasis c x) →
  (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm c (Fin.cons (t : K) (fun i => (w i : K)) : Fin (n + 1) → K)) = 0 := by
  intro k K _ _ _ c n E t w ht hw hx
  obtain ⟨x, hx⟩ := hx
  have e : dForm c (Fin.cons (t : K) (fun i => (w i : K)) : Fin (n + 1) → K) =
      E.toRat (n + 1) (dForm E.const (Fin.cons t w : Fin (n + 1) → E.ring)) := by
    have h := TopForm.formMap_dForm (D := n + 1) (α := E.const) (β := c) E.ring.subtype rfl
      (Fin.cons t w : Fin (n + 1) → E.ring)
    refine Eq.trans ?_ h.symm
    congr 1
    funext i
    cases i using Fin.cases <;> rfl
  letI := E.const.toAlgebra
  letI := c.toAlgebra
  haveI : IsScalarTower k E.ring K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType k E.ring := E.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField k E.ring
  obtain ⟨t', ht'⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  obtain ⟨m, z, b, -, hb⟩ := exists_basis_kaehler_uniformiser k ht'
  have h1 := trdeg_eq_of_basis_kaehler k K b
  have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := k) hx
  rw [h1, Cardinal.mk_fin] at h2
  obtain rfl : n = m := by
    have : n + 1 = m + 1 := by exact_mod_cast h2
    omega
  have hG := isFreeGen_dForm_uniformiser_cons k E.ring E.const n t w E.essFiniteType ht ⟨b⟩ hw
  rw [e]
  exact E.formOrd_toRat hG

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroOfTwOrbNeZero
open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

theorem exists_ne_zero_of_avg_ne_zero {H : Type} [Group H] (u : H → ℂ) (h : avg u ≠ 0) : ∃ k, u k ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (by simp [avg, hc])

theorem exists_ne_zero_of_twOrb_ne_zero {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G)
    (f : G → ℂ) (h : twOrb θ K δ f ≠ 0) : ∃ x, f (x⁻¹ * δ * θ x) ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  unfold twOrb
  simp only [hc]
  simp [avg]

theorem exists_ne_zero_of_clSum_ne_zero {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G)
    (S : Set G) (wt f : G → ℂ) (h : clSum θ K S wt f ≠ 0) : ∃ δ ∈ S, ∃ x, f (x⁻¹ * δ * θ x) ≠ 0 := by
  by_contra hc
  apply h
  unfold clSum
  refine finsum_eq_zero_of_forall_eq_zero fun c => ?_
  split_ifs with hS
  · by_contra hne
    exact hc ⟨c.rep, hS, exists_ne_zero_of_twOrb_ne_zero θ K c.rep f (right_ne_zero_of_mul hne)⟩
  · rfl

theorem nrmL_twConj {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (δ x : GLw n w) :
    nrmL n w (x⁻¹ * δ * thL n w x) = x⁻¹ * nrmL n w δ * x := by
  have hinv := TwistInvol.thL_involutive E n w x
  unfold nrmL
  unfold thL at hinv ⊢
  split_ifs at hinv ⊢ with hs
  · simp
  · simp only [map_mul, map_inv, hinv]
    group

end GlobalTheory.BCT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatGLOfIsCompAlongSplit
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitSatake

theorem hasSatGL_of_isCompAlong_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ₁ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (ρ₂ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W),
    IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) ρ₁ →
    IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) ρ₂ →
    ∀ T : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL w ρ₁ T → GlobalTheory.LFun.HasSatGL w ρ₂ T := by
  intro E _ _ _ n π hπ w hw V W _ _ _ _ ρ₁ ρ₂ h₁ h₂ T hT
  obtain ⟨e, he⟩ := GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL E n w hw
  obtain ⟨r, -, -, hc⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w
  let s : GL (Fin n) (w.adicCompletion E) →* UA E n :=
    (locU n w).subtype.comp e.symm.toMulEquiv.toMonoidHom
  have hs : ∀ y, cLoc w (s y) = y := fun y => by
    have := he (e.symm y)
    rw [e.apply_symm_apply] at this
    exact this.symm
  let P : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  have key : ∀ {X : Type} [AddCommGroup X] [Module ℂ X] (τ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) X),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) τ →
      ∃ f : τ.IntertwiningMap (P.rep.comp s), f ≠ 0 := by
    rintro X _ _ τ ⟨-, f, h0, hf, h2⟩
    refine ⟨⟨f.codRestrict π hf, fun y => LinearMap.ext fun v => Subtype.ext ?_⟩, fun e0 => h0 ?_⟩
    · have h3 := h2 (e.symm y) v
      have hy : ((cLoc w).comp (locU n w).subtype) (e.symm y) = y := hs y
      rw [hy] at h3
      exact h3
    · exact LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun e0 v)
  obtain ⟨f, hf⟩ := key ρ₁ h₁
  obtain ⟨f', hf'⟩ := key ρ₂ h₂
  have hcomm : ∀ g : UA E n, ∃ u, ∀ y, Commute ((s u)⁻¹ * g) (s y) := fun g =>
    ⟨e (r g), fun y => by
      have : s (e (r g)) = (r g : UA E n) := congrArg Subtype.val (e.symm_apply_apply (r g))
      rw [this]
      exact hc g (e.symm y)⟩
  obtain ⟨q⟩ := (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor _ _ _ _ _ P.rep s ρ₁ ρ₂ P.isIrreducible_rep h₁.1 h₂.1 hcomm f hf).2 f' hf'
  exact GlobalTheory.BaseChangeBridge.hasSatGL_of_equiv q.toLinearEquiv
    (fun g x => LinearMap.congr_fun (q.toIntertwiningMap.isIntertwining' g) x) hT

end GlobalTheory.SplitSatake
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMulRight
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RightMulJac

theorem integral_mul_right : ∀ (D : D7) (t n : ℕ) (μ₁ : Measure (Mx D t n)) (𝓕₁ : Set (Mx D t n)),
    IsCovolOne (ratMx D t n) μ₁ 𝓕₁ →
    ∀ (a : GL (Fin n) (AE D)) (f : Mx D t n → ℂ),
      ∫ x, f (x ⬝ a.1) ∂μ₁ = npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(t : ℂ)) * ∫ x, f x ∂μ₁ := by
  intro D t n μ₁ 𝓕₁ hμ a f
  haveI : μ₁.IsAddHaarMeasure := hμ.1
  haveI : BorelSpace (Mx D t n) := ⟨rfl⟩
  have hkey := GlobalTheory.ModuLR.modu_lrMul D t n μ₁ hμ.1 1 a
  simp only [map_one, one_pow, one_mul, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mul, ENNReal.coe_one] at hkey
  set c : ℝ≥0 := absA D (Matrix.GeneralLinearGroup.det a) with hc
  have hc0 : c ≠ 0 := by
    exact ((Group.isUnit (Matrix.GeneralLinearGroup.det a)).map (absA D)).ne_zero
  have hcont : Continuous fun u : Mx D t n => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) a.val : Mx D t n) := continuous_id.matrix_mul continuous_const
  have hcont' : Continuous fun u : Mx D t n => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) (a⁻¹).val : Mx D t n) := continuous_id.matrix_mul continuous_const
  let e : Mx D t n ≃ₜ Mx D t n :=
    { toFun := fun u => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) a.val : Mx D t n)
      invFun := fun u => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) (a⁻¹).val : Mx D t n)
      left_inv := fun u => by simp [Matrix.mul_assoc]
      right_inv := fun u => by simp [Matrix.mul_assoc]
      continuous_toFun := hcont
      continuous_invFun := hcont' }
  have hemb : MeasurableEmbedding (fun u : Mx D t n => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) a.val : Mx D t n)) := e.measurableEmbedding
  have hmap : μ₁.map (fun u : Mx D t n => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) a.val : Mx D t n)) = ((c : ENNReal) ^ t)⁻¹ • μ₁ := by
    conv_rhs => rw [hkey]
    rw [smul_smul, ENNReal.inv_mul_cancel (by simp [hc0]) (by simp), one_smul]
  rw [show (∫ x, f (x ⬝ a.1) ∂μ₁) = ∫ x, f ((fun u : Mx D t n => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) a.val : Mx D t n)) x) ∂μ₁ from rfl,
    ← hemb.integral_map, hmap, integral_smul_measure]
  rw [Complex.real_smul, npow]
  congr 1
  rw [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.coe_toReal,
    show (-(t : ℂ)) = ((-(t : ℝ) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (NNReal.coe_nonneg c), Real.rpow_neg (NNReal.coe_nonneg c), Real.rpow_natCast]

end GlobalTheory.RightMulJac

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnvRepAllEnvIncl
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct

namespace GlobalTheory.CentralOps

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}


open Classical in
def lieRep (R : RealPoints θ V) : GlobalTheory.AutFinLit.LieC V →ₗ⁅ℂ⁆ Module.End ℂ (SmF θ V) :=
  DirectSum.toLieAlgebra _ (fun τ => (envRep R τ).toLieHom.comp (UniversalEnvelopingAlgebra.ι ℂ)) fun τ τ' h x y => by
    change (envRep R τ (UniversalEnvelopingAlgebra.ι ℂ x)) * envRep R τ' (UniversalEnvelopingAlgebra.ι ℂ y) -
      envRep R τ' (UniversalEnvelopingAlgebra.ι ℂ y) * envRep R τ (UniversalEnvelopingAlgebra.ι ℂ x) = 0
    rw [(envRep_comm R h _ _).eq, sub_self]

def envRepAll (R : RealPoints θ V) : GlobalTheory.AutFinLit.Env V →ₐ[ℂ] Module.End ℂ (SmF θ V) :=
  UniversalEnvelopingAlgebra.lift ℂ (lieRep R)


open Classical in
def envIncl (V : HSp D) (τ : D.what₂.Tau) : EnvAt V τ →ₐ[ℂ] GlobalTheory.AutFinLit.Env V :=
  UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp
    (DirectSum.lieAlgebraOf ℂ D.what₂.Tau (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ))

open Classical in
theorem envIncl_ι (τ : D.what₂.Tau) (x : ℂ ⊗[ℝ] LieAt V τ) :
    envIncl V τ (UniversalEnvelopingAlgebra.ι ℂ x) =
      UniversalEnvelopingAlgebra.ι ℂ (DirectSum.of (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ x) := by
  simp [envIncl]

theorem envRepAll_envIncl (R : RealPoints θ V) (τ : D.what₂.Tau) (u : EnvAt V τ) :
    envRepAll R (envIncl V τ u) = envRep R τ u := by
  classical
  have : (envRepAll R).comp (envIncl V τ) = envRep R τ := by
    apply UniversalEnvelopingAlgebra.hom_ext
    refine LieHom.ext fun x => ?_
    change envRepAll R (envIncl V τ (UniversalEnvelopingAlgebra.ι ℂ x)) = envRep R τ (UniversalEnvelopingAlgebra.ι ℂ x)
    rw [envIncl_ι, envRepAll, UniversalEnvelopingAlgebra.lift_ι_apply, lieRep]
    exact DirectSum.toModule_lof ℂ (M := fun τ => ℂ ⊗[ℝ] LieAt V τ) τ x
  exact congrArg (fun f : EnvAt V τ →ₐ[ℂ] _ => f u) this

end GlobalTheory.CentralOps
end
end
