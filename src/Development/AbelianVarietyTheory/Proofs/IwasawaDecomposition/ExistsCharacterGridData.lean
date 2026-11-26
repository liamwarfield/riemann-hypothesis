module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySizesCongruencesHostFactsColumnChoices
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NFunAddOneLtEExpAddCen
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAuxiliaryOfIsAuxiliaryCharacter
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie.GridCharacters

theorem levelLe_of_le {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)} {m n : ℕ}
    (h : χ.LevelLe w m) (hmn : m ≤ n) : χ.LevelLe w n := fun x hx hx' =>
  h x hx (hx'.trans (WithZero.exp_le_exp.2 (by omega)))

theorem expAt_succ {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    (h : χ.LevelLe w (n + 1)) (h' : ¬ χ.LevelLe w n) : ExpAt χ w (n + 1) := fun m =>
  ⟨fun hm => by
    by_contra hlt
    exact h' (levelLe_of_le hm (by omega)), fun hm => levelLe_of_le h hm⟩

end GlobalTheory.LamTie.GridCharacters
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open GlobalTheory.ChiGrid Formalism.L2.Host

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts}

theorem natCast_mem_of_under {w : HeightOneSpectrum (𝓞 D.host.E)} {p : ℕ}
    (h : ((p : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal) : ((p : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
  have h1 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (p : 𝓞 D.host.F) ∈ w.asIdeal := h
  rwa [map_natCast] at h1

theorem natCast_mem_under {w : HeightOneSpectrum (𝓞 D.host.E)} {p : ℕ}
    (h : ((p : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) : ((p : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
  show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (p : 𝓞 D.host.F) ∈ w.asIdeal
  rwa [map_natCast]

theorem nFun_add_one_lt_eExp_add_cen (C : ℝ) (j a : Fin D.R.m) (g : D.R.Psi) :
    (BlochKatoReduction.Gen.NFun D.R : ℚ) + 1 < eExp D j g + (cen D C (D.eTau.symm g) (a.1 + 1) : ℚ) := by
  have h1 := GlobalTheory.LamTie.e_add_v_two_pos (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0 j
  have h2 := Int.lt_floor_add_one
    ((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0).mid (a.1 + 1))
  have h3 := (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0).mid_eq (i := a.1 + 1) (by omega)
  have h4 : (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0).a (a.1 + 1) =
      ((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0).v 2 : ℚ) + 1 / 2 +
        ((D.R.m : ℚ) + 1 - ((a.1 + 1 : ℕ) : ℚ)) * (gap D C : ℚ) := rfl
  have h5 : ((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0).ga : ℚ) = gap D C := rfl
  have h6 := (isLeast_gap D C).1.2.1
  have h7 : bigN D ≤ bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  have h8 : ((bigN D + 2 : ℕ) : ℚ) ≤ gap D C := by exact_mod_cast (by omega)
  have h9 : ((a.1 + 1 : ℕ) : ℚ) ≤ D.R.m := by exact_mod_cast a.2
  have h10 : (0 : ℚ) ≤ gap D C := by positivity
  have h11 : (gap D C : ℚ) ≤ ((D.R.m : ℚ) + 1 - ((a.1 + 1 : ℕ) : ℚ)) * (gap D C : ℚ) := by nlinarith
  have h12 : BlochKatoReduction.Gen.NFun D.R = bigN D := GlobalTheory.LamTie.nFun_eq_bigN D
  rw [h12]
  unfold eExp cen
  push_cast at h8
  linarith

end GlobalTheory.BigTop.Fun

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGridUnitGapFieldContainsValues
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyThetaLiftGridDataUnitGapAllStates
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyThetaLiftGridDataUnitGapAllStates
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HeightCounting.Up

theorem nonempty_gridData_allSt : ∀ cDep : ℝ, AllSt fun K _ _ _ _ _ x => Nonempty (GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩) := by
  intro cDep
  unfold AllSt StepW Step
  refine EvG.imp GlobalTheory.T.eventually_sizes_congruences_hostFacts_columnChoices fun K _ _ _ _ H => large₂.mono (fun B f T _ h hk _ _ w _ P x => ?_) H
  obtain ⟨-, -, -, -, -, -, w0, hP⟩ := h hk T w x.o.Z
  refine GlobalTheory.HeightCounting.Up.ListModel.nonempty_grid w x.o.Z x.m.z ⟨1, cDep, K.s.b⟩ fun k e => ?_
  have hd := hP.distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hd
  fin_cases k
  · exact hd.1 (Or.inr (Or.inr (Or.inr e.symm)))
  · exact hd.2.1 (Or.inr (Or.inr e.symm))

end GlobalTheory.HeightCounting.Up
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyThetaLiftGridDataUnitGapAllStatesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_thetaLiftGridData_unit_gap_all_states : ∀ cDep : ℝ, AllSt fun K _ _ _ _ _ x => Nonempty (GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩) := by
  first | exact @GlobalTheory.HeightCounting.Up.nonempty_gridData_allSt | exact GlobalTheory.HeightCounting.Up.nonempty_gridData_allSt | (intros; apply GlobalTheory.HeightCounting.Up.nonempty_gridData_allSt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNumberFieldGridCharactersUniform
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNumberFieldGridCharactersUniform
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.GridField

open GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun

def vPre (s : Stages) (v : HeightOneSpectrum (𝓞 s.toD7.host.F)) : HeightOneSpectrum (𝓞 s.B.toPre.host.F) := v

def toPl {P Q : Pre} (h : P = Q) (v : HeightOneSpectrum (𝓞 P.host.F)) : HeightOneSpectrum (𝓞 Q.host.F) := by
  subst h
  exact v

theorem leastSplitAuxiliaryPrime_congr_preData {s s' : Stages} (h : s.B.toPre = s'.B.toPre) : GlobalTheory.ChiGrid.q0 s.toD7 = GlobalTheory.ChiGrid.q0 s'.toD7 := by
  obtain ⟨B, C, W, V, S, N, Gj⟩ := s
  obtain ⟨B', C', W', V', S', N', Gj'⟩ := s'
  cases B
  cases B'
  dsimp only at h
  subst h
  rfl

theorem exists_gridData_pl_eq_and_fieldHas_of_basePlace_eq {s s' : Stages} {B₀ : Pre} (hs : s.B.toPre = B₀) (hs' : s'.B.toPre = B₀) {T T' : Type}
    {L : Formalism.IndefR.Links.LevCh s.toD7 T} {L' : Formalism.IndefR.Links.LevCh s'.toD7 T'} {sc : Consts} (G : GridData L sc)
    (G' : GridData L' sc) (hv : toPl hs' (vPre s' G'.pl.v0) = toPl hs (vPre s G.pl.v0)) {K : Type} [Field K]
    (e : K →+* ℂ) (hF : FieldHas G' e) : ∃ G'' : GridData L sc, G''.pl = G.pl ∧ FieldHas G'' e := by
  subst hs
  obtain ⟨B, C, W, V, S, N, Gj⟩ := s
  obtain ⟨B', C', W', V', S', N', Gj'⟩ := s'
  cases B
  cases B'
  dsimp only at hs'
  subst hs'
  have hv0 : G'.pl.v0 = G.pl.v0 := hv
  refine ⟨⟨G.pl, ⟨G'.ch.chiH, G'.ch.chi, G'.ch.chi_eq, G'.ch.triv, G'.ch.inf,
      fun i h1 h2 PP hPP => G'.ch.unr i h1 h2 PP ?_, G'.ch.lev1, G'.ch.wild,
      fun i h1 h2 PP hPP => G'.ch.lev0 i h1 h2 PP (hPP.trans hv0.symm)⟩, G.sp⟩, rfl, ?_⟩
  · intro h
    apply hPP
    rcases G'.pl.mem_S0_of_sum_eq.1 h with h | h
    · exact G.pl.mem_S0_of_sum_eq.2 (Or.inl (h.trans hv0))
    · exact G.pl.mem_S0_of_sum_eq.2 (Or.inr h)
  · refine ⟨hF.values, fun v hv => ?_⟩
    have hd : G.pl.depth sc v = G'.pl.depth sc v := by
      unfold Places.depth
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd (h1.trans hv0.symm) h2
      · exact absurd (h2.trans hv0) h1
      · rfl
    rw [hd]
    refine hF.roots v ?_
    rcases G.pl.mem_S0_of_sum_eq.1 hv with h | h
    · exact G'.pl.mem_S0_of_sum_eq.2 (Or.inl (h.trans hv0.symm))
    · exact G'.pl.mem_S0_of_sum_eq.2 (Or.inr h)

theorem exists_field_uniform : ∀ (cDep b : ℝ) (B₀ : Pre), ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
    ∀ (s : Stages), s.B.toPre = B₀ → 0 < GlobalTheory.ChiGrid.q0 s.toD7 → ∀ (T : Type) (L : Formalism.IndefR.Links.LevCh s.toD7 T)
      (_G : GlobalTheory.ChiGrid.GridData L ⟨1, cDep, b⟩), ∃ G' : GlobalTheory.ChiGrid.GridData L ⟨1, cDep, b⟩,
        GlobalTheory.BigTop.Fun.FieldHas G' M.val.toRingHom := by
  intro cDep b B₀
  classical

  let Wit : Set (HeightOneSpectrum (𝓞 B₀.host.F)) := {v | ∃ (s : Stages) (hs : s.B.toPre = B₀) (T : Type)
    (L : Formalism.IndefR.Links.LevCh s.toD7 T) (G : GridData L ⟨1, cDep, b⟩), toPl hs (vPre s G.pl.v0) = v}
  have hfin : Wit.Finite := by
    rcases Wit.eq_empty_or_nonempty with h | ⟨v₁, s₁, hs₁, T₁, L₁, G₁, -⟩
    · rw [h]
      exact Set.finite_empty
    · have hn : ((GlobalTheory.ChiGrid.q0 s₁.toD7 : ℕ) : 𝓞 B₀.host.F) ≠ 0 := by
        subst hs₁
        exact_mod_cast (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec s₁.toD7).1.ne_zero
      refine (Formalism.L2.DIV.primesOf ((GlobalTheory.ChiGrid.q0 s₁.toD7 : ℕ) : 𝓞 B₀.host.F)).finite_toSet.subset ?_
      rintro _ ⟨s, hs, T, L, G, rfl⟩
      refine Formalism.L2.DIV.mem_primesOf.2 ⟨hn, ?_⟩
      subst hs
      rw [leastSplitAuxiliaryPrime_congr_preData hs₁]
      exact G.pl.basePlace_over_qZero
  have hex : ∀ v : Wit, ∃ Mv : IntermediateField ℚ ℂ, FiniteDimensional ℚ Mv ∧
      ∃ (s : Stages) (hs : s.B.toPre = B₀) (T : Type) (L : Formalism.IndefR.Links.LevCh s.toD7 T)
        (G : GridData L ⟨1, cDep, b⟩), toPl hs (vPre s G.pl.v0) = v ∧ FieldHas G Mv.val.toRingHom := by
    rintro ⟨v, s, hs, T, L, G, hv⟩
    obtain ⟨Mv, h1, h2⟩ := exists_fieldHas G
    exact ⟨Mv, h1, s, hs, T, L, G, hv, h2⟩
  choose Mv hMv hW using hex
  haveI := hfin.to_subtype
  haveI : ∀ v, FiniteDimensional ℚ (Mv v) := hMv
  refine ⟨⨆ v, Mv v, IntermediateField.finiteDimensional_iSup_of_finite, ?_⟩
  intro s hs _ T L G
  obtain ⟨s', hs', T', L', G', hv', hF⟩ := hW ⟨toPl hs (vPre s G.pl.v0), s, hs, T, L, G, rfl⟩
  have hF' : FieldHas G' (⨆ v, Mv v).val.toRingHom :=
    FieldHas.map (IntermediateField.inclusion (le_iSup Mv _)).toRingHom hF
  obtain ⟨G'', -, h⟩ := exists_gridData_pl_eq_and_fieldHas_of_basePlace_eq hs hs' G G' hv' _ hF'
  exact ⟨G'', h⟩

end GlobalTheory.GridField

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNumberFieldGridCharactersUniformStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_numberField_gridCharacters_uniform : ∀ (cDep b : ℝ) (B₀ : Pre), ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ (s : Stages), s.B.toPre = B₀ → 0 < GlobalTheory.ChiGrid.q0 s.toD7 → ∀ (T : Type) (L : Formalism.IndefR.Links.LevCh s.toD7 T) (_G : GlobalTheory.ChiGrid.GridData L ⟨1, cDep, b⟩), ∃ G' : GlobalTheory.ChiGrid.GridData L ⟨1, cDep, b⟩, GlobalTheory.BigTop.Fun.FieldHas G' M.val.toRingHom := by
  first | exact @GlobalTheory.GridField.exists_field_uniform | exact GlobalTheory.GridField.exists_field_uniform | (intros; apply GlobalTheory.GridField.exists_field_uniform <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEmbeddingFixedFieldOfLeComplexImage
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEmbeddingFixedFieldOfLeComplexImage
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem exists_embedding_fixedField_of_le_complexImage : ∀ (s : Stages) (M : IntermediateField ℚ ℂ), M ≤ s.B.fixedCoefficientFieldInComplex → ∃ j : M →+* s.toD7.LL0, (embLL0 s.toD7).comp j = M.val.toRingHom := by
  intro s M hle
  let e := IntermediateField.equivMap s.B.LL0 s.B.embLL.toRatAlgHom
  refine ⟨(e.symm.toAlgHom.toRingHom).comp (IntermediateField.inclusion hle).toRingHom, ?_⟩
  ext x
  show s.B.embLL ((e.symm ⟨x.1, hle x.2⟩ : s.B.LL0) : _) = x.1
  exact congrArg Subtype.val (e.apply_symm_apply ⟨x.1, hle x.2⟩)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEmbeddingFixedFieldOfLeComplexImageStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_LL0_of_le_fixedCoefficientField : ∀ (s : Stages) (M : IntermediateField ℚ ℂ), M ≤ s.B.fixedCoefficientFieldInComplex → ∃ j : M →+* s.toD7.LL0, (embLL0 s.toD7).comp j = M.val.toRingHom := by
  first | exact @GlobalTheory.exists_embedding_fixedField_of_le_complexImage | exact GlobalTheory.exists_embedding_fixedField_of_le_complexImage | (intros; apply GlobalTheory.exists_embedding_fixedField_of_le_complexImage <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalSubfieldComplexFinitelyGenerate
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalSubfieldComplexFinitelyGenerate
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.finDimSubfield_finGen : ∀ (M : IntermediateField ℚ ℂ), FiniteDimensional ℚ M → ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ Lf : IntermediateField ℚ ℂ, (↑S : Set ℂ) ⊆ Lf → M ≤ Lf := by
  intro M hM
  classical
  let b := Module.finBasis ℚ M
  refine ⟨Finset.univ.image (fun i => ((b i : M) : ℂ)), ?_, ?_⟩
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    have : IsIntegral ℚ (b i) := Algebra.IsIntegral.isIntegral _
    exact (this.map M.val).isAlgebraic
  · intro Lf hS x hx
    have hb : ∀ i, ((b i : M) : ℂ) ∈ Lf := fun i =>
      hS (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
    have hx' : (⟨x, hx⟩ : M) = ∑ i, (b.repr ⟨x, hx⟩ i) • b i := (b.sum_repr _).symm
    have : x = ((∑ i, (b.repr ⟨x, hx⟩ i) • b i : M) : ℂ) := by rw [← hx']
    rw [this, IntermediateField.coe_sum]
    simp only [IntermediateField.coe_smul]
    exact Lf.sum_mem fun i _ => Lf.smul_mem (hb i)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalSubfieldComplexFinitelyGenerateStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_subfield_complex_finitelyGenerated : ∀ (M : IntermediateField ℚ ℂ), FiniteDimensional ℚ M → ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ Lf : IntermediateField ℚ ℂ, (↑S : Set ℂ) ⊆ Lf → M ≤ Lf := by
  first | exact @GlobalTheory.finDimSubfield_finGen | exact GlobalTheory.finDimSubfield_finGen | (intros; apply GlobalTheory.finDimSubfield_finGen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeastSplitAuxiliaryPrimePosAllStates
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeastSplitAuxiliaryPrimePosAllStates
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up.PositiveBaseCharge

theorem q0_pos_allSt : AllSt fun _ _ _ _ _ _ x => 0 < GlobalTheory.ChiGrid.q0 (Dof x) :=
  StepW.of_all fun _ _ _ _ _ _ _ _ _ x => (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec (Dof x)).1.pos

end GlobalTheory.HeightCounting.Up.PositiveBaseCharge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeastSplitAuxiliaryPrimePosAllStatesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leastSplitAuxiliaryPrime_pos_allStates : AllSt fun _ _ _ _ _ _ x => 0 < GlobalTheory.ChiGrid.q0 (Dof x) := by
  first | exact @GlobalTheory.HeightCounting.Up.PositiveBaseCharge.q0_pos_allSt | exact GlobalTheory.HeightCounting.Up.PositiveBaseCharge.q0_pos_allSt | (intros; apply GlobalTheory.HeightCounting.Up.PositiveBaseCharge.q0_pos_allSt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGridUnitGapFieldContainsValues
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up

theorem exists_grid_fieldHas : ∀ cDep : ℝ, AllSt fun K _ _ _ _ _ x => ∃ G : GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩, GlobalTheory.BigTop.Fun.FieldHas G (embLL0 (Dof x)) := by
  intro cDep
  have h := StepW.and (GlobalTheory.T.nonempty_thetaLiftGridData_unit_gap_all_states cDep) GlobalTheory.T.leastSplitAuxiliaryPrime_pos_allStates
  refine EvG.imp h (fun K _ _ _ _ hK => ?_)
  obtain ⟨S₁, P₁, A, S₂, a1, a2, hh⟩ := hK
  choose M hMf hM using GlobalTheory.T.exists_numberField_gridCharacters_uniform cDep K.s.b
  choose S hSa hS using fun B₀ => GlobalTheory.T.finiteDimensional_subfield_complex_finitelyGenerated (M B₀) (hMf B₀)
  refine ⟨fun B f F => S₁ B f F ∪ S B, P₁, A, S₂, ?_, a2, ?_⟩
  · intro B f F z hz
    rcases Finset.mem_union.1 hz with hz | hz
    exacts [a1 B f F z hz, hSa B z hz]
  · intro B f T hO hH hP hA hk hF htriv w hw P x
    have hH' : Has₂ B (S₁ B.toPre f B.KsC) (S₂ B.toPre f B.KsC B.fixedCoefficientFieldInComplex (T.set f)) :=
      ⟨fun z hz => hH.1 z (Finset.mem_union_left _ hz), hH.2⟩
    obtain ⟨h1, h3⟩ := hh B f T hO hH' hP hA hk hF htriv w hw
    obtain ⟨G⟩ := h1 P x
    obtain ⟨G', hG'⟩ := hM B.toPre (w.st x.o.Z) rfl (h3 P x) _ x.m.z.R.toRealDat.toLevCh G
    have hle : M B.toPre ≤ B.fixedCoefficientFieldInComplex := hS B.toPre _ (fun z hz => hH.1 z (Finset.mem_union_right _ hz))
    obtain ⟨j, hj⟩ := GlobalTheory.T.exists_ringHom_LL0_of_le_fixedCoefficientField (w.st x.o.Z) (M B.toPre) hle
    refine ⟨G', GlobalTheory.BigTop.Fun.FieldHas.map j ?_⟩
    rw [hj]; exact hG'

end GlobalTheory.HeightCounting.Up
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGridUnitGapFieldContainsValuesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_grid_unit_gap_field_contains_values : ∀ cDep : ℝ, AllSt fun K _ _ _ _ _ x => ∃ G : GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩, GlobalTheory.BigTop.Fun.FieldHas G (embLL0 (Dof x)) := by
  first | exact @GlobalTheory.HeightCounting.Up.exists_grid_fieldHas | exact GlobalTheory.HeightCounting.Up.exists_grid_fieldHas | (intros; apply GlobalTheory.HeightCounting.Up.exists_grid_fieldHas <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAuxiliaryHeckeCharacterToricListOfGridStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAuxiliaryHeckeCharacterToricListOfGridAlt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridLambdaData

theorem isAuxiliaryHeckeCharacter_toricListOfGrid : ∀ (D : D7) {T : Type} (L : Formalism.IndefR.Links.LevCh D T) (sc : GlobalTheory.ChiGrid.Consts) (G : GlobalTheory.ChiGrid.GridData L sc) (w0 : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.LamTie.PlacesOk D.host (AbsolutelyIrreducibleSpan.q0 D) w0 → ∀ a : Fin D.R.m, GlobalTheory.LamTie.IsAuxiliaryHeckeCharacter D.host (G.pl.w G.pl.v0) ((GlobalTheory.BigTop.Fun.lamOf G).c a) ((GlobalTheory.BigTop.Fun.lamOf G).chi a) := by
  intro D T L sc G _ _ a
  have hw0 : (G.pl.w G.pl.v0).under (𝓞 D.host.F) = G.pl.v0 := G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))
  have hS1 : ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.LamTie.Over4 D.host w → w.under (𝓞 D.host.F) ∈ GlobalTheory.ChiGrid.S1 D := by
    intro w h
    rw [GlobalTheory.ChiGrid.S1_mem_OmF]
    rcases h with ⟨k, hk⟩ | hk | hk
    · fin_cases k
      · exact Or.inl (GlobalTheory.BigTop.Fun.natCast_mem_under hk)
      · exact Or.inr (Or.inl (GlobalTheory.BigTop.Fun.natCast_mem_under hk))
    · exact Or.inr (Or.inr (Or.inl (GlobalTheory.BigTop.Fun.natCast_mem_under hk)))
    · exact Or.inr (Or.inr (Or.inr (GlobalTheory.BigTop.Fun.natCast_mem_under hk)))
  have hOv : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∈ GlobalTheory.ChiGrid.S1 D → GlobalTheory.LamTie.Over4 D.host w := by
    intro w h
    rcases (GlobalTheory.ChiGrid.S1_mem_OmF D).1 h with h | h | h | h
    · exact Or.inl ⟨0, GlobalTheory.BigTop.Fun.natCast_mem_of_under h⟩
    · exact Or.inl ⟨1, GlobalTheory.BigTop.Fun.natCast_mem_of_under h⟩
    · exact Or.inr (Or.inl (GlobalTheory.BigTop.Fun.natCast_mem_of_under h))
    · exact Or.inr (Or.inr (GlobalTheory.BigTop.Fun.natCast_mem_of_under h))
  have a1 : 1 ≤ a.1 + 1 := by omega
  have a2 : a.1 + 1 ≤ D.R.m := a.2
  refine ⟨GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (G.ch.chi_eq _ a1 a2), G.ch.triv _ a1 a2,
    GlobalTheory.BigTop.Fun.lamOf_hasInfQ G a, fun w h4 h0 => ?_, fun w h4 => ?_, fun w he => ?_⟩
  · refine G.ch.unr _ a1 a2 w fun hw => ?_
    rcases G.pl.mem_S0_of_sum_eq.1 hw with h | h
    · exact h0 (h.trans hw0.symm)
    · exact h4 (hOv w h)
  · obtain ⟨l2, l1⟩ := G.ch.lev1 _ a1 a2 w (hS1 w h4)
    exact GlobalTheory.LamTie.GridCharacters.expAt_succ (n := 1) l2 l1
  · have e : w.under (𝓞 D.host.F) = G.pl.v0 :=
      (show w.under (𝓞 D.host.F) = (G.pl.w G.pl.v0).under (𝓞 D.host.F) from he).trans hw0
    obtain ⟨l1, l0⟩ := G.ch.lev0 _ a1 a2 w e
    exact GlobalTheory.LamTie.GridCharacters.expAt_succ (n := 0) l1 fun h => l0 (((G.ch.chiH _).unrAt_iff w).2 h)

end GlobalTheory.GridLambdaData
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lamOf_chi_is_chosen_hecke_character_of_placesOk : ∀ (D : D7) {T : Type} (L : Formalism.IndefR.Links.LevCh D T) (sc : GlobalTheory.ChiGrid.Consts) (G : GlobalTheory.ChiGrid.GridData L sc) (w0 : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.LamTie.PlacesOk D.host (AbsolutelyIrreducibleSpan.q0 D) w0 → ∀ a : Fin D.R.m, GlobalTheory.LamTie.IsAuxiliaryHeckeCharacter D.host (G.pl.w G.pl.v0) ((GlobalTheory.BigTop.Fun.lamOf G).c a) ((GlobalTheory.BigTop.Fun.lamOf G).chi a) := by
  first | exact @GlobalTheory.GridLambdaData.isAuxiliaryHeckeCharacter_toricListOfGrid | exact GlobalTheory.GridLambdaData.isAuxiliaryHeckeCharacter_toricListOfGrid | (intros; apply GlobalTheory.GridLambdaData.isAuxiliaryHeckeCharacter_toricListOfGrid <;> assumption)
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up.GridLg

theorem lamOf_ok (D : D7) {T : Type} (L : Formalism.IndefR.Links.LevCh D T) (cDep b : ℝ) (G : GlobalTheory.ChiGrid.GridData L ⟨1, cDep, b⟩)
    (w0 : HeightOneSpectrum (𝓞 D.host.E)) (h : GlobalTheory.LamTie.PlacesOk D.host (AbsolutelyIrreducibleSpan.q0 D) w0) :
    (GlobalTheory.BigTop.Fun.lamOf G).Ok := by
  classical
  refine ⟨⟨?_, h.distinct, h.splits⟩, GlobalTheory.T.lamOf_chi_is_chosen_hecke_character_of_placesOk D L _ G w0 h, fun j a g => ?_⟩
  · have h1 := G.pl.basePlace_over_qZero
    have h2 := G.pl.w_over G.pl.v0 (Finset.mem_insert_self _ _)
    show ((GlobalTheory.ChiGrid.q0 D : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w G.pl.v0).asIdeal
    have h3 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((GlobalTheory.ChiGrid.q0 D : ℕ) : 𝓞 D.host.F) ∈ (G.pl.w G.pl.v0).asIdeal := by
      rw [← h2] at h1; exact h1
    rwa [map_natCast] at h3
  · exact GlobalTheory.BigTop.Fun.nFun_add_one_lt_eExp_add_cen 1 j a g

end GlobalTheory.HeightCounting.Up.GridLg

end
