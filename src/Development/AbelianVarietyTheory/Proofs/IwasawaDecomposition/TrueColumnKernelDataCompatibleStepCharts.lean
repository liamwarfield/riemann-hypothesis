module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFullHermitianColumnsTrueColumns
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultiplierPowerUnitConstant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsToricTorsionCubicalWeilOneComplexPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepNearLiftsComponentMemLocalChartGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepCharacterInverseTypeAtLifts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CongruentAutomorphismsLiftStepGroupElements
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CongruentAutomorphismsLiftStepGroupElements
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

set_option maxHeartbeats 1600000 in
private theorem mem_GLint_and_exists_liftsInv_of_congE : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m)
    (b : (I.stp u a i).β) (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : B.fields.K),
    MidAt I hi b P g z → g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 ∧
      ∀ g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, CongE P.1 ((I.cst a).D P) g g' →
        ∃ κ : (I.stp u a i).G b, (I.stp u a i).gam b κ = 1 ∧ LiftsInv I κ P g' ∧ ∀ P', P' ≠ P → LiftsInv I κ P' 1 := by
  classical
  intro B X I hI u a i hi b P g z hmid
  have hO := hI.idx_ok a
  have hpr := (GlobalTheory.TwU.exists_midLev_iff (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P
    ((I.idx a).h i (Idx.get b hi) P) g).mp ⟨z, hmid⟩
  have hgi : g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 := hO.int i (Idx.get b hi) P hpr
  refine ⟨hgi, fun g' hg' hc => ?_⟩
  have hb : b.1 = some (Idx.get b hi) := (Option.some_get _).symm
  have hstd : ∀ (k : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1)) {x : Sp B.fields.E (B.R.N i)},
      x ∈ stdAt B.fields.E (B.R.N i) P.1 → k.1 x ∈ stdAt B.fields.E (B.R.N i) P.1 :=
    fun k _ hx => GlobalTheory.TopStep.glint_mem k hx
  refine ⟨⟨1, ⟨fun w => if h : w.1 = P.1 then
      (GlobalTheory.TopStep.redGL (B.R.N i) w.1 ⟨g, by rw [h]; exact hgi⟩)⁻¹ else 1, ?_⟩,
    ⟨fun w => if h : w.1 = P.1 then
      (⟨g', by rw [h]; exact hg'⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) w.1))⁻¹ else 1, ?_⟩⟩, ?_, ?_, ?_⟩
  · rw [LevFam.grp, Subgroup.mem_pi]
    intro w _
    simp only [levGAt, hb, Option.elim]
    by_cases hw : w.1 = P.1
    · rw [dite_eq_left hw]
      apply inv_mem
      rw [hO.grpG]
      obtain ⟨w, hwG⟩ := w
      simp only at hw
      subst hw
      exact ⟨g, hpr, fun x hx => GlobalTheory.TopStep.redV_redGL ⟨g, hgi⟩ hx⟩
    · rw [dite_eq_right hw]
      exact one_mem _
  · rw [LevQFam.grp, Subgroup.mem_pi]
    intro w _
    simp only [levQAt, hb, Option.elim]
    by_cases hw : w.1 = P.1
    · rw [dite_eq_left hw]
      apply inv_mem
      obtain ⟨w, hwQ⟩ := w
      simp only at hw
      subst hw
      have hgQ : (⟨g, hgi⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1)) ∈
          ((I.idx a).levQ i (Idx.get b hi) ⟨P.1, hwQ⟩).H := by
        rw [hO.grpQ, Subgroup.mem_subgroupOf]
        exact hpr
      set k := (⟨g, hgi⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1))⁻¹ with hk
      have hkg : ∀ v, k.1 (g v) = v := by
        intro v
        have h1 : k * (⟨g, hgi⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1)) = 1 := inv_mul_cancel _
        exact congrArg (fun m : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1) => m.1 v) h1
      have hdeep := levQ_deep I hI a i hi (Idx.get b hi) P hwQ (k * ⟨g', hg'⟩)
      obtain ⟨hd, -⟩ := hdeep (by
        intro x hx
        have hneg := Submodule.neg_mem _ (hstd k (hc x hx))
        rw [map_smul, map_sub, hkg, ← smul_neg, neg_sub] at hneg
        exact hneg)
      have e2 : (⟨g', hg'⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1)) = ⟨g, hgi⟩ * (k * ⟨g', hg'⟩) := by
        rw [hk, mul_inv_cancel_left]
      rw [e2]
      exact mul_mem hgQ hd
    · rw [dite_eq_right hw]
      exact one_mem _
  · exact map_one (ufGL B.fields.E (B.R.N i))
  · refine ⟨hg', ?_, ?_⟩
    · intro h x hx
      dsimp only
      rw [dite_eq_left rfl, inv_inv, ← GlobalTheory.TopStep.redV_redGL ⟨g, hgi⟩ hx]
      have hD : (I.cst a).D P = 1 := hO.depthG P h
      have hq := hc x hx
      rw [hD, pow_one] at hq
      funext l
      have h1 : IntAt P.1 (g x l) := GlobalTheory.TopStep.mem_stdAt.mp (hstd ⟨g, hgi⟩ hx) l
      have h2 : IntAt P.1 (g' x l) := GlobalTheory.TopStep.mem_stdAt.mp (hstd ⟨g', hg'⟩ hx) l
      have h3 : IntAt P.1 (((qOf P.1 : ℕ) : B.fields.E)⁻¹ * (g x l - g' x l)) := GlobalTheory.TopStep.mem_stdAt.mp hq l
      have h0 := GlobalTheory.TopStep.redP_eq_zero_of_div (P := P.1) (a := g x l - g' x l) (by rw [div_eq_inv_mul]; exact h3)
      rw [GlobalTheory.TopStep.reduction_sub h1 h2, sub_eq_zero] at h0
      exact h0.symm
    · intro h
      dsimp only
      rw [dite_eq_left rfl, inv_inv]
  · intro P' hP'
    have hne : P'.1 ≠ P.1 := fun e => hP' (Subtype.ext e)
    refine ⟨one_mem _, ?_, ?_⟩
    · intro h x hx
      dsimp only
      rw [dite_eq_right hne, inv_one]
      simp
    · intro h
      dsimp only
      rw [dite_eq_right hne, inv_one]
      all_goals rfl


open Classical in
theorem midAt_lifts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m)
    (b : (I.stp u a i).β) (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : B.fields.K),
    MidAt I hi b P g z → g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 ∧
      ∀ g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, CongE P.1 ((I.cst a).D P) g g' →
        ∃ κ : (I.stp u a i).G b, (I.stp u a i).gam b κ = 1 ∧ LiftsInv I κ P g' ∧ ∀ P', P' ≠ P → LiftsInv I κ P' 1 := mem_GLint_and_exists_liftsInv_of_congE

end GlobalTheory.Mem.Col2.AdT

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CongruentAutomorphismsLiftStepGroupElementsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruent_automorphisms_lift_step_group_elements : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m) (b : (I.stp u a i).β) (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : B.fields.K), MidAt I hi b P g z → g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 ∧ ∀ g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, CongE P.1 ((I.cst a).D P) g g' → ∃ κ : (I.stp u a i).G b, (I.stp u a i).gam b κ = 1 ∧ LiftsInv I κ P g' ∧ ∀ P', P' ≠ P → LiftsInv I κ P' 1 := by
  first | exact @GlobalTheory.Mem.Col2.AdT.midAt_lifts | exact GlobalTheory.Mem.Col2.AdT.midAt_lifts | (intros; apply GlobalTheory.Mem.Col2.AdT.midAt_lifts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLatticeIdealTrivialAtChainBadPrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLatticeIdealTrivialAtChainBadPrimes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT


open Formalism.HermitianLatticesTheory GlobalTheory.ThetaMove in
theorem inverseHalfDifferent_local_trivial_at_prime_norm {R : Ranks} (H : Host R) (P : HeightOneSpectrum (𝓞 H.E)) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (h2 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 H.E) ∉ P.asIdeal ^ 2) :
    Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (H.AA0 : Submodule (𝓞 H.E) H.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 H.E) H.E) := by
  have := P.isPrime
  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 H.E) ∈ P.asIdeal := Ideal.absNorm_mem _
  have hnd := GlobalTheory.PeriodIdealUnit.not_dvd_different (K := H.K) hp P.asIdeal hmem h2
  have hnot : ¬ H.𝔟 ≤ P.asIdeal := fun hle => hnd (by
    rw [H.𝔟_spec.1]
    exact (Ideal.dvd_iff_le.2 hle).mul_right _)
  obtain ⟨z, hz, hzP⟩ := IsConcreteLE.not_le_iff_exists.1 hnot
  have hB : ((H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 fun h => by
      have h3 := H.𝔟_spec.2
      simp [h] at h3
  refine GlobalTheory.PeriodIdealUnit.locP_eq_one P _ ?_ ?_
  · intro t ht
    have ht' : t ∈ H.AA0 := ht
    unfold Host.AA0 at ht'
    obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1
      ((FractionalIdeal.mem_inv_iff hB).1 ht' _ (FractionalIdeal.mem_coeIdeal_of_mem _ hz))
    refine (mem_locP P 1 t).2 ⟨z, hzP, Submodule.mem_one.2 ⟨w, ?_⟩⟩
    rw [Algebra.smul_def, hw, mul_comm]
  · refine ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
    rw [one_smul]
    show (1 : H.E) ∈ H.AA0
    unfold Host.AA0
    refine (FractionalIdeal.mem_inv_iff hB).2 fun y hy => ?_
    rw [one_mul]
    exact FractionalIdeal.coeIdeal_le_one hy

theorem aaUnit_sall : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ), (I.J.amb B χ).AAUnit (Sall (Pr := B.primes X) I.sel (I.tup a) u) := by
  intro B X I hOk u a χ P hP
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have bad := GlobalTheory.ThetaMove.BadPrimes.bad_primes B.fields (B.primes X) I.sel I.S (I.tup a) u hX hPr hOk.sel_ok
    (hOk.T_mem u) hOk.g_mem P hP
  show Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Th.perAA B.host ⊤) = _
  rw [Th.perAA_top]
  exact inverseHalfDifferent_local_trivial_at_prime_norm B.host P bad.2.1 bad.2.2.1

end GlobalTheory.Mem.Col2.AdT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLatticeIdealTrivialAtChainBadPrimesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodLatticeIdeal_trivial_at_chain_bad_primes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ), (I.J.amb B χ).AAUnit (Sall (Pr := B.primes X) I.sel (I.tup a) u) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.aaUnit_sall | exact GlobalTheory.Mem.Col2.AdT.aaUnit_sall | (intros; apply GlobalTheory.Mem.Col2.AdT.aaUnit_sall <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTopStepLevelCongruentBlockSumOne
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTopStepLevelCongruentBlockSumOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

open GlobalTheory.TopStep

section Local

variable {E : Type} [Field E] {N : ℕ}

theorem prXpG_sumE (hN : N = (N - 1) + 1) (g : Sp E (N - 1) ≃ₗ[E] Sp E (N - 1)) :
    prXpG E N ∘ₗ (sumE hN g 1).toLinearMap = (g.toLinearMap : Sp E ((N - 1) + 0) →ₗ[E] Sp E ((N - 1) + 0)) ∘ₗ prXpG E N := by
  refine LinearMap.ext fun x => funext fun i => ?_

  exact congrFun (prH_sumE hN g 1 x) i

theorem atNL_sumE (hN : N = (N - 1) + 1) (g : Sp E (N - 1) ≃ₗ[E] Sp E (N - 1)) :
    atNL E N (N - 1) ∘ₗ (sumE hN g 1).toLinearMap = atNL E N (N - 1) := by
  refine LinearMap.ext fun x => ?_
  have hlt : N - 1 < N := by omega

  have h := sumE_last hN g 1 x
  rw [Units.val_one, one_mul] at h
  simp only [LinearMap.comp_apply, atNL, dif_pos hlt, LinearMap.proj_apply]
  exact h

end Local

end GlobalTheory.Mem.Col2.AdT

namespace GlobalTheory.Mem.Col2.AdT

open GlobalTheory.TopStep

theorem exists_topLev_liftsInv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i = B.R.m →
    ∀ (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (P : SBof I a), ∃ g g' z,
      GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P g z ∧ LiftsInv I κ P g' ∧
        CongE P.1 (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P) g g' := by
  intro B X I hI u a i hi b κ P
  subst hi

  rcases b with ⟨_ | b₀, hb⟩
  swap
  · exact absurd (hb.mp rfl) (lt_irrefl _)
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1

  have hq : ((qOf P.1 : ℕ) : 𝓞 B.fields.E) ∉ P.1.asIdeal ^ 2 :=
    Formalism.L2.Ker.mq_rowSG_unif (I.tup a) (GlobalTheory.Mem.FieldsLaws.fields_ok (B := B)) hPr hI.sel_ok P
  have hN := N_m_succ B.R
  by_cases hP : P.1 ∈ (B.primes X).vGs
  ·
    have hQn : P.1 ∉ I.Q a := QE_disj (I.tup a) hPr hI.sel_ok hI.g_mem P.1 hP
    have hmem : κ.2.1.1 ⟨P.1, hP⟩ ∈ (levGTop I.Ch I.Ps ⟨P.1, hP⟩).H := by
      have h := κ.2.1.2
      simp only [LevFam.grp, Subgroup.mem_pi] at h
      rw [← topLev_levG_m I.Ch I.sel (I.tup a) (I.cst a) I.Ps]
      exact h ⟨P.1, hP⟩ (Set.mem_univ _)
    obtain ⟨h₀, hh₀, hdiag⟩ := (mem_levDiag _ _ _).mp hmem
    rw [rowTyG_PsymF_H] at hh₀
    have hr : B.R.r = B.R.k + 2 * B.R.rS + 1 := by
      simp only [Formalism.BasicNotions.Ranks.rS, Formalism.BasicNotions.Ranks.r]
      obtain ⟨s, hs⟩ := B.R.m_even
      have := B.R.two_le_m
      omega
    have hsym : rSym B.R.k B.R.rS = B.R.r := by rw [hr]; rfl

    have hJ := (mem_HJsym_iff_JSymG (𝓞 B.fields.E ⧸ P.1.asIdeal) (B.R.N B.R.m - 1) B.R.k B.R.r B.R.t B.R.m B.R.rS
      (r_le_X' B.R) hr B.R.t_odd.pos (rank_X'_eq B.R) h₀⁻¹).mp (Subgroup.inv_mem _ hh₀)

    obtain ⟨j, hj⟩ := redGL_surjective (E := B.fields.E) (n := B.R.N B.R.m - 1) P.1 h₀⁻¹
    have hjinv : redGL _ P.1 j⁻¹ = h₀ := by rw [map_inv, hj, inv_inv]
    have hlev : j.1 ∈ GlobalTheory.TwU.rowLevTop (B.primes X) B.R (I.cst a).sharp (B.R.N B.R.m) P.1 := by
      have h := GlobalTheory.Mem.LastGrp.mem_JGsym0 (fun x hx h0 => intAt_div_of_redP hq hx h0)
        (hsym.symm ▸ r_le_X' B.R) j
        (fun x y hxy => by rw [← redGL_val, hj]; exact hJ.1.1 x y hxy)
        (fun x y hxy => by rw [← redGL_val, hjinv]; simpa using hJ.2.1 x y hxy)
        (fun x hx => by rw [← redGL_val, hj]; exact hJ.1.2.1 x hx)
        (fun x y hx hy => by rw [← redGL_val, hj]; exact hJ.1.2.2.1 x y hx hy)
      have e : GlobalTheory.CongLevel.extE 0 j.1 = j.1 := LinearEquiv.ext (GlobalTheory.Mem.LastGrp.extE_zero j.1)
      rw [e, hsym] at h
      simp only [GlobalTheory.TwU.rowLevTop, if_pos hP, hI.sharp a, if_true]
      exact h
    refine ⟨sumE hN j.1 1, sumE hN j.1 1, _, ⟨j.1, hlev, prXpG_sumE hN j.1, atNL_sumE hN j.1, rfl⟩, ⟨?_, ?_, ?_⟩, congE_refl _ _ _⟩
    · rw [← extI_val hN j]
      exact (extI hN P.1 j).2
    · intro h x hx
      rw [← extI_val hN j, redV_redGL _ hx, redGL_extI, hj, ← hdiag, ← map_inv]
    · exact fun h => absurd h hQn
  ·
    have hQ : P.1 ∈ I.Q a := by
      classical
      have h := P.2
      simp only [SBof, rowSG, uSG, Finset.mem_union] at h
      exact h.resolve_left hP
    have hmem : κ.2.2.1 ⟨P.1, hQ⟩ ∈ (levQTop B.R I.sel (I.tup a) (topDep B.R (I.cst a).M) ⟨P.1, hQ⟩).H := by
      have h := κ.2.2.2
      simp only [LevQFam.grp, Subgroup.mem_pi] at h
      rw [← topLev_levQ_m I.Ch I.sel (I.tup a) (I.cst a) I.Ps]
      exact h ⟨P.1, hQ⟩ (Set.mem_univ _)
    simp only [levQTop] at hmem
    obtain ⟨j, hj, hjc⟩ := (mem_levCong _ _ _ _).mp (Subgroup.inv_mem _ hmem)
    have hlev : j.1 ∈ GlobalTheory.TwU.rowLevTop (B.primes X) B.R (I.cst a).sharp (B.R.N B.R.m) P.1 := by
      simp only [GlobalTheory.TwU.rowLevTop, if_neg hP]
      exact GlobalTheory.TopLaw.mem_JQ_of_red hq j ((mem_levRed _ _).mp hj)
    refine ⟨sumE hN j.1 1, ((κ.2.2.1 ⟨P.1, hQ⟩)⁻¹).1, _, ⟨j.1, hlev, prXpG_sumE hN j.1, atNL_sumE hN j.1, rfl⟩,
      ⟨((κ.2.2.1 ⟨P.1, hQ⟩)⁻¹).2, fun h => absurd h hP, fun h => rfl⟩, ?_⟩

    have h2 : (extI hN P.1 j)⁻¹ * (κ.2.2.1 ⟨P.1, hQ⟩)⁻¹ ∈ prinCong _ P.1 (2 * (I.cst a).M) :=
      prinCong_anti (by have := two_mul_le_topDep B.R (I.cst a).M; omega) hjc
    have h3 : ((κ.2.2.1 ⟨P.1, hQ⟩)⁻¹)⁻¹ * extI hN P.1 j ∈ prinCong _ P.1 (2 * (I.cst a).M) := by
      have := Subgroup.inv_mem _ h2
      rwa [_root_.mul_inv_rev, inv_inv] at this
    have h4 := (inv_mul_mem_prinCong _ _ _).mp h3
    intro x hx
    simp only [GlobalTheory.TwU.topDep, if_neg hP]
    have := h4 x hx
    rwa [extI_val] at this

end GlobalTheory.Mem.Col2.AdT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTopStepLevelCongruentBlockSumOneStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_topStep_level_congruent_blockSum_one : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i = B.R.m → ∀ (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (P : SBof I a), ∃ g g' z, GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P g z ∧ LiftsInv I κ P g' ∧ CongE P.1 (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P) g g' := by
  first | exact @GlobalTheory.Mem.Col2.AdT.exists_topLev_liftsInv | exact GlobalTheory.Mem.Col2.AdT.exists_topLev_liftsInv | (intros; apply GlobalTheory.Mem.Col2.AdT.exists_topLev_liftsInv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalConstantWeilCharacterValuesIsIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalConstantWeilCharacterValuesIsIntegral
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT


open Classical in
theorem addChar_isIntegral {A : Type} [AddCommGroup A] [Finite A] {K : Type} [Field K] (ψ : AddChar A K) (y : A) :
    IsIntegral ℤ (ψ y) := by
  refine IsIntegral.of_pow (Nat.card_pos (α := A)) ?_
  rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero', AddChar.map_zero_eq_one]
  exact isIntegral_one

theorem qOf_pos {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : 0 < qOf w := by
  refine Nat.pos_of_ne_zero ?_
  unfold qOf
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact w.ne_bot

theorem ciPsi_isIntegral {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {SB : Finset (HeightOneSpectrum (𝓞 X.E))}
    (P : SB) (x : X.E) : IsIntegral ℤ (ciPsi Ch P x) := by
  classical
  unfold ciPsi
  split
  · have := ciFinite (X := X) (qOf_pos P.1).ne'
    exact addChar_isIntegral _ _
  · exact isIntegral_one

theorem twZeta_pow_eq_one {X : Fields} (σ₀ : X.K →+* ℂ) {N : ℕ} (hN : 0 < N)
    (hex : ∃ z : X.K, σ₀ z = Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))) : twZeta σ₀ N ^ N = 1 := by
  have hs : σ₀ (twZeta σ₀ N) = Complex.exp (2 * Real.pi * Complex.I / (N : ℂ)) := Classical.epsilon_spec hex
  apply σ₀.injective
  rw [map_pow, hs, map_one, ← Complex.exp_nat_mul]
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [show (N : ℂ) * (2 * Real.pi * Complex.I / (N : ℂ)) = 2 * Real.pi * Complex.I by field_simp]
  exact Complex.exp_two_pi_mul_I

theorem twPsiQ_isIntegral {X : Fields} (σ₀ : X.K →+* ℂ) (xi0 : X.E) (P : HeightOneSpectrum (𝓞 X.E)) (D : ℕ)
    (hz : twZeta σ₀ (qOf P ^ D) ^ (qOf P ^ D) = 1) (a : X.E) : IsIntegral ℤ (twPsiQ σ₀ xi0 P D a) := by
  classical
  unfold twPsiQ
  split
  · refine IsIntegral.of_pow (pow_pos (qOf_pos P) D) ?_
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hz, _root_.one_zpow]
    exact isIntegral_one
  · exact isIntegral_one

theorem psi_isIntegral : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → I.IsTw → ∀ (a : I.ι) (P : SBof I a) (x : B.fields.E),
    IsIntegral ℤ ((I.cst a).psi P x) := by
  intro B X I h ht a P x
  rw [ht.cst_eq a]
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · rw [twCst_psi_g hP]
    exact ciPsi_isIntegral _ _ _
  · rw [twCst_psi_Q hP]
    exact twPsiQ_isIntegral _ _ _ _
      (twZeta_pow_eq_one _ (pow_pos (qOf_pos P.1) _) (TC.root_of_ok h ht.deep a P hP)) x

end GlobalTheory.Mem.Col2.AdT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalConstantWeilCharacterValuesIsIntegralStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localConstantWeilCharacter_values_isIntegral : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → I.IsTw → ∀ (a : I.ι) (P : SBof I a) (x : B.fields.E), IsIntegral ℤ ((I.cst a).psi P x) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.psi_isIntegral | exact GlobalTheory.Mem.Col2.AdT.psi_isIntegral | (intros; apply GlobalTheory.Mem.Col2.AdT.psi_isIntegral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeFunctionalsEqMovedLevelFunctionals
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeFunctionalsEqMovedLevelFunctionals
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.FunMv

open GlobalTheory.Mem.Dil GlobalTheory.Mem.Col2.DilPt

section Res

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hasRes_add {P : HeightOneSpectrum (𝓞 E)} {a b : P.adicCompletion E} {c d : 𝓞 E ⧸ P.asIdeal}
    (ha : HasRes P a c) (hb : HasRes P b d) : HasRes P (a + b) (c + d) := by
  obtain ⟨r, rfl, hr⟩ := ha
  obtain ⟨r', rfl, hr'⟩ := hb
  refine ⟨r + r', by rw [map_add (f := _)], ?_⟩
  have e : a + b - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (r + r')) =
      (a - algebraMap E _ (algebraMap (𝓞 E) E r)) + (b - algebraMap E _ (algebraMap (𝓞 E) E r')) := by
    simp only [map_add (f := _)]; ring
  rw [e]
  exact Valuation.map_add_lt _ hr hr'

theorem hasRes_mul {P : HeightOneSpectrum (𝓞 E)} {a b : P.adicCompletion E} {c d : 𝓞 E ⧸ P.asIdeal}
    (ha : HasRes P a c) (hb : HasRes P b d) : HasRes P (a * b) (c * d) := by
  have hale := hasRes_le_one ha
  obtain ⟨r, rfl, hr⟩ := ha
  obtain ⟨r', rfl, hr'⟩ := hb
  refine ⟨r * r', by rw [map_mul], ?_⟩
  have e : a * b - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (r * r')) =
      a * (b - algebraMap E _ (algebraMap (𝓞 E) E r')) + algebraMap E _ (algebraMap (𝓞 E) E r') * (a - algebraMap E _ (algebraMap (𝓞 E) E r)) := by
    simp only [map_mul]; ring
  rw [e]
  refine Valuation.map_add_lt _ ?_ ?_
  · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' hale) hr'
  · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_le_one P r')) hr

theorem hasRes_sum {P : HeightOneSpectrum (𝓞 E)} {ι : Type} (s : Finset ι) (a : ι → P.adicCompletion E) (c : ι → 𝓞 E ⧸ P.asIdeal)
    (h : ∀ j ∈ s, HasRes P (a j) (c j)) : HasRes P (∑ j ∈ s, a j) (∑ j ∈ s, c j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasRes_coe P 0
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact hasRes_add (h j (Finset.mem_insert_self j s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem exists_hasRes [StarRing E] {v : HeightOneSpectrum (𝓞 F)} {P : HeightOneSpectrum (𝓞 E)} (hP : P.under (𝓞 F) = v)
    (x : E ⊗[F] v.adicCompletion F) (hx : Valued.v (psi v P hP x) ≤ 1) : ∃ c, HasRes P (psi v P hP x) c := by
  obtain ⟨z, rfl⟩ : ∃ z, prV (E := E) v z = x := ⟨_, Formalism.UG.P.afsplit_prV_IE v x⟩
  rw [psi_prV] at hx ⊢
  obtain ⟨c, hc⟩ := exists_res P z hx
  exact ⟨_, c, rfl, hc⟩

end Res

end GlobalTheory.Mem.Col2.FunMv

end

noncomputable section

namespace GlobalTheory.Mem.Col2.FunMv

open GlobalTheory.Mem.Dil GlobalTheory.Mem.Col2.DilPt
open scoped TensorProduct

theorem hasRes_last {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (y k : GL (Fin n) (AfE F E)) (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) (hP : P.under (𝓞 F) = v)
    (x : Sp E n) (r : Fin n) (b : 𝓞 E ⧸ P.asIdeal) (cj : Fin n → 𝓞 E ⧸ P.asIdeal)
    (hk : ∀ j, HasRes P (adAt F P ((k⁻¹ : GL (Fin n) (AfE F E)).1 r j)) (if j = r then b else 0))
    (hy : ∀ j, HasRes P (psi v P hP (prV (E := E) v (GlobalTheory.Mem.Col2.pullV y x j))) (cj j)) :
    HasRes P (adAt F P (GlobalTheory.Mem.Col2.pullV (y * k) x r)) (b * cj r) := by
  rw [pullbackVector_mul_right]
  have e1 : adAt F P ((((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ GlobalTheory.Mem.Col2.pullV y x) r) =
      ∑ j, adAt F P ((k⁻¹ : GL (Fin n) (AfE F E)).1 r j) * adAt F P (GlobalTheory.Mem.Col2.pullV y x j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  have e2 : b * cj r = ∑ j, (if j = r then b else 0) * cj j := by
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [e1, e2]
  refine hasRes_sum _ _ _ fun j _ => hasRes_mul (hk j) ?_
  rw [← psi_prV v P hP]
  exact hy j

end GlobalTheory.Mem.Col2.FunMv

end

noncomputable section

namespace GlobalTheory.Mem.Col2.FunMv

open GlobalTheory.Mem.Dil GlobalTheory.Mem.Col2.DilPt
open scoped TensorProduct

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  {hc : Formalism.BasicNotions.CMData F E} {n T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {S : Formalism.L2.Forms.StepLevel F E hc.sig (1 : Matrix (Fin n) (Fin n) E) T f bad}
  {π : 𝓞 E} {P : HeightOneSpectrum (𝓞 E)} {v : HeightOneSpectrum (𝓞 F)}

def resL (hLb : IsBase S π) (hP : P.under (𝓞 F) = v) (h3 : π ∉ (conjPrime₂ P).asIdeal) (r : Fin n) :
    latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb)) →+
      𝓞 E ⧸ P.asIdeal where
  toFun s := Classical.choose (exists_hasRes hP (s.1 r) (val_coord_le hLb hP h3 s.2 r))
  map_zero' := by
    have h := Classical.choose_spec (exists_hasRes hP ((0 : latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb))).1 r) (val_coord_le hLb hP h3 (zero_mem _) r))
    refine h.unique ?_
    have h0 := hasRes_coe P 0
    simpa using h0
  map_add' s t := by
    have hs := Classical.choose_spec (exists_hasRes hP (s.1 r) (val_coord_le hLb hP h3 s.2 r))
    have ht := Classical.choose_spec (exists_hasRes hP (t.1 r) (val_coord_le hLb hP h3 t.2 r))
    have hst := Classical.choose_spec (exists_hasRes hP ((s + t).1 r) (val_coord_le hLb hP h3 (s + t).2 r))
    refine hst.unique ?_
    have e : psi v P hP ((s + t).1 r) = psi v P hP (s.1 r) + psi v P hP (t.1 r) := by
      rw [← map_add (f := _)]; rfl
    rw [e]
    exact hasRes_add hs ht

theorem resL_spec (hLb : IsBase S π) (hP : P.under (𝓞 F) = v) (h3 : π ∉ (conjPrime₂ P).asIdeal) (r : Fin n)
    (s : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb))) :
    HasRes P (psi v P hP (s.1 r)) (resL hLb hP h3 r s) :=
  Classical.choose_spec (exists_hasRes hP (s.1 r) (val_coord_le hLb hP h3 s.2 r))

theorem exists_fun (hLb : IsBase S π) (hv : (T : 𝓞 F) ∈ v.asIdeal) (hP : P.under (𝓞 F) = v)
    (hw : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w = P ∨ w = conjPrime₂ P)
    (h2 : π ∉ P.asIdeal ^ 2) (h3 : π ∉ (conjPrime₂ P).asIdeal)
    (hk : ∀ t t' : latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb)),
      t'.1 = Formalism.UG.inclE (F := F) (v.adicCompletion F) (π : E) • t.1 → S.fT v hv t' = 0)
    (hT : T.Prime) (hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = T) (r : Fin n) (hr : r.1 + 1 = n) :
    ∃ ι₀ : S.fM v hv →+ 𝓞 E ⧸ P.asIdeal, ∀ s c, HasRes P (psi v P hP (s.1 r)) c → ι₀ (S.fT v hv s) = c := by
  classical
  set ψ := resL hLb hP h3 r with hψ
  have hle : ∀ x, ψ x = 0 → S.fT v hv x = 0 := fun x hx => by
    have h := resL_spec hLb hP h3 r x
    rw [← hψ, hx] at h
    exact fT_kill hLb hv hP hw h2 h3 hk r hr x (hasRes_lt_one h)
  have hne : ∃ a, (S.fT v hv).toAddMonoidHom a ≠ 0 := by
    by_contra H
    push_neg at H
    exact S.fT_ne v hv (LinearMap.ext H)
  have hker : ∀ x, S.fT v hv x = 0 → ψ x = 0 := fun x hx =>
    GlobalTheory.Mem.Col2.Reside.ker_of_prime (S.fT v hv).toAddMonoidHom ψ (hcard ▸ hT) hne hle x hx
  have hsurj : Function.Surjective (S.fT v hv) := by
    haveI : Fact (Nat.card (S.fM v hv)).Prime := ⟨(S.fM_card v hv).symm ▸ hT⟩
    rcases AddSubgroup.eq_bot_or_eq_top_of_prime_card (S.fT v hv).toAddMonoidHom.range with h | h
    · exfalso
      obtain ⟨a, ha⟩ := hne
      have : (S.fT v hv).toAddMonoidHom a ∈ (S.fT v hv).toAddMonoidHom.range := ⟨a, rfl⟩
      rw [h] at this
      exact ha this
    · intro m
      have : m ∈ (S.fT v hv).toAddMonoidHom.range := by rw [h]; trivial
      obtain ⟨a, ha⟩ := this
      exact ⟨a, ha⟩
  let g := Function.surjInv hsurj
  have hg : ∀ m, S.fT v hv (g m) = m := Function.surjInv_eq hsurj
  refine ⟨{ toFun := fun m => ψ (g m), map_zero' := ?_, map_add' := ?_ }, fun s c hc => ?_⟩
  · refine hker _ ?_
    rw [hg]
  · intro m m'
    rw [← sub_eq_zero, ← map_add (f := _), ← map_sub]
    refine hker _ ?_
    rw [map_sub, map_add (f := _), hg, hg, hg, sub_self]
  · show ψ (g (S.fT v hv s)) = c
    have e : ψ (g (S.fT v hv s)) = ψ s := by
      rw [← sub_eq_zero, ← map_sub]
      refine hker _ ?_
      rw [map_sub, hg, sub_self]
    rw [e]
    exact (resL_spec hLb hP h3 r s).unique hc

end Loc

end GlobalTheory.Mem.Col2.FunMv

end

noncomputable section

namespace GlobalTheory.Mem.Col2.FunMv

open GlobalTheory.Mem.Dil GlobalTheory.Mem.Col2.DilPt
open scoped TensorProduct

theorem exists_fun' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : Formalism.BasicNotions.CMData F E) {n T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1)
    (S : Formalism.L2.Forms.StepLevel F E hc.sig J T f bad) (π : 𝓞 E) (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    (hLb : ∀ x, x ∈ S.Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → π ∣ r))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) (hP : P.under (𝓞 F) = v)
    (hw : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w = P ∨ w = conjPrime₂ P)
    (h2 : π ∉ P.asIdeal ^ 2) (h3 : π ∉ (conjPrime₂ P).asIdeal)
    (hk : ∀ t t' : latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J S.Lb)),
      t'.1 = Formalism.UG.inclE (F := F) (v.adicCompletion F) (π : E) • t.1 → S.fT v hv t' = 0)
    (hT : T.Prime) (hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = T) (r : Fin n) (hr : r.1 + 1 = n) :
    ∃ ι₀ : S.fM v hv →+ 𝓞 E ⧸ P.asIdeal, (∀ s c, HasRes P (psi v P hP (s.1 r)) c → ι₀ (S.fT v hv s) = c) ∧
      ∀ (s : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J S.Lb))) (j : Fin n),
        ∃ c, HasRes P (psi v P hP (s.1 j)) c := by
  subst hJ
  obtain ⟨ι₀, h⟩ := exists_fun (S := S) hLb hv hP hw h2 h3 hk hT hcard r hr
  exact ⟨ι₀, h, fun s j => exists_hasRes hP (s.1 j) (val_coord_le (S := S) hLb hP h3 s.2 j)⟩

end GlobalTheory.Mem.Col2.FunMv

end


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Mem.Col2.TC.funMoved_charts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ β : Ch, FunKilled (K β).lev (X.piT u) → ∀ (P : (B.primes X).vT u) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∃ ι : (K β).lev.fM v h →+ 𝓞 B.fields.E ⧸ P.1.asIdeal, ∀ c, chOf c = β → GlobalTheory.TwU.FunMoved (sm I l Z) (K β).lev P v h ι ((K (chOf c)).y ⟨c, rfl⟩).1 ((I.stp u a i).rep c).1.1.deco.1 := by
  intro B X I hI hPins l Z u a i hi bad Ch chOf K k hR β hkill P v h hov
  classical
  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  have hPr := l.pr
  have hgr := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hPins l Z).2.2.2 i hi).1
  have hsP : GlobalTheory.TwU.seamP (sm I l Z) P.1 = P.1 := by
    ext x
    exact TwU.mem_seamP (sm I l Z) P.1 x
  rw [hsP] at hov
  have hPv : P.1.under (𝓞 B.host.F) = v := by
    unfold IsOver at hov
    exact HeightOneSpectrum.ext hov.symm
  have hw : ∀ w : HeightOneSpectrum (𝓞 B.host.E), w.under (𝓞 B.host.F) = v → w = P.1 ∨ w = conjPrime₂ P.1 := fun w hw' =>
    (under_eq_iff B.host P.1 w).1 (hw'.trans hPv.symm)
  have hcard : Nat.card (𝓞 B.host.E ⧸ P.1.asIdeal) = B.T u := by
    have e := hPr.vT_norm u P.1 P.2
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at e
    exact e
  have hN : 0 < B.R.N i := B.R.N_pos i
  let r : Fin (B.R.N i) := ⟨B.R.N i - 1, by omega⟩
  have hr : r.1 + 1 = B.R.N i := by show B.R.N i - 1 + 1 = _; omega
  obtain ⟨ι₀, hι₀, hres⟩ := GlobalTheory.Mem.Col2.FunMv.exists_fun' B.sp.cm hgr (K β).lev (X.piT u) P.1 v (fun x => hR.lb β x) h hPv hw
    (hPr.piT_notMem_sq hX u P.2) (conj_piT_notMem hPr u P) (hkill v h) (hPr.T_prime u) hcard r hr
  refine ⟨(AddMonoidHom.mulLeft (Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)))).comp ι₀, fun c hc => ?_⟩
  subst hc
  intro w hw' z hz
  choose cj hcj using hres z
  have hf := (hR.pt c).f P w hw' r hr
  have hsum := GlobalTheory.Mem.Col2.FunMv.hasRes_last (((K (chOf c)).y ⟨c, rfl⟩).1 : GA B (B.R.N i)) (k (chOf c)) v P.1 hPv w r _ cj (fun j => hR.k_T (chOf c) P r j hr)
    (fun j => by have := hcj j; rw [hz] at this; exact this)
  refine (hf.unique hsum).trans ?_
  show _ = Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) * ι₀ ((K (chOf c)).lev.fT v h z)
  exact congrArg _ (hι₀ z (cj r) (hcj r)).symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeFunctionalsEqMovedLevelFunctionalsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrimeFunctionals_eq_moved_level_functionals : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ β : Ch, FunKilled (K β).lev (X.piT u) → ∀ (P : (B.primes X).vT u) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∃ ι : (K β).lev.fM v h →+ 𝓞 B.fields.E ⧸ P.1.asIdeal, ∀ c, chOf c = β → GlobalTheory.TwU.FunMoved (sm I l Z) (K β).lev P v h ι ((K (chOf c)).y ⟨c, rfl⟩).1 ((I.stp u a i).rep c).1.1.deco.1 := by
  first | exact @GlobalTheory.Mem.Col2.TC.funMoved_charts | exact GlobalTheory.Mem.Col2.TC.funMoved_charts | (intros; apply GlobalTheory.Mem.Col2.TC.funMoved_charts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnKernelDataCompatibleStepCharts
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000

noncomputable section
namespace GlobalTheory.Mem.Col2.AdT

section Lev
variable {B : Base} {X : PreX B.toPre} {I : TC B X} (hOk : I.Ok) (hP : TC.Pins B X) {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι} {i : ℕ} {hi : i ≤ B.R.m}
  {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))} {Ch : Type} {chOf : (I.stp u a i).Cl → Ch} {K : Charts I l Z u a i hi bad chOf} {k : Ch → GA B (B.R.N i)}
  (hR : ReadsAt I l Z K k) (c : (I.stp u a i).Cl) {fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E} (hfb : FrNear I l Z a (k (chOf c)) fb)
  (hfin : ChiFin I l Z (K (chOf c)).lev)
  {dep : SBof I a → ℕ} {Rel : SBof I a → (Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) → B.fields.K → Prop}


include hOk hP hR hfb hfin in
theorem locLe_of (hd : ∀ P, dep P ≤ (I.cst a).D P)
    (h : ∀ κ : (I.stp u a i).G c.1, Keeps I κ ((I.stp u a i).rep c) → ∀ P, ∃ g g' z, Rel P g z ∧ LiftsInv I κ P g' ∧ CongE P.1 (dep P) g g') :
    GlobalTheory.TwU.LocLe (sm I l Z) (K (chOf c)).lev fb dep Rel := by
  intro P v hv κ hκ hU
  obtain ⟨x, hx, hxκ⟩ := GlobalTheory.T.local_group_element_eq_level_component_bad_prime I hOk l Z a (B.T u) i hi bad (K (chOf c)).lev P v hv κ hκ hU
  obtain ⟨κ', hk, -, hin⟩ := GlobalTheory.T.exists_stepGroupElement_of_chartLevel I hOk hP l Z u a i hi bad Ch chOf K k hR c fb hfb hfin ⟨x, hx⟩
  obtain ⟨g, g', z, hg, hl, hc⟩ := h κ' hk P
  exact ⟨g, z, hg, hxκ fb dep g (GlobalTheory.T.rational_automorphism_congruent_near_frame_reading I hOk l Z a i fb _ dep P x g' g hl.1 (hd P) (hin P g' hl) hc)⟩


include hOk hP hR hfb hfin in
theorem chiIs_of (hd : ∀ P, 1 ≤ dep P ∧ dep P ≤ (I.cst a).D P)
    (hex : ∀ (κ : (I.stp u a i).G c.1) P, ∃ g', LiftsInv I κ P g')
    (h : ∀ (κ : (I.stp u a i).G c.1) (g g' : SBof I a → Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : SBof I a → B.fields.K), (∀ P, Rel P (g P) (z P) ∧ LiftsInv I κ P (g' P) ∧ CongE P.1 (dep P) (g P) (g' P)) →
      (((I.stp u a i).chr c.1 κ : B.fields.Kˣ) : B.fields.K) * ∏ P, z P = 1) :
    GlobalTheory.TwU.ChiIs (sm I l Z) (K (chOf c)).lev fb dep Rel := by
  intro κ g z hg
  obtain ⟨κ', -, hχ, hin⟩ := GlobalTheory.T.exists_stepGroupElement_of_chartLevel I hOk hP l Z u a i hi bad Ch chOf K k hR c fb hfb hfin κ
  choose g' hg' using hex κ'
  have e := h κ' g g' z fun P => ⟨(hg P).1, hg' P,
    GlobalTheory.T.rational_automorphisms_near_same_adelic_congruent I hOk l Z a i fb _ dep P κ.1 (g' P) (g P) (hg' P).1 (hd P).1 (hd P).2 (hin P _ (hg' P)) (hg P).2⟩
  rw [hχ]
  exact (map_mul B.embLL _ _).symm.trans ((congrArg B.embLL e).trans (map_one _))


include hOk hP hR hfb hfin in
theorem lev_mid (hm : i < B.R.m) (y0 : SBof I a → Sp B.fields.E (B.R.N i))
    (hy0 : i + 1 = B.R.m → ∀ P, y0 P ∈ cosetIn ((I.stp u a i).rep c) P)
    (hRel : ∀ P g z, Rel P g z ↔ MidAt I hm c.1 P g z ∧ (i + 1 = B.R.m → GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P (g (y0 P)) (y0 P))) :
    GlobalTheory.TwU.LocLe (sm I l Z) (K (chOf c)).lev fb (I.cst a).D Rel ∧ GlobalTheory.TwU.LocGe (sm I l Z) (K (chOf c)).lev fb (I.cst a).D Rel ∧
      GlobalTheory.TwU.ChiIs (sm I l Z) (K (chOf c)).lev fb (I.cst a).D Rel := by
  refine ⟨locLe_of hOk hP hR c hfb hfin (fun _ => le_rfl) fun κ hκ P => ?_, ?_,
    chiIs_of hOk hP hR c hfb hfin (fun P => ⟨(hOk.idx_ok a).cst_ok.D_pos P, le_rfl⟩) (fun κ P => ?_) fun κ g g' z h => ?_⟩
  · obtain ⟨g, z, hg, hl⟩ := GlobalTheory.T.exists_middleStep_level_inverse_lifts I hOk u a i hm c.1 κ P
    refine ⟨g, g, z, (hRel P g z).2 ⟨hg, fun h1 => ?_⟩, hl, congE_refl _ _ _⟩
    have h2 := (GlobalTheory.T.couplingCosetInFrames_preimage_under_lift I hOk u a i c.1 κ _ P g hκ.1 hl (y0 P)).1 (by rw [hκ.2]; exact hy0 h1 P)
    exact ((((GlobalTheory.T.couplingCosetInFrames_shape_at_bad_prime I hOk u a i _ P).2 h1).2.2 _ (hy0 h1 P)).1 _).1 h2
  · rintro P v hv κ hκ ⟨g, z, hg, hin⟩
    obtain ⟨hg1, hg2⟩ := (hRel P g z).1 hg
    obtain ⟨hint, hc⟩ := GlobalTheory.T.congruent_automorphisms_lift_step_group_elements I hOk u a i hm c.1 P g z hg1
    refine GlobalTheory.T.stepNearLifts_component_mem_localChartGroup I hOk hP l Z u a i hi bad Ch chOf K k hR c fb hfb P v hv κ hκ g hint hin fun g' hg' hgg => ?_
    obtain ⟨κ', e1, e2, e3⟩ := hc g' hg' hgg
    refine ⟨κ', ⟨e1, funext fun P' => Set.ext fun z' => ?_⟩, e2, e3⟩
    by_cases hPP : P' = P
    · subst hPP
      rw [GlobalTheory.T.couplingCosetInFrames_preimage_under_lift I hOk u a i c.1 κ' _ P' g' e1 e2 z']
      by_cases h1 : i + 1 = B.R.m
      · exact (((GlobalTheory.T.couplingCosetInFrames_shape_at_bad_prime I hOk u a i _ P').2 h1).2.2 _ (hy0 h1 P')).2 g g' hg' hgg (hg2 h1) z'
      · rw [(GlobalTheory.T.couplingCosetInFrames_shape_at_bad_prime I hOk u a i _ P').1 h1]
        exact Iff.rfl
    · exact GlobalTheory.T.couplingCosetInFrames_preimage_under_lift I hOk u a i c.1 κ' _ P' 1 e1 (e3 P' hPP) z'
  · obtain ⟨g, z, -, hl⟩ := GlobalTheory.T.exists_middleStep_level_inverse_lifts I hOk u a i hm c.1 κ P
    exact ⟨g, hl⟩
  · exact GlobalTheory.T.step_group_character_inverse_type_at_lifts I hOk u a i hm c.1 κ g g' z fun P => ⟨((hRel P _ _).1 (h P).1).1, (h P).2⟩


include hOk hP hR hfb hfin in
theorem lev_top (hm : i = B.R.m) :
    GlobalTheory.TwU.LocLe (sm I l Z) (K (chOf c)).lev fb (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a)) (GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i) ∧
      GlobalTheory.TwU.ChiIs (sm I l Z) (K (chOf c)).lev fb (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a)) (GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i) := by
  have hd : ∀ P, 1 ≤ GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P ∧ GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P ≤ (I.cst a).D P := fun P => by
    unfold GlobalTheory.TwU.topDep
    have h1 := (hOk.idx_ok a).cst_ok.M_pos
    split_ifs with h
    · exact ⟨le_rfl, (hOk.idx_ok a).cst_ok.D_pos P⟩
    · exact ⟨by omega, (hOk.idx_ok a).depthQ P h⟩
  refine ⟨locLe_of hOk hP hR c hfb hfin (fun P => (hd P).2) fun κ _ P => GlobalTheory.T.exists_topStep_level_congruent_blockSum_one I hOk u a i hm c.1 κ P,
    chiIs_of hOk hP hR c hfb hfin hd (fun κ P => ?_) fun κ g g' z h => GlobalTheory.T.last_step_character_inverse_type_at_lifts I hOk u a i hm c.1 κ g g' z h⟩
  obtain ⟨g, g', z, -, hl, -⟩ := GlobalTheory.T.exists_topStep_level_congruent_blockSum_one I hOk u a i hm c.1 κ P
  exact ⟨g', hl⟩

end Lev


set_option maxHeartbeats 4000000 in
theorem adTie_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (u : B.Word) (a : I.ι) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : ∀ i, i ≤ B.R.m → Type) (chOf : ∀ i hi, (I.stp u a i).Cl → Ch i hi) (eY : ∀ i (hi : i ≤ B.R.m), (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (Kc : ∀ i hi (β : Ch i hi), LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf i hi c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (dt : Formalism.L2.Herm.unitaryOneFiniteAdeles (I.rec7 l Z).sp.cm →* (I.rec7 l Z).Dt), I.IsTw → I.StdKer l Z t → GlobalTheory.Pdv.StdRd I l Z t → (∀ (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i), (t.rd u a).pin i c ↔ (i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1)) → ex.errX.piT = X.piT → I.StdDt l Z dt → (∀ v ∈ bad, v ∈ badG (I.rec7 l Z) ∨ I.UnderQ a v) → (∀ i hi, I.ReadsK l Z u a i hi (chOf i hi) (Kc i hi) ∧ I.IdY l Z u a i hi (eY i hi)) → (∀ i hi β, FunKilled (Kc i hi β).lev (X.piT u)) → (∀ i hi β, ∃ n : ℕ, 0 < n ∧ ∀ κ : (Kc i hi β).lev.U, (∀ v ∈ badG (I.rec7 l Z), bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (Kc i hi β).lev.chi κ ^ n = 1) → (a ≠ I.mu0 → ∀ i hi c (y : Formalism.L2.Herm.unitaryOneFiniteAdeles (I.rec7 l Z).sp.cm), Matrix.GeneralLinearGroup.det y.1 = Matrix.GeneralLinearGroup.det ((Kc i hi (chOf i hi c)).y ⟨c, rfl⟩).1 → detPt B.host I.SQ ((I.stp u a i).rep c).1.1 = dt y) → ∃ A : GlobalTheory.TwU.AdData t u a (fun i hi => ⟨B.T u, bad, eY i hi, Ch i hi, chOf i hi, fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c), Kc i hi⟩), GlobalTheory.TwU.AdPins A dt ∧ GlobalTheory.TwU.AdTie A dt (B.fields.conjO (X.piT u)) := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t u a bad Ch chOf eY Kc dt hTw hSK hRd hPin hX hDt hbad hRK hFun hFin hDet
  have hch : t.ChTie := (GlobalTheory.T.kernelChoices_standard_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex t ⟨hSK.X_eq, hSK.seam, hSK.Pr, hSK.Ch, hSK.sel, hSK.S, hSK.word, hSK.tup,
    hSK.cst, hSK.idx, hSK.m2, hSK.glob, hSK.amb, hSK.δ, hSK.O⟩ hX).1
  rcases t with ⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, Xf, seam, seam_ok, Pr, pr_ok, g_rec, Ch', sel, S, word, T_rec, tup, Q_rec, cst, idx, m2, glob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf, kf_un, served⟩
  obtain ⟨hXf, hseam, hPr, hCh, hsel, hSS, hword, htup, hcst, hidx, hm2, hglob, hamb, hδ, hO⟩ := hSK
  dsimp only at hXf hseam hPr hCh hsel hSS hword htup hcst hidx hm2 hglob hamb hδ hO
  subst hXf
  cases hseam
  cases hPr
  cases hCh
  cases hsel
  subst hSS
  cases htup
  cases hcst
  cases hidx
  subst hm2
  cases hglob
  cases hword
  obtain ⟨r, hr, hN, hXi⟩ := hRd u a
  obtain rfl : rd u a = r := eq_of_heq hr
  have hm : B.R.m = B.R.m - 2 + 2 := hOk.hm
  choose k hk using fun i hi => (hRK i hi).1
  choose sc hsc using fun i hi => (hk i hi).onto
  choose fb hfb using fun i hi (β : Ch i hi) => GlobalTheory.T.exists_rational_frames_near_adelic_at_bad_primes I hOk l Z a (B.R.N i) (k i hi β)
  have hm1 : B.R.m - 2 + 1 ≤ B.R.m := by omega
  choose y0 hy0 using fun (β : Ch _ hm1) (P : SBof I a) => ((GlobalTheory.T.couplingCosetInFrames_shape_at_bad_prime I hOk u a _ ((I.stp u a _).rep (sc _ hm1 β)) P).2 (by omega)).1
  have hkey : ∀ i hi c, (sc i hi (chOf i hi c)).1 = c.1 ∧ cosetIn ((I.stp u a i).rep (sc i hi (chOf i hi c))) = cosetIn ((I.stp u a i).rep c) :=
    fun i hi c => ((hk i hi).key _ _).1 (hsc i hi _)
  have hm3 : B.R.m - 2 + 1 + 1 = B.R.m := by omega
  have hib : ∀ i (hi : i < B.R.m) c, Idx.get c.1 hi = Idx.get (sc i hi.le (chOf i hi.le c)).1 hi := fun i hi c => by rw [(hkey i hi.le c).1]
  have hcrd := (spaces_in_coordinates I hOk hP l Z).2.2.2
  have hdt : ∀ x, dt x = FullDt.u1Dt B.host I.SQ x := fun x => by
    obtain ⟨b, hb⟩ := FullDt.exists_lift B.host x
    exact (hDt x b hb).trans (FullDt.normOneFiniteAdeleDetClass_of_isDetLift B.host I.SQ x b hb).symm
  refine ⟨{ crd := fun _ _ => 1
            iA := RingEquiv.refl _
            q := (QuotientGroup.mk' (KDq B.host I.SQ)).comp (finIdele (afIso B.host.F B.host.E))
            pt := fun i _ c => ((I.stp u a i).rep c).1.1
            yb := fun c => ((I.stp u a _).rep c).1.2
            ib := fun i hi β => Idx.get (sc i hi.le β).1 hi
            fb := fb
            y0 := y0 }, ?_, ?_⟩
  · refine ⟨(GlobalTheory.T.base_fields_definite_laws B).1, hOk.sel_ok, ⟨hOk.g_mem, hOk.T_mem u⟩, hch, hOk.ch_tied.mu0, GlobalTheory.T.localConstantWeilCharacter_values_isIntegral I hOk hTw a, fun _ => rfl, fun _ => Iff.rfl,
      ⟨fun y => ?_, fun k z hz => ?_⟩, fun x y hxy => ?_, fun ι hι j b x hb hx => ?_, fun h => ?_,
      fun μ _ _ => ⟨tildeQ B.host I.SQ (I.xi μ), fun x => ?_, fun u => ?_⟩, fun i hi => ?_, fun i hi y τ => ?_⟩
    · obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective (show DtQ B.host I.SQ from y)
      exact ⟨finAf B.host.F B.host.E a, mk_eq_of_snd_eq B.host I.SQ (afIso_finAf B.host.F B.host.E a)⟩
    · have hz' : (show B.host.E from z.1) * B.host.conj (k : B.host.E) = k := hz
      show (QuotientGroup.mk (finIdele (afIso B.host.F B.host.E) (ratId B.host.F B.host.E k)) : DtQ B.host I.SQ) = e1Q B.host I.SQ z
      rw [← isUnitaryPointsMap_unitaryRationalPointsFiner B.host I.SQ k z hz']
      refine mk_eq_of_snd_eq B.host I.SQ ?_
      show afIso B.host.F B.host.E ((k : B.host.E) ⊗ₜ[B.host.F] 1) = _
      rw [afIso_tmul_one]
      rfl
    · refine (hDt y (finIdele (afIso B.host.F B.host.E) x) ?_).symm
      have e : finAf B.host.F B.host.E (finIdele (afIso B.host.F B.host.E) x) = x :=
        Units.ext ((afIso B.host.F B.host.E).injective (afIso_finAf B.host.F B.host.E _))
      unfold IsDetLift
      rw [e]
      exact hxy.symm
    · show muTilQ B.host I.SQ I.C.mu0 (j.1 + 1) (QuotientGroup.mk (finIdele (afIso B.host.F B.host.E) x)) = _
      have e : (QuotientGroup.mk (finIdele (afIso B.host.F B.host.E) x) : DtQ B.host I.SQ) = QuotientGroup.mk b :=
        mk_eq_of_snd_eq B.host I.SQ ((GlobalTheory.T.finiteAdeleFieldIdentification_eq_baseChangeRingEquiv _ _ ι hι x).symm.trans hx)
      rw [e, muTilQ_succ B.host I.SQ I.C.mu0 j, tildeQ_mk B.host I.SQ (reference_characters_factor_tame I.SQ I.C j), finPartI_eq_self hb]
      rfl
    · obtain rfl : a = I.mu0 := h
      refine ⟨I.trueColumn_tuple_trivial_eq_one, ?_⟩
      show (O u I.mu0).mt = _
      rw [hO.mt u I.mu0, l.xi0, tildeQ_one]
      funext j
      split_ifs
      · exact mul_one _
      · rfl
    · have hk : KDq B.host I.SQ ≤ ((I.xi μ).1.comp (finPartI B.host.E)).ker :=
        (KDq_anti B.host (I.Q_subset_SQ μ)).trans ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hOk).2.2 μ).1
      show tildeQ B.host I.SQ (I.xi μ) (QuotientGroup.mk (finIdele (afIso B.host.F B.host.E) x)) = _
      rw [tildeQ_mk B.host I.SQ hk, finPartI_eq_self fun _ => rfl]
      exact Units.ext ((hOk.xi_reads μ).apply _ x rfl)
    · exact hO.mt u μ
    · rw [(hcrd i hi).1]
      simp [cT]
    · show (O u a).frm i y τ = _
      have e1 : Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) (1 : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) τ = 1 :=
        Matrix.map_one _ (map_zero _) (map_one _)
      refine (congrFun ((hO.frm u a i y).trans ((hRK i hi).2 y).symm) τ).trans ?_
      exact ((congrArg (· * (eY i hi y).1 τ) e1).trans (one_mul _)).symm
  · have hmov : ∀ {n : ℕ} (y : GL (Fin n) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)), GlobalTheory.TwU.ratA (I.rec7 l Z).host.F 1 * y = y := fun y => by
      rw [map_one, one_mul]
    refine ⟨⟨fun i _ c => hN i c, fun c => PtAt.mem_ybSet _ hm3, fun i hi c c' x => ?_, fun c c' x => ?_, ⟨fun c => hN _ c, fun c c' x => ?_⟩,
      fun i hi c => (hPin u a i c).2 (Or.inl (by have : i ≤ B.R.m - 2 + 1 := hi; omega)), fun c' => (hPin u a _ c').trans (or_iff_right (by show ¬ B.R.m - 2 + 1 + 1 + 1 ≤ B.R.m; omega))⟩,
      fun _ _ => rfl, fun _ _ v hv => GlobalTheory.T.exists_badPrime_over_bad_place_of_chain I hOk l Z a v (hbad v hv), fun i hi c => ?_, fun i hi c P => ?_, fun i hi β P v h hv => ?_,
      fun c y hy P => ?_, fun i hi hi2 β => ?_, fun β => ?_, fun β => ?_, fun i hi c y hy => ?_, ?_⟩
    · have hi' : i < B.R.m - 2 := hi
      refine (hXi i (by omega) c c' x).trans ?_
      rw [xiAt_entry I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega) (Idx.some_get _ (by omega)).symm (Idx.some_get _ (by omega)).symm]
      exact congrArg₂ (fun al be => B.embLL (XiEntry I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) i al be _ _ x)) (hib i _ c) (hib (i + 1) _ c')
    · refine (hXi (B.R.m - 2) (by omega) c c' x).trans ?_
      rw [xiAt_penultimate_eq_xiCpl1 I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega) (Idx.some_get _ (by omega)).symm]
      exact congrArg (fun al => B.embLL (XiCpl1 I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (B.R.m - 2) al _ _ _ x)) (hib (B.R.m - 2) _ c)
    · refine (hXi (B.R.m - 2 + 1) (by omega) c c' x).trans ?_
      rw [xiAt_last I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega : B.R.m - 2 + 1 + 1 = B.R.m), xiOver_eq_topG]
      rfl
    · exact (seamOf_lat _ _ _ _ _ _ _ _).trans ((hN i c).trans (GlobalTheory.T.representativeLattice_eq_companion_of_adelicRep I hOk hP l Z u a i hi bad _ _ _ _ (hk i hi) c))
    · have h := GlobalTheory.T.chart_reads_at_class_GL I hOk hP l Z u a i hi bad _ _ _ _ (hk i hi) c _ (hfb i hi _) P
      rw [← hmov ((Kc i hi (chOf i hi c)).y ⟨c, rfl⟩).1] at h
      exact h
    · obtain ⟨ι, hι⟩ := GlobalTheory.T.levelPrimeFunctionals_eq_moved_level_functionals I hOk hP l Z u a i hi bad _ _ _ _ (hk i hi) β (hFun i hi β) P v h hv
      refine ⟨ι, fun c hc => ?_⟩
      have h := hι c hc
      rw [← hmov ((Kc i hi (chOf i hi c)).y ⟨c, rfl⟩).1] at h
      exact h
    · have h1 := (GlobalTheory.T.couplingCosetInFrames_shape_at_bad_prime I hOk u a _ ((I.stp u a _).rep c) P).2 (show B.R.m - 2 + 1 + 1 = B.R.m by omega)
      have h2 := hy0 (chOf _ hm1 c) P
      rw [(hkey _ hm1 c).2] at h2
      exact ((h1.2.2 _ h2).1 _).1 (h1.2.1 y hy)
    · have hi2' : i ≤ B.R.m - 2 := hi2
      obtain ⟨c, rfl⟩ := (hk i hi.le).onto β
      refine lev_mid hOk hP (hk i hi.le) c (hfb i hi.le _) (hFin i hi.le _) hi (fun _ => 0) (fun h => by omega) fun P g z => ?_
      rw [and_iff_left fun h => by omega, ← (hkey i hi.le c).1]
      exact Iff.rfl
    · obtain ⟨c, rfl⟩ := (hk _ hm1).onto β
      refine lev_mid hOk hP (hk _ hm1) c (hfb _ hm1 _) (hFin _ hm1 _) (by omega) (y0 (chOf _ hm1 c)) (fun _ P => (hkey _ hm1 c).2 ▸ hy0 _ P) fun P g z => ?_
      rw [← (hkey _ hm1 c).1]
      exact and_congr Iff.rfl ⟨fun h _ => h, fun h => h (by omega)⟩
    · have hm2 : B.R.m - 2 + 1 + 1 ≤ B.R.m := by omega
      obtain ⟨c, rfl⟩ := (hk _ hm2).onto β
      exact lev_top hOk hP (hk _ hm2) c (hfb _ hm2 _) (hFin _ hm2 _) (by omega)
    · refine (hO.dt u a i c).trans ?_
      by_cases ha : a = I.mu0
      · subst ha
        exact (FullDt.detPt_of_reads I hOk u i (hk i hi) c y hy).trans (hdt y).symm
      · exact hDet ha i hi c y hy
    · have e := eq_of_heq hamb
      have h := GlobalTheory.T.periodLatticeIdeal_trivial_at_chain_bad_primes I hOk u a χ
      rw [← e] at h
      exact h

end GlobalTheory.Mem.Col2.AdT

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnKernelDataCompatibleStepChartsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumn_kernelData_compatible_stepCharts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (u : B.Word) (a : I.ι) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : ∀ i, i ≤ B.R.m → Type) (chOf : ∀ i hi, (I.stp u a i).Cl → Ch i hi) (eY : ∀ i (hi : i ≤ B.R.m), (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (Kc : ∀ i hi (β : Ch i hi), LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf i hi c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (dt : Formalism.L2.Herm.unitaryOneFiniteAdeles (I.rec7 l Z).sp.cm →* (I.rec7 l Z).Dt), I.IsTw → I.StdKer l Z t → GlobalTheory.Pdv.StdRd I l Z t → (∀ (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i), (t.rd u a).pin i c ↔ (i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1)) → ex.errX.piT = X.piT → I.StdDt l Z dt → (∀ v ∈ bad, v ∈ badG (I.rec7 l Z) ∨ I.UnderQ a v) → (∀ i hi, I.ReadsK l Z u a i hi (chOf i hi) (Kc i hi) ∧ I.IdY l Z u a i hi (eY i hi)) → (∀ i hi β, FunKilled (Kc i hi β).lev (X.piT u)) → (∀ i hi β, ∃ n : ℕ, 0 < n ∧ ∀ κ : (Kc i hi β).lev.U, (∀ v ∈ badG (I.rec7 l Z), bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (Kc i hi β).lev.chi κ ^ n = 1) → (a ≠ I.mu0 → ∀ i hi c (y : Formalism.L2.Herm.unitaryOneFiniteAdeles (I.rec7 l Z).sp.cm), Matrix.GeneralLinearGroup.det y.1 = Matrix.GeneralLinearGroup.det ((Kc i hi (chOf i hi c)).y ⟨c, rfl⟩).1 → detPt B.host I.SQ ((I.stp u a i).rep c).1.1 = dt y) → ∃ A : GlobalTheory.TwU.AdData t u a (fun i hi => ⟨B.T u, bad, eY i hi, Ch i hi, chOf i hi, fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c), Kc i hi⟩), GlobalTheory.TwU.AdPins A dt ∧ GlobalTheory.TwU.AdTie A dt (B.fields.conjO (X.piT u)) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.adTie_true | exact GlobalTheory.Mem.Col2.AdT.adTie_true | (intros; apply GlobalTheory.Mem.Col2.AdT.adTie_true <;> assumption)
end
