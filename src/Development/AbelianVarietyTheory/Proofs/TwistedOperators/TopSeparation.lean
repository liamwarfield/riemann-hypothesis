module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorNegSpaceFrameChangeConjSubst

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactMeetsBesselTopRationalOrbits
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactMeetsBesselTopRationalOrbits
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)

namespace GlobalTheory.BesCover

open GlobalTheory.Per GlobalTheory.Per.Inhab

theorem exists_compact_cover {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} {ρ : ℕ}
    {e : Matrix (Fin B.rank) (Fin ρ) D.host.E} (he : IsIsoSub B e) (hι : HSpace.IsIsomEmb A B ι) (hA : IsAniso A)
    (hnorm : ∀ δ γ, EmbRel B A ι δ γ → ∀ n ∈ NFlag B e, δ * n * δ⁻¹ ∈ NFlag B e)
    {t : GA D A → GA D B} (ht : ∀ h, EmbRel B A ι (t h) h) :
    ∃ Ω : Set (GA D B), IsCompact Ω ∧ ∀ (h : GA D A) (n : NFlag B e), ∃ γ ∈ GQ B, γ * ((n : GA D B) * t h) ∈ Ω := by
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact D A hA
  obtain ⟨K', hK', hcov'⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B _ _ he).1
  obtain ⟨s, hc, hs, hq⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι hι
  obtain ⟨-, -, -, -, _, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain rfl : t = s := funext fun h => (hs h _).1 (ht h)
  refine ⟨(fun q : GA D A × NFlag B e => (q.2 : GA D B) * s q.1) '' (K ×ˢ K'),
    (hK.prod hK').image ((continuous_subtype_val.comp continuous_snd).mul (hc.comp continuous_fst)), fun g n => ?_⟩
  obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov g
  obtain ⟨γ', hγ', k', hk', e⟩ := hcov' ⟨_, hnorm _ γ⁻¹ ((hs _ _).2 rfl) n n.2⟩
  have e' : s γ⁻¹ * n * (s γ⁻¹)⁻¹ = (γ' : GA D B) * k' := congrArg Subtype.val e
  have e1 : (n : GA D B) = s γ * (γ' * k') * (s γ)⁻¹ := by
    rw [← e']; simp only [map_inv, inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  refine ⟨(s γ * γ')⁻¹, inv_mem (mul_mem (hq γ hγ) hγ'), (k, k'), ⟨hk, hk'⟩, ?_⟩
  rw [e1]
  simp only [map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

theorem bplus_cover : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∃ Ω : Set (GA D (G.V (.grid D.R.m 0))), IsCompact Ω ∧ ∀ (h : GA D (G.V (.top 0))) (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e),
      ∃ γ ∈ GQ (G.V (.grid D.R.m 0)), γ * ((n : GA D (G.V (.grid D.R.m 0))) * embTop G h) ∈ Ω := by
  intro D T L sc G W M _
  have hV := G.isV (X := .top 0) (Nat.zero_le _) (fun j e => by cases e)
  have hA : IsAniso (G.V (.top 0)) := GlobalTheory.Per.isAniso_of_posDef hV.sigOK fun τ => by
    rw [hV.sig τ, hV.rank]; simp [Node.neg]
  have hι := (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
  have hs : ∀ h, EmbRel _ _ (G.rowDec 0 (by have := D.R.two_le_m; omega)).ι (embTop G h) h :=
    fun h => (embRel_iff _ h _).2 rfl
  exact exists_compact_cover G.besTop.e_iso hι hA
    (fun δ γ h n hn => (GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop δ γ h n hn).1) hs

end GlobalTheory.BesCover
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactMeetsBesselTopRationalOrbitsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_meets_besselTopRationalOrbits : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∃ Ω : Set (GA D (G.V (.grid D.R.m 0))), IsCompact Ω ∧ ∀ (h : GA D (G.V (.top 0))) (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e),
      ∃ γ ∈ GQ (G.V (.grid D.R.m 0)), γ * ((n : GA D (G.V (.grid D.R.m 0))) * embTop G h) ∈ Ω := by
  first | exact @GlobalTheory.BesCover.bplus_cover | exact GlobalTheory.BesCover.bplus_cover | (intros; apply GlobalTheory.BesCover.bplus_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AtRealPlaceMemUnipotentFlagAdelic
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AtRealPlaceMemUnipotentFlagAdelic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)
open scoped TensorProduct

noncomputable section
open Matrix
open Classical

namespace GlobalTheory.FlagRealUnip

variable {D : D7}

theorem tauE_sig (τ : D.what₂.Tau) (a : D.host.E) :
    tauE D τ (D.sp.cm.sig a) = starRingEnd ℂ (tauE D τ a) :=
  D.sp.cm.cmUnram.2.1 _ a

def single (σ : (D.what₂.Tau → ℂ) →+ AE D) (τ : D.what₂.Tau) : ℂ →+ AE D :=
  σ.comp (AddMonoidHom.single (fun _ : D.what₂.Tau => ℂ) τ)

theorem single_apply (σ : (D.what₂.Tau → ℂ) →+ AE D) (τ : D.what₂.Tau) (c : ℂ) :
    single σ τ c = σ (Pi.single τ c) := rfl

set_option maxHeartbeats 2000000 in
theorem chart_mul_incA {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ)
    (z : D.what₂.Tau → ℂ) (y : D.host.E) :
    σ z * incA D y = σ (fun τ => z τ * tauE D τ y) := by
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · rw [RingHom.map_sub, RingHom.map_mul, hσ.fin, hσ.fin, zero_mul, sub_zero]
  · have hy : θ τ (infPart D (incA D y)) = tauE D τ y := by
      show θ τ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (1 ⊗ₜ y)) = _
      rw [Algebra.TensorProduct.map_tmul, map_one]
      exact (hσ.inf τ).1 y
    have e1 := (infPart D).map_sub (σ z * incA D y) (σ fun τ => z τ * tauE D τ y)
    have e2 := (infPart D).map_mul (σ z) (incA D y)
    have e3 := (θ τ).map_sub (infPart D (σ z * incA D y)) (infPart D (σ fun τ => z τ * tauE D τ y))
    have e4 := (θ τ).map_mul (infPart D (σ z)) (infPart D (incA D y))
    rw [e1, e3, e2, e4, hσ.comp, hσ.comp, hy, sub_self]

theorem single_mul_incA {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ)
    (τ : D.what₂.Tau) (c : ℂ) (y : D.host.E) :
    single σ τ c * incA D y = single σ τ (c * tauE D τ y) := by
  rw [single_apply, single_apply, chart_mul_incA hσ]
  congr 1
  funext τ'
  by_cases h : τ' = τ
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem map_mulVec_single {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ)
    (τ : D.what₂.Tau) {m k : ℕ} (M : Matrix (Fin m) (Fin k) D.host.E) (c : Fin k → ℂ) :
    (M.map (incA D)) *ᵥ (fun j => single σ τ (c j)) = fun i => single σ τ ((M.map (tauE D τ) *ᵥ c) i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, single_mul_incA hσ, mul_comm]

end GlobalTheory.FlagRealUnip

namespace GlobalTheory.FlagRealUnip

variable {D : D7}

theorem subOne_mulVec {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (B : HSp D)
    (τ : D.what₂.Tau) {u : Matrix (Fin B.rank) (Fin B.rank) ℂ} {h : GA D B} (hh : IsAtTau θ B τ u h)
    (x : Fin B.rank → D.host.E) :
    subOne B h *ᵥ ratV x = fun i => single σ τ (((u - 1) *ᵥ fun k => tauE D τ (x k)) i) := by
  funext i
  have hent : ∀ j, subOne B h i j = single σ τ ((u - 1) i j) := fun j => by
    unfold subOne
    rw [Matrix.sub_apply, GlobalTheory.PointAtPlaceHom.entry_eq hσ B τ hh i j, add_sub_cancel_left, Matrix.sub_apply]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, hent, ratV, single_mul_incA hσ, ← map_sum]

theorem conj_gram (B : HSp D) {ρ : ℕ} (e : Matrix (Fin B.rank) (Fin ρ) D.host.E) (τ : D.what₂.Tau) :
    (e.map (tauE D τ))ᴴ * gramAt D B τ =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e * B.gram).map (tauE D τ) := by
  rw [Matrix.map_mul]
  congr 1
  ext k i
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Formalism.UG.cT, Matrix.transpose_apply]
  exact (tauE_sig τ (e i k)).symm

end GlobalTheory.FlagRealUnip

namespace GlobalTheory.FlagRealUnip

theorem atTau_mem_NFlag : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (B : HSp D) {ρ : ℕ} (e : Matrix (Fin B.rank) (Fin ρ) D.host.E) (τ : D.what₂.Tau)
    (u : Matrix (Fin B.rank) (Fin B.rank) ℂ), u ∈ GlobalTheory.RealBessel.unipRad (gramAt D B τ) (e.map (tauE D τ)) →
    atTau θ B τ u ∈ NFlag B e := by
  intro D θ hθ B ρ e τ u hu
  obtain ⟨huU, h1, h2⟩ := hu
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hs := GlobalTheory.PointAtPlaceHom.atTau_spec hθ B τ huU
  refine Subgroup.subset_closure ⟨fun i => ?_, fun x hx => ?_⟩
  · obtain ⟨a, ha0, ha⟩ := h1 i
    refine ⟨fun k => single σ τ (a k), fun j hj => by show single σ τ (a j) = 0; rw [ha0 j hj, map_zero], ?_⟩
    rw [subOne_mulVec hσ B τ hs, map_mulVec_single hσ]
    funext k
    exact congrArg (fun v => single σ τ (v k)) ha
  · obtain ⟨a, ha⟩ := h2 (fun k => tauE D τ (x k)) (by
      rw [conj_gram]
      funext k
      have := RingHom.map_mulVec (tauE D τ) (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e * B.gram) x k
      rw [hx] at this
      exact this.symm.trans (map_zero _))
    refine ⟨fun k => single σ τ (a k), ?_⟩
    rw [subOne_mulVec hσ B τ hs, map_mulVec_single hσ]
    funext k
    exact congrArg (fun v => single σ τ (v k)) ha

end GlobalTheory.FlagRealUnip
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AtRealPlaceMemUnipotentFlagAdelicStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.atRealPlace_mem_unipotentFlag_adelic : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (B : HSp D) {ρ : ℕ} (e : Matrix (Fin B.rank) (Fin ρ) D.host.E) (τ : D.what₂.Tau)
    (u : Matrix (Fin B.rank) (Fin B.rank) ℂ), u ∈ GlobalTheory.RealBessel.unipRad (gramAt D B τ) (e.map (tauE D τ)) →
    atTau θ B τ u ∈ NFlag B e := by
  first | exact @GlobalTheory.FlagRealUnip.atTau_mem_NFlag | exact GlobalTheory.FlagRealUnip.atTau_mem_NFlag | (intros; apply GlobalTheory.FlagRealUnip.atTau_mem_NFlag <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneSimultaneousRightTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneSimultaneousRightTranslate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)
noncomputable section

namespace GlobalTheory.BplusShift

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem embTop_mul (a b : GA D (G.V (.top 0))) : embTop G (a * b) = embTop G a * embTop G b := by
  obtain ⟨s, -, hs, -⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D _ _ _
    (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
  have e : ∀ h, embTop G h = s h := fun h => ((embRel_iff _ h _).1 ((hs h _).2 rfl)).symm
  rw [e, e, e, map_mul]

theorem inner_left (W : G.Weil) (M : Vol G) (hM : M.IsRow) {φ : Fn G (.top 0)} {F : Fn G (.grid D.R.m 0)}
    (hφ : φ ∈ contLeft (G.V (.top 0))) (hF : F ∈ contLeft (G.V (.grid D.R.m 0))) {γ : GA D (G.V (.top 0))}
    (hγ : γ ∈ GQ (G.V (.top 0))) (h : GA D (G.V (.top 0))) :
    ∫ n in M.fdN, besInt W φ F (γ * h) n ∂M.νN = ∫ n in M.fdN, besInt W φ F h n ∂M.νN := by
  obtain ⟨_, _, _, _⟩ := GlobalTheory.Per.Inhab.flag_topology _ G.besTop.e_iso
  obtain ⟨-, -, -, -, _, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.grid D.R.m 0))
  obtain ⟨s, -, hs, hq⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D _ _ _
    (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
  have e : ∀ h, embTop G h = s h := fun h => ((embRel_iff _ h _).1 ((hs h _).2 rfl)).symm
  have r1 := (hs γ (s γ)).2 rfl
  have r2 := (hs γ⁻¹ (s γ)⁻¹).2 (map_inv s _).symm
  have hδ : s γ ∈ GQ (G.V (.grid D.R.m 0)) := hq _ hγ
  let c : NFlag (G.V (.grid D.R.m 0)) G.besTop.e ≃ₜ* NFlag (G.V (.grid D.R.m 0)) G.besTop.e :=
    { toFun := fun n => ⟨s γ * n * (s γ)⁻¹, (GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop _ _ r1 n n.2).1⟩
      invFun := fun n => ⟨(s γ)⁻¹ * n * (s γ)⁻¹⁻¹, (GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop _ _ r2 n n.2).1⟩
      left_inv := fun n => Subtype.ext (by simp [mul_assoc])
      right_inv := fun n => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hc : ∀ n, c n ∈ NFlagQ (G.V (.grid D.R.m 0)) G.besTop.e ↔ n ∈ NFlagQ (G.V (.grid D.R.m 0)) G.besTop.e := fun n => by
    change s γ * n.1 * (s γ)⁻¹ ∈ GQ (G.V (.grid D.R.m 0)) ↔ n.1 ∈ GQ (G.V (.grid D.R.m 0))
    rw [Subgroup.mul_mem_cancel_right _ (inv_mem hδ), Subgroup.mul_mem_cancel_left _ hδ]
  have hl : ∀ γ' ∈ NFlagQ (G.V (.grid D.R.m 0)) G.besTop.e, ∀ n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e,
      besInt W φ F (γ * h) (γ' * n) = besInt W φ F (γ * h) n := fun γ' hγ' n => by
    have hq' := Subgroup.mem_subgroupOf.1 hγ'
    simp only [besInt, Subgroup.coe_mul]
    rw [GlobalTheory.BesselChar.besChar_mul W.ψ G.besTop _ _ γ'.2 n.2, GlobalTheory.BesselChar.besChar_rat W.ψ W.ψ_std.1 G.besTop _ γ'.2 hq',
      one_mul, mul_assoc γ'.1, hF.2 _ hq']
  refine (GlobalTheory.Mem.TrueRecord.integral_aut _ hM.unip.1 hM.unip.2.1 hM.unip.2.2 c hc _ hl).symm.trans ?_
  congr 1
  funext n
  change φ (γ * h) * F ((s γ * n * (s γ)⁻¹) * embTop G (γ * h)) * star (besChar W.ψ G.besTop (s γ * n * (s γ)⁻¹)) =
    φ h * F (n * embTop G h) * star (besChar W.ψ G.besTop n)
  rw [(GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop _ _ r1 n n.2).2, hφ.2 γ hγ h, e, e, map_mul,
    show s γ * n * (s γ)⁻¹ * (s γ * s h) = s γ * (n * s h) by group, hF.2 _ hδ]

end GlobalTheory.BplusShift


open GlobalTheory.BplusShift in
theorem GlobalTheory.BplusShift.bplus_rTr : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∀ φ ∈ contLeft (G.V (.top 0)), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ a : GA D (G.V (.top 0)),
      Bplus W M (rTr _ a φ) (rTr _ (embTop G a) F) = Bplus W M φ F := by
  intro D T L sc G W M hM φ hφ F hF a
  have hshift : ∀ h n, besInt W (rTr _ a φ) (rTr _ (embTop G a) F) h n = besInt W φ F (h * a) n := fun h n => by
    simp only [besInt, rTr]
    rw [embTop_mul, mul_assoc (n : GA D (G.V (.grid D.R.m 0)))]
  simp only [Bplus, hshift]
  obtain ⟨hμ, h𝓕⟩ := hM.top.haar_fund
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))
  haveI := hμ
  haveI : (M.ν (.top 0)).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ _ hμ
  have hmp : MeasurePreserving (· * a) (M.ν (.top 0)) (M.ν (.top 0)) := measurePreserving_mul_right _ a
  have hmp' : MeasurePreserving (· * a⁻¹) (M.ν (.top 0)) (M.ν (.top 0)) := measurePreserving_mul_right _ a⁻¹
  rw [← hmp.setIntegral_image_emb (measurableEmbedding_mulRight a)
    (fun h => ∫ n in M.fdN, besInt W φ F h n ∂M.νN) (M.fd (.top 0)), Set.image_mul_right]
  have hF' : IsFundamentalDomain (GQ (G.V (.top 0))) ((· * a⁻¹) ⁻¹' M.fd (.top 0)) (M.ν (.top 0)) :=
    h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving (e := id) Function.bijective_id
      fun g x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  exact (h𝓕.setIntegral_eq hF' fun γ x => inner_left W M hM hφ hF γ.2 x).symm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneSimultaneousRightTranslateStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselPeriodCorankOne_simultaneous_rightTranslate : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∀ φ ∈ contLeft (G.V (.top 0)), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ a : GA D (G.V (.top 0)),
      Bplus W M (rTr _ a φ) (rTr _ (embTop G a) F) = Bplus W M φ F := by
  first | exact @GlobalTheory.BplusShift.bplus_rTr | exact GlobalTheory.BplusShift.bplus_rTr | (intros; apply GlobalTheory.BplusShift.bplus_rTr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneAdditiveBoundedCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneAdditiveBoundedCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)

noncomputable section

namespace GlobalTheory.BplusLaws

private theorem norm_besChar_eq_one {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1) (d : BesDat A B ι) (n : GA D B) :
    ‖besChar ψ d n‖ = 1 := by
  unfold besChar
  split_ifs with h
  · obtain ⟨a, b, -, -, hv⟩ := h.choose_spec
    rw [hv]
    exact hψ _
  · simp

private theorem coCpt_gridData_V_zero {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) :
    GlobalTheory.Unf.CoCpt (G.V (.top 0)) := by
  have hV := GlobalTheory.FunObj.isV_Xp G
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact (G.V (.top 0)) fun τ =>
    GlobalTheory.DefiniteQuotient.posDef_of_signature (by
      have h1 := hV.sigOK (tauE D τ)
      rw [hV.sig (tauE D τ)] at h1
      exact h1)
  refine ⟨C, hC, fun g => ?_⟩
  obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov g
  exact ⟨γ⁻¹, inv_mem hγ, by rwa [← mul_assoc, inv_mul_cancel, one_mul]⟩

private theorem integrableOn_besInt_of_bounded {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)
    (M : Vol G) (hM : M.IsRow) {φ : GA D (G.V (.top 0)) → ℂ} (hφc : Continuous φ) {Cφ : ℝ}
    (hCφ : ∀ g, ‖φ g‖ ≤ Cφ) (hvol : M.ν (.top 0) (M.fd (.top 0)) < ⊤)
    {F : GA D (G.V (.grid D.R.m 0)) → ℂ} (hFc : Continuous F) {K : ℝ}
    (hK : ∀ h (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e), ‖F ((n : GA D _) * embTop G h)‖ ≤ K) :
    (∀ h, IntegrableOn (besInt W φ F h) M.fdN M.νN) ∧
      IntegrableOn (fun h => ∫ n in M.fdN, besInt W φ F h n ∂M.νN) (M.fd (.top 0)) (M.ν (.top 0)) := by
  have hψ : ∀ x, ‖W.ψ x‖ = 1 := W.ψ_std.1.2.1
  obtain ⟨-, -, hBor, -⟩ := GlobalTheory.Per.Inhab.flag_topology _ G.besTop.e_iso
  haveI := GlobalTheory.Unf.EvalCont.firstCountable_GA (G.V (.top 0))
  have hemb : Continuous (embTop G) :=
    GlobalTheory.Per.Inhab.emb_continuous (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
      (fun h => (GlobalTheory.FunObj.embRel_iff _ h _).2 rfl)
  have hχ : Continuous fun n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e => besChar W.ψ G.besTop (n : GA D _) :=
    GlobalTheory.BesselChar.besChar_continuous _ W.ψ_std.1 _
  have hjoint : Continuous fun q : GA D (G.V (.top 0)) × NFlag (G.V (.grid D.R.m 0)) G.besTop.e =>
      besInt W φ F q.1 q.2 := by
    unfold besInt
    refine ((hφc.comp continuous_fst).mul (hFc.comp ?_)).mul ((hχ.comp continuous_snd).star)
    exact (continuous_subtype_val.comp continuous_snd).mul (hemb.comp continuous_fst)
  have hbd : ∀ h n, ‖besInt W φ F h n‖ ≤ Cφ * K := by
    intro h n
    unfold besInt
    rw [norm_mul, norm_mul, norm_star, norm_besChar_eq_one hψ, mul_one]
    exact mul_le_mul (hCφ h) (hK h n) (norm_nonneg _) (le_trans (norm_nonneg _) (hCφ h))
  have hNlt : M.νN M.fdN < ⊤ := by rw [hM.unip.2.2]; exact ENNReal.one_lt_top
  refine ⟨fun h => Measure.integrableOn_of_bounded hNlt.ne ?_ (ae_of_all _ (hbd h)), ?_⟩
  · exact (hjoint.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · have hT : GlobalTheory.Unf.EvalCont.Tame fun h (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e) => besInt W φ F h n :=
      GlobalTheory.Unf.EvalCont.tame_of_bounded hjoint hbd
    have hcont := GlobalTheory.Unf.EvalCont.Tame.continuous_integral M.νN M.fdN hNlt hT
    exact Measure.integrableOn_of_bounded hvol.ne hcont.aestronglyMeasurable
      (ae_of_all _ fun h => norm_setIntegral_le_of_norm_le_const hNlt fun n _ => hbd h n)

theorem bplus_add_bound : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∀ Ω : Set (GA D (G.V (.grid D.R.m 0))), IsCompact Ω → (∀ (h : GA D (G.V (.top 0))) (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e),
      ∃ γ ∈ GQ (G.V (.grid D.R.m 0)), γ * ((n : GA D (G.V (.grid D.R.m 0))) * embTop G h) ∈ Ω) →
    ∀ φ ∈ contLeft (G.V (.top 0)), ∃ C : ℝ,
      (∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ F' ∈ contLeft (G.V (.grid D.R.m 0)), Bplus W M φ (F + F') = Bplus W M φ F + Bplus W M φ F') ∧
      (∀ φ' ∈ contLeft (G.V (.top 0)), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), Bplus W M (φ + φ') F = Bplus W M φ F + Bplus W M φ' F) ∧
      ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ K : ℝ, (∀ x ∈ Ω, ‖F x‖ ≤ K) → ‖Bplus W M φ F‖ ≤ C * K := by
  intro D T L sc G W M hM Ω hΩc hΩ φ hφ
  have hcpt := coCpt_gridData_V_zero G
  obtain ⟨haar, fund⟩ := GlobalTheory.FunObj.Vol.IsAt.haar_fund hM.top
  have hvol : M.ν (.top 0) (M.fd (.top 0)) < ⊤ := GlobalTheory.Unf.EvalCont.vol_lt_top hcpt ⟨_, _, haar, fund⟩
  have hOrb : ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ K : ℝ, (∀ x ∈ Ω, ‖F x‖ ≤ K) →
      ∀ h (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e), ‖F ((n : GA D _) * embTop G h)‖ ≤ K := by
    intro F hF K hK h n
    obtain ⟨γ, hγ, hmem⟩ := hΩ h n
    rw [← hF.2 γ hγ]
    exact hK _ hmem
  have hconv : ∀ ψ ∈ contLeft (G.V (.top 0)), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)),
      (∀ h, IntegrableOn (besInt W ψ F h) M.fdN M.νN) ∧
        IntegrableOn (fun h => ∫ n in M.fdN, besInt W ψ F h n ∂M.νN) (M.fd (.top 0)) (M.ν (.top 0)) := by
    intro ψ hψ F hF
    obtain ⟨Cψ, hCψ⟩ := GlobalTheory.Unf.EvalCont.bounded_of_contAut hcpt ⟨hψ.2, hψ.1⟩
    obtain ⟨K, hK⟩ := hΩc.exists_bound_of_continuousOn hF.1.continuousOn
    exact integrableOn_besInt_of_bounded W M hM hψ.1 hCψ hvol hF.1 (hOrb F hF K hK)
  obtain ⟨Cφ, hCφ⟩ := GlobalTheory.Unf.EvalCont.bounded_of_contAut hcpt ⟨hφ.2, hφ.1⟩
  refine ⟨Cφ * (M.ν (.top 0)).real (M.fd (.top 0)), ?_, ?_, ?_⟩
  · intro F hF F' hF'
    unfold Bplus
    refine GlobalTheory.Per.Inhab.iterated_add (hconv φ hφ F hF) (hconv φ hφ F' hF') fun h n => ?_
    unfold besInt
    simp only [Pi.add_apply]
    ring
  · intro φ' hφ' F hF
    unfold Bplus
    refine GlobalTheory.Per.Inhab.iterated_add (hconv φ hφ F hF) (hconv φ' hφ' F hF) fun h n => ?_
    unfold besInt
    simp only [Pi.add_apply]
    ring
  · intro F hF K hK
    have hK' := hOrb F hF K hK
    have hNlt : M.νN M.fdN < ⊤ := by rw [hM.unip.2.2]; exact ENNReal.one_lt_top
    have hNr : M.νN.real M.fdN = 1 := by simp [Measure.real, hM.unip.2.2]
    have hbd : ∀ h n, ‖besInt W φ F h n‖ ≤ Cφ * K := by
      intro h n
      unfold besInt
      rw [norm_mul, norm_mul, norm_star, norm_besChar_eq_one W.ψ_std.1.2.1, mul_one]
      exact mul_le_mul (hCφ h) (hK' h n) (norm_nonneg _) (le_trans (norm_nonneg _) (hCφ h))
    unfold Bplus
    calc ‖∫ h in M.fd (.top 0), ∫ n in M.fdN, besInt W φ F h n ∂M.νN ∂M.ν (.top 0)‖
        ≤ (Cφ * K) * (M.ν (.top 0)).real (M.fd (.top 0)) := by
          refine norm_setIntegral_le_of_norm_le_const hvol fun h _ => ?_
          have := norm_setIntegral_le_of_norm_le_const hNlt fun n (_ : n ∈ M.fdN) => hbd h n
          rwa [hNr, mul_one] at this
      _ = Cφ * (M.ν (.top 0)).real (M.fd (.top 0)) * K := by ring

end GlobalTheory.BplusLaws

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneAdditiveBoundedCompactStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselPeriodCorankOne_additive_bounded_compact : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∀ Ω : Set (GA D (G.V (.grid D.R.m 0))), IsCompact Ω → (∀ (h : GA D (G.V (.top 0))) (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e),
      ∃ γ ∈ GQ (G.V (.grid D.R.m 0)), γ * ((n : GA D (G.V (.grid D.R.m 0))) * embTop G h) ∈ Ω) →
    ∀ φ ∈ contLeft (G.V (.top 0)), ∃ C : ℝ,
      (∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ F' ∈ contLeft (G.V (.grid D.R.m 0)), Bplus W M φ (F + F') = Bplus W M φ F + Bplus W M φ F') ∧
      (∀ φ' ∈ contLeft (G.V (.top 0)), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), Bplus W M (φ + φ') F = Bplus W M φ F + Bplus W M φ' F) ∧
      ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ K : ℝ, (∀ x ∈ Ω, ‖F x‖ ≤ K) → ‖Bplus W M φ F‖ ≤ C * K := by
  first | exact @GlobalTheory.BplusLaws.bplus_add_bound | exact GlobalTheory.BplusLaws.bplus_add_bound | (intros; apply GlobalTheory.BplusLaws.bplus_add_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneRightTranslateUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneRightTranslateUnipotent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)

noncomputable section

namespace GlobalTheory.BplusUnip

variable {D : D7}

theorem setIntegral_mul_right {B : HSp D} {ρ : ℕ} {e : Matrix (Fin B.rank) (Fin ρ) D.host.E} (he : IsIsoSub B e)
    {ν : Measure (NFlag B e)} {𝓝 : Set (NFlag B e)} (hN : GlobalTheory.Per.IsUnitN B e ν 𝓝) (f : NFlag B e → ℂ)
    (hf : ∀ γ ∈ NFlagQ B e, ∀ n, f (γ * n) = f n) (y : NFlag B e) :
    ∫ n in 𝓝, f (n * y) ∂ν = ∫ n in 𝓝, f n ∂ν := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag B he
  obtain ⟨u1, u2, u3⟩ := hN
  haveI : DiscreteTopology (NFlagQ B e) := by
    refine DiscreteTopology.of_continuous_injective
      (f := fun γ : NFlagQ B e => (⟨γ.1.1, γ.2⟩ : GQ B)) ?_ ?_
    · exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
    · intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg (fun x : GQ B => (x : GA D B)) hab))
  obtain ⟨K, hK, hcov⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B ρ e he).1
  have hcov' : ∀ x : NFlag B e, ∃ s ∈ NFlagQ B e, s * x ∈ K := fun x => by
    obtain ⟨γ, hγ, k, hk, e⟩ := hcov x
    exact ⟨γ⁻¹, inv_mem hγ, by rw [e, ← mul_assoc, inv_mul_cancel, one_mul]; exact hk⟩
  have hr : ∀ a : NFlag B e, ν.map (· * a) = ν := fun a =>
    Formalism.L2.SG.CovariantRepresentation.haar_map_mul_right_of_lattice ν (NFlagQ B e) hK hcov' a
  have hmp : MeasurePreserving (· * y) ν ν := ⟨measurable_mul_const y, hr y⟩
  have hmp' : MeasurePreserving (· * y⁻¹) ν ν := ⟨measurable_mul_const y⁻¹, hr y⁻¹⟩
  rw [← hmp.setIntegral_image_emb (measurableEmbedding_mulRight y) f 𝓝, Set.image_mul_right]
  have hF : IsFundamentalDomain (NFlagQ B e) ((· * y⁻¹) ⁻¹' 𝓝) ν :=
    u2.preimage_of_equiv hmp'.quasiMeasurePreserving (e := id) Function.bijective_id
      fun g x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  exact (u2.setIntegral_eq hF fun γ x => hf γ γ.2 x).symm

theorem bplus_rTr_unip : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∀ (φ : GA D (G.V (.top 0)) → ℂ), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ u ∈ NFlag (G.V (.grid D.R.m 0)) G.besTop.e,
      Bplus W M φ (rTr _ u F) = besChar W.ψ G.besTop u * Bplus W M φ F := by
  intro D T L sc G W M hM φ F hF u hu
  have hn : ∀ n, ‖besChar W.ψ G.besTop n‖ = 1 := fun n => by
    unfold besChar
    split_ifs with h
    · obtain ⟨a, b, -, -, e⟩ := h.choose_spec
      rw [e]
      exact W.ψ_std.1.2.1 _
    · exact norm_one
  have hu1 : besChar W.ψ G.besTop u * star (besChar W.ψ G.besTop u) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    norm_num
  have inner : ∀ h, ∫ n in M.fdN, besInt W φ (rTr _ u F) h n ∂M.νN =
      besChar W.ψ G.besTop u * ∫ n in M.fdN, besInt W φ F h n ∂M.νN := fun h => by
    have hs : EmbRel _ _ (G.rowDec 0 (by have := D.R.two_le_m; omega)).ι (embTop G h) h := (embRel_iff _ h _).2 rfl
    obtain ⟨hy, hyc⟩ := GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop (embTop G h) h hs u hu
    let y : NFlag (G.V (.grid D.R.m 0)) G.besTop.e := ⟨_, hy⟩
    have hinv : ∀ γ ∈ NFlagQ (G.V (.grid D.R.m 0)) G.besTop.e, ∀ n,
        besInt W φ F h (γ * n) = besInt W φ F h n := fun γ hγ n => by
      have hγQ : (γ : GA D (G.V (.grid D.R.m 0))) ∈ GQ (G.V (.grid D.R.m 0)) := Subgroup.mem_subgroupOf.1 hγ
      simp only [besInt, Subgroup.coe_mul]
      rw [GlobalTheory.BesselChar.besChar_mul W.ψ G.besTop _ _ γ.2 n.2,
        GlobalTheory.BesselChar.besChar_rat W.ψ W.ψ_std.1 G.besTop _ γ.2 hγQ, one_mul, mul_assoc (γ : GA D (G.V (.grid D.R.m 0))) (n : GA D (G.V (.grid D.R.m 0))) (embTop G h),
        hF.2 _ hγQ]
    have hpt : ∀ n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e, besInt W φ (rTr _ u F) h n =
        besChar W.ψ G.besTop u * besInt W φ F h (n * y) := fun n => by
      simp only [besInt, rTr, Subgroup.coe_mul, y]
      rw [GlobalTheory.BesselChar.besChar_mul W.ψ G.besTop _ _ n.2 hy, hyc, star_mul]
      have e1 : (n : GA D (G.V (.grid D.R.m 0))) * (embTop G h * u * (embTop G h)⁻¹) * embTop G h =
          (n : GA D (G.V (.grid D.R.m 0))) * embTop G h * u := by group
      rw [e1]
      linear_combination (-(φ h * F ((n : GA D (G.V (.grid D.R.m 0))) * embTop G h * u) *
        star (besChar W.ψ G.besTop (n : GA D (G.V (.grid D.R.m 0)))))) * hu1
    simp_rw [hpt]
    rw [integral_const_mul, setIntegral_mul_right G.besTop.e_iso hM.unip _ hinv y]
  unfold Bplus
  simp_rw [inner]
  exact integral_const_mul _ _

end GlobalTheory.BplusUnip
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneRightTranslateUnipotentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselPeriodCorankOne_rightTranslate_unipotent : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∀ (φ : GA D (G.V (.top 0)) → ℂ), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ u ∈ NFlag (G.V (.grid D.R.m 0)) G.besTop.e,
      Bplus W M φ (rTr _ u F) = besChar W.ψ G.besTop u * Bplus W M φ F := by
  first | exact @GlobalTheory.BplusUnip.bplus_rTr_unip | exact GlobalTheory.BplusUnip.bplus_rTr_unip | (intros; apply GlobalTheory.BplusUnip.bplus_rTr_unip <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)

noncomputable section

namespace GlobalTheory.SepRows.SepProof

section
open Classical

theorem atTau_mem_GinfC' {D : D7} (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    atTau θ V τ g ∈ GinfC V := by
  unfold atTau; split_ifs with h
  exacts [h.choose_spec.1, one_mem _]

theorem pairVec_comp_rho {D : D7} {V : HSp D} (c : CoefA V) (ξ : Module.Dual ℂ c.W) (Ψ : Bridge.Gf V → c.W) {a : GA D V}
    (ha : a ∈ GinfC V) : pairVec c (ξ ∘ₗ c.ρ a⁻¹) Ψ = rTr V a (pairVec c ξ Ψ) := by
  funext h
  have e : (finHom V).rangeRestrict (h * a) = (finHom V).rangeRestrict h := by
    rw [map_mul]
    have : (finHom V).rangeRestrict a = 1 := Subtype.ext (MonoidHom.mem_ker.1 ha)
    rw [this, mul_one]
  simp only [rTr, pairVec_apply, e, mul_inv_rev, map_mul, LinearMap.comp_apply, Module.End.mul_apply]

theorem mult_equiv {D : D7} (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) {T : MMap M} (hT : T ∈ Mult θ M J χ) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (v : M.Vec) (w : M.sm τ) (hw : (w : M.H τ) = M.rep τ g (v τ)) :
    T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v) := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact hT.equiv τ g hg v w hw
  | zero => rfl
  | add T₁ T₂ _ _ h₁ h₂ =>
    simp only [MultilinearMap.add_apply, h₁, h₂]; rfl
  | smul c T _ h =>
    simp only [MultilinearMap.smul_apply, h]; rfl

end

theorem Bplus_smul_left {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (a : ℂ)
    (φ : GA D (G.V (.top 0)) → ℂ) (F : GA D (G.V (.grid D.R.m 0)) → ℂ) : Bplus W M (a • φ) F = a * Bplus W M φ F := by
  have e : ∀ h n, besInt W (a • φ) F h n = a * besInt W φ F h n := fun h n => by
    simp only [besInt, Pi.smul_apply, smul_eq_mul]; ring
  simp only [Bplus, e, integral_const_mul]

theorem Bplus_smul_right {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (a : ℂ)
    (φ : GA D (G.V (.top 0)) → ℂ) (F : GA D (G.V (.grid D.R.m 0)) → ℂ) : Bplus W M φ (a • F) = a * Bplus W M φ F := by
  have e : ∀ h n, besInt W φ (a • F) h n = a * besInt W φ F h n := fun h n => by
    simp only [besInt, Pi.smul_apply, smul_eq_mul]; ring
  simp only [Bplus, e, integral_const_mul]


end GlobalTheory.SepRows.SepProof

end
