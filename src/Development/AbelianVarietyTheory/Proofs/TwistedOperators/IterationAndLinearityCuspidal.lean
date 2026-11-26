module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAlgebraicLiftedKernel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ErrorExponentStatement
open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.BasicNotions Formalism.L2.Theta GlobalTheory.MixPer GlobalTheory.MixModel MeasureTheory
  GlobalTheory.Core.Mi Formalism.L2.SG.InstExistsPf Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH Matrix

noncomputable section

namespace GlobalTheory.Core.Mi.PerCmp

variable {D : D7} {X : HidaSetting.HidaSetting D} {h : X.B.I = instOf D} {u : D.what₂.Word}
  {V₀ A L : HSp D} {d : HypDec (D.sp.Y 0) V₀ D.R.rS} {o : OrthDec V₀ A L}
  {ζ : Fin L.rank → D.host.E} {lam : D.host.E}

theorem hyp_linIndep {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) :
    LinearIndependent D.host.E d.e.transpose := by
  have h1 : Function.Injective d.e.mulVec := by
    intro x y hxy
    have := congrArg (fun v => (d.e'.conjTranspose * HSpace.gram S).mulVec v) hxy
    simpa [Matrix.mulVec_mulVec, d.e'e] using this
  exact Matrix.mulVec_injective_iff.mp h1

theorem besPer_domN {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L)
    (ζ : Fin L.rank → D.host.E) {ψ : AddChar (AF ↥D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    (θ : D.host.E) (μ 𝓕) (ν : Measure (flagN d)) (hν : ν.IsHaarMeasure) {𝓝 𝓝' : Set (flagN d)}
    (h𝓝 : IsFundamentalDomain (NFlagQ S d.e) 𝓝 ν) (h𝓝' : IsFundamentalDomain (NFlagQ S d.e) 𝓝' ν)
    (φ : GA D A → ℂ) (f : GA D S → ℂ) (hf : ∀ γ ∈ GQ S, ∀ g, f (γ * g) = f g) :
    besPer ψ θ d o ζ μ 𝓕 ν 𝓝 φ f = besPer ψ θ d o ζ μ 𝓕 ν 𝓝' φ f := by
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag S (isIsoSub_e d)
  haveI : Countable (NFlagQ S d.e) := by
    have hinj : Function.Injective
        (fun x : NFlagQ S d.e => (⟨x.1.1, x.2⟩ : GQ S)) := fun x y hxy =>
      Subtype.ext (Subtype.ext (congrArg (fun z : GQ S => z.1) hxy))
    exact hinj.countable
  unfold besPer
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  refine h𝓝.setIntegral_eq h𝓝' fun γ n => ?_
  have hγ : ((γ : flagN d) : GA D S) ∈ GQ S := Subgroup.mem_subgroupOf.1 γ.2
  change besFun ψ θ d o ζ φ f a ((γ : flagN d) * n) = _
  simp only [besFun, Subgroup.coe_mul]
  rw [psiBes_mul d ψ θ _ γ.1.2 n.2, GlobalTheory.CharLaws.psiBes_rat ψ d hψ.2.2.1 θ _ hγ, one_mul,
    mul_assoc ((γ : flagN d) : GA D S), hf _ hγ]

theorem besPer_domA {ρ : ℕ} (B : GlobalTheory.Unf.BesLev D ρ) {ψ : AddChar (AF ↥D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) {𝓕 : Set (GA D B.A)} (h𝓕 : IsFundamentalDomain (GQ B.A) 𝓕 B.vA.μ)
    (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) (hφ : ∀ γ ∈ GQ B.A, ∀ g, φ (γ * g) = φ g)
    (hf : ∀ γ ∈ GQ B.V, ∀ g, f (γ * g) = f g) :
    besPer ψ 1 B.d B.o B.ζ B.vA.μ 𝓕 B.vN.ν B.vN.𝓝 φ f = B.per ψ φ f := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  haveI := B.vA.haar
  exact h𝓕.setIntegral_eq B.vA.fund fun γ x => Shift.inner_left B ψ hψ φ f hφ hf γ.2 x

end GlobalTheory.Core.Mi.PerCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevJGridSuccIndep
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowVal

theorem levJ_grid_succ_indep {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t t' : T) (i j : ℕ) :
    levJ G t (.grid (i + 1) (j + 1)) = levJ G t' (.grid (i + 1) (j + 1)) := rfl

theorem levJ_top_indep {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t t' : T) (j : ℕ) :
    levJ G t (.top j) = levJ G t' (.top j) := by
  cases j <;> rfl

theorem vol_row_top_indep : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t t' : T) (M M' : Vol G), M.Is t → M'.Is t' → (∀ j, 1 ≤ j → j ≤ D.R.m → M.ν (.grid D.R.m j) = M'.ν (.grid D.R.m j)) ∧ ∀ j, j ≤ D.R.m → M.ν (.top j) = M'.ν (.top j) := by
  intro D T L sc G t t' M M' hM hM'
  refine ⟨fun j hj1 hjm => ?_, fun j hj => ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, D.R.m = i + 1 := ⟨D.R.m - 1, by omega⟩
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hX : levJ G t (.grid D.R.m (j' + 1)) = levJ G t' (.grid D.R.m (j' + 1)) := by
      rw [hi]; exact levJ_grid_succ_indep G t t' i j'
    have h1 := hM.vtx (.grid D.R.m (j' + 1)) ⟨le_rfl, hjm⟩
    have h2 := hM'.vtx (.grid D.R.m (j' + 1)) ⟨le_rfl, hjm⟩
    rw [← hX] at h2
    exact GlobalTheory.HaarNorm.vol_nu_eq_of_isAt M M' _ _ h1 h2
  · have h1 := hM.vtx (.top j) hj
    have h2 := hM'.vtx (.top j) hj
    rw [← levJ_top_indep G t t' j] at h2
    exact GlobalTheory.HaarNorm.vol_nu_eq_of_isAt M M' _ _ h1 h2

end GlobalTheory.RowVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColconSplitFamAppend
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal

open GlobalTheory.Unf

theorem colcon_splitFam_append {T : Type} {S : Arrow T → Type} {X Y : Node} {p : Path T X Y} :
    ∀ {Z : Node} (q : Path T Y Z) (d : p.Fam S) (e : q.Fam S), splitFam q (Path.Fam.append (q := q) d e) = (d, e)
  | _, .nil, _, _ => rfl
  | _, .snoc _ q, d, e => by
      show ((splitFam q (Path.Fam.append (q := q) d e.1)).1, ((splitFam q (Path.Fam.append (q := q) d e.1)).2, e.2)) = (d, e)
      rw [colcon_splitFam_append q d e.1]
      rfl

theorem colcon_getD_downFam {T : Type} {S : Arrow T → Type} (t : T) (i : ℕ) :
    ∀ (n : ℕ) (f : ∀ j : Fin n, S (.down t i j)) (j : ℕ) (hj : j < n), getD t i n (downFam t i n f) j hj = f ⟨j, hj⟩
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, f, j, hj => by
      unfold getD
      have hs := colcon_splitFam_append (p := Path.one (.down t i n)) (downPath t i n) ((), f (Fin.last n))
        (downFam t i n fun j => f j.castSucc)
      rw [downFam]
      split_ifs with h
      · erw [hs]
        exact colcon_getD_downFam t i n _ j h
      · have hnj : n = j := by omega
        subst j
        change (splitFam (p := Path.one (.down t i n)) (downPath t i n) _).1.2 =
          f (Fin.last n)
        rw [hs]

theorem colcon_nIter_congr {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)] [∀ i, MeasurableSpace (H i)]
    {R : ∀ i, Subgroup (H i)} (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)) {q q' : (∀ i, H i) → ℂ} :
    ∀ (l : List ι) (h : ∀ i, H i) (z : ℂ), NIter ρ μ q l h z →
      (∀ h' : ∀ i, H i, (∀ i, i ∉ l → h' i = h i) → q h' = q' h') → NIter ρ μ q' l h z
  | [], h, z, hz, hq => (show z = q h from hz).trans (hq h fun _ _ => rfl)
  | i :: l, h, z, ⟨f, hf, hr⟩, hq => ⟨f, hf, fun g => colcon_nIter_congr ρ μ l _ _ (hr g) fun h' hh' => hq h' fun k hk => by
      rw [hh' k fun hl => hk (List.mem_cons_of_mem _ hl), Function.update_of_ne fun e => hk (by simp [e])]⟩

theorem colcon_quot {G : Type} [Group G] [MeasurableSpace G] {R R' : Subgroup G} (e : R = R') {ρ : Measure R} {ρ' : Measure R'}
    (hh : HEq ρ ρ') {μ : Measure G} {f : G → ℂ} {z : ℂ} (h : IsQuotIntL1 ρ' μ f z) : IsQuotIntL1 ρ μ f z := by
  subst e
  obtain rfl := eq_of_heq hh
  exact h

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem colcon_rowGrp_jac {t : T} {M : Vol G} (hM : M.Is t) (j σ : ℕ) (hj : j + 2 * σ + 1 = D.R.m) :
    rowGrp G j = jacGrp (jacAt G hM j σ hj).d := by
  unfold rowGrp
  rw [dite_eq_left (by omega)]
  obtain rfl : σ = (D.R.m - 1 - j) / 2 := by omega
  rfl

theorem colcon_rowGrp_bes {t : T} {M : Vol G} (hM : M.Is t) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m)
    (vN : VolN (besDecAt G j σ hj)) :
    rowGrp G j = besGrp (besAt G hM j σ hj vN).d (besAt G hM j σ hj vN).o := by
  unfold rowGrp
  rw [dite_eq_right (by omega), dite_eq_left (by omega)]
  obtain rfl : σ = (D.R.m - 2 - j) / 2 := by omega
  rfl

theorem colcon_gen (G : GridData L sc) (W : G.Weil) (t : T) {M : Vol G} (hM : M.Is t) (Φ : SchDown G t)
    (F : Fn G (.grid D.R.m D.R.m)) (ρ : ∀ j, Measure (rowGrp G j))
    (hJ : ∀ j σ (hj : j + 2 * σ + 1 = D.R.m), HEq (ρ j) (jacAt G hM j σ hj).μR)
    (hB : ∀ j σ (hj : j + 2 * σ + 2 = D.R.m), HEq (ρ j) (besAt G hM j σ hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some).μR) :
    ∀ (σ j : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (vN : VolN (besDecAt G j σ hj)) (h : Pts G) (g : GA D (G.V (.grid D.R.m j)))
      (φ : GA D (G.V (.top j)) → ℂ) (z : ℂ), g = h j →
      (chainFrom G W t hM σ j hj vN).Iter
        (colPer W hM σ j hj vN (dataFrom G W t hM (downFam t D.R.m D.R.m Φ) σ j hj vN) F φ g) z →
      NIter ρ (fun j => M.ν (.grid D.R.m j)) (fun h' => jPer W M t (conAt W hM Φ h') F σ j hj φ)
        (List.range' (j + 1) (2 * σ)) h z := fun
  | 0, j, hj, vN, h, g, φ, z, hg, hz => by
      subst hg
      have hc : conAt W hM Φ h j = lastDat W hM j hj vN (h j) (Φ ⟨j, by omega⟩)
          (castSch G (show j + 1 + 1 = D.R.m by omega) (Φ ⟨j + 1, by omega⟩)) := by
        unfold conAt
        rw [dite_eq_left hj]
        rfl
      have hz' : z = colPer W hM 0 j hj vN (dataFrom G W t hM (downFam t D.R.m D.R.m Φ) 0 j hj vN) F φ (h j) () := hz
      show z = jPer W M t (conAt W hM Φ h) F 0 j hj φ
      rw [hz']
      show _ = ∫ h' in M.fd (.grid D.R.m D.R.m), F h' * biL W M t j φ (conAt W hM Φ h j)
        (GlobalTheory.RowChain.topEmb G (show D.R.m = j + 1 + 1 by omega) h') ∂M.ν (.grid D.R.m D.R.m)
      rw [hc]
      dsimp only [GlobalTheory.RowChain.colPer, dataFrom]
      rw [colcon_getD_downFam, colcon_getD_downFam]
      rfl
  | σ + 1, j, hj, vN, h, g, φ, z, hg, hz => by
      subst hg
      have hj' : j + 1 + 1 + 2 * σ + 2 = D.R.m := by omega
      let vN' := (GlobalTheory.Unf.Inhab.nonempty_volN (besDecAt G (j + 1 + 1) σ hj')).some
      have hstep : ∃ (f₁ : GA D (G.V (.grid D.R.m (j + 1))) → ℂ)
          (f₂ : GA D (G.V (.grid D.R.m (j + 1))) → GA D (G.V (.grid D.R.m (j + 1 + 1))) → ℂ),
        IsQuotIntL1 (jacAt G hM (j + 1) (σ + 1) (by omega)).μR
          (M.ν (.grid D.R.m (j + 1))) f₁ z ∧
        ∀ a, IsQuotIntL1 (besAt G hM (j + 1 + 1) σ hj' vN').μR
          (M.ν (.grid D.R.m (j + 1 + 1))) (f₂ a) (f₁ a) ∧
          ∀ b, (chainFrom G W t hM σ (j + 1 + 1) hj' vN').Iter
            (fun rest => colPer W hM (σ + 1) j hj vN
              (dataFrom G W t hM (downFam t D.R.m D.R.m Φ) (σ + 1) j hj vN)
              F φ (h j) (a, b, rest)) (f₂ a b) := hz
      rcases hstep with ⟨f₁, f₂, h1, h2⟩
      have hl : List.range' (j + 1) (2 * (σ + 1)) = (j + 1) :: (j + 1 + 1) :: List.range' (j + 1 + 1 + 1) (2 * σ) := by
        rw [show 2 * (σ + 1) = 2 * σ + 1 + 1 by ring, List.range'_succ, List.range'_succ]
      rw [hl]
      have hjJ : j + 1 + 2 * (σ + 1) + 1 = D.R.m := by omega
      refine ⟨f₁, colcon_quot (colcon_rowGrp_jac hM (j + 1) (σ + 1) hjJ)
        (hJ (j + 1) (σ + 1) hjJ) h1, fun a => ?_⟩
      refine ⟨f₂ a, colcon_quot (colcon_rowGrp_bes hM (j + 1 + 1) σ hj' vN')
        (hB (j + 1 + 1) σ hj') (h2 a).1,
        fun b => ?_⟩
      have hi := (h2 a).2 b
      dsimp only [GlobalTheory.RowChain.colPer, dataFrom] at hi
      have ih := colcon_gen G W t hM Φ F ρ hJ hB σ (j + 1 + 1) hj' vN'
        (Function.update (Function.update h (j + 1) a) (j + 1 + 1) b) b _ (f₂ a b) (by simp) hi
      refine colcon_nIter_congr _ _ _ _ _ ih fun h' hh' => ?_
      have e0 : h' j = h j := (hh' j (by simp only [List.mem_range'_1]; omega)).trans
        ((Function.update_of_ne (by omega) _ _).trans (Function.update_of_ne (by omega) _ _))
      have e1 : h' (j + 1) = a := (hh' (j + 1) (by simp only [List.mem_range'_1]; omega)).trans
        ((Function.update_of_ne (by omega) _ _).trans (Function.update_self _ _ _))
      have e2 : h' (j + 1 + 1) = b := (hh' (j + 1 + 1) (by simp only [List.mem_range'_1]; omega)).trans (Function.update_self _ _ _)
      change _ = jPer W M t (conAt W hM Φ h') F σ (j + 1 + 1) hj'
        (biL W M t j φ (conAt W hM Φ h' j))
      apply congrArg (jPer W M t (conAt W hM Φ h') F σ (j + 1 + 1) hj')
      have hx : j + 2 * ((D.R.m - 4 - j) / 2 + 1) + 2 = D.R.m := by omega
      have hlast : ¬ (j + 2 * 0 + 2 = D.R.m) := by omega
      have hC : conAt W hM Φ h' j = _ :=
        (dite_eq_right hlast).trans (dite_eq_left hx)
      rw [hC]
      obtain rfl : σ = (D.R.m - 4 - j) / 2 := by omega
      simp only [e0, e1, e2, colcon_getD_downFam]
      -- These projections of the Bessel data are independent of the choice of vN.
      dsimp only [biL, GlobalTheory.SeeSaw.biLift, volAt, contr, flatBF, flatFB, Link.κ,
        stepAt, linkAt, besAt, jacAt]
      rfl

theorem nIter_conAt_of_colPer : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (W : G.Weil) (t : T) {M : Vol G} (hM : M.Is t) (Φ : SchDown G t) (F : Fn G (.grid D.R.m D.R.m)) (φ : Fn G (.top 0)) (z : ℂ), (chain G W t hM).Iter (colPer W hM _ 0 top_idx (topVN hM) (chainData G W t hM (downFam t D.R.m D.R.m Φ)) F φ 1) z → ∀ (ρ : ∀ j, Measure (rowGrp G j)), (∀ j σ (hj : j + 2 * σ + 1 = D.R.m), HEq (ρ j) (jacAt G hM j σ hj).μR) → (∀ j σ (hj : j + 2 * σ + 2 = D.R.m), HEq (ρ j) (besAt G hM j σ hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some).μR) → NIter ρ (fun j => M.ν (.grid D.R.m j)) (fun h => jPer W M t (conAt W hM Φ h) F _ 0 top_idx φ) (idx D) 1 z := by
  intro D T L sc G W t M hM Φ F φ z hz ρ hJ hB
  have e : List.range' (0 + 1) (2 * ((D.R.m - 2) / 2)) = idx D := by
    unfold idx
    have := top_idx (D := D)
    congr 1
    omega
  rw [← e]
  exact colcon_gen G W t hM Φ F ρ hJ hB _ 0 top_idx (topVN hM) 1 1 φ z rfl hz

end GlobalTheory.RowVal
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open Formalism.IndefR Formalism.IndefR.Links Formalism.L2.DIV GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow

variable {D : D7}

section Lin

variable {ψ : AddChar (AF D.host.F) ℂ} {T₀ : HSp D}

end Lin

theorem unitN_unique {S : HSp D} {ρ : ℕ} {e : Matrix (Fin S.rank) (Fin ρ) D.host.E} (he : IsIsoSub S e)
    {ν ν' : Measure (NFlag S e)} {𝓝 𝓝' : Set (NFlag S e)} (h : GlobalTheory.Per.IsUnitN S e ν 𝓝) (h' : GlobalTheory.Per.IsUnitN S e ν' 𝓝') :
    ν = ν' := by
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag S he
  haveI : Countable (NFlagQ S e) := by
    have hinj : Function.Injective (fun x : NFlagQ S e => (⟨x.1.1, x.2⟩ : GQ S)) := fun x y hxy =>
      Subtype.ext (Subtype.ext (congrArg (fun z : GQ S => z.1) hxy))
    exact hinj.countable
  haveI := h.1
  haveI := h'.1
  have hs := Measure.isMulLeftInvariant_eq_smul ν ν'
  have hac : ν ≪ ν' := by rw [hs]; exact Measure.smul_absolutelyContinuous
  have h2 : ν 𝓝' = 1 := ((h'.2.1.mono hac).measure_eq h.2.1).trans h.2.2
  have h3 : ν 𝓝' = Measure.haarScalarFactor ν ν' := by
    conv_lhs => rw [hs]
    simp [h'.2.2]
  rw [hs, ENNReal.coe_eq_one.1 (h3.symm.trans h2), one_smul]

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem per_indep {ρ : ℕ} (B : GlobalTheory.Unf.BesLev D ρ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    {μ : Measure (GA D B.A)} (hA : μ = B.vA.μ) {𝓕 : Set (GA D B.A)} (h2 : IsFundamentalDomain (GQ B.A) 𝓕 μ)
    {ν : Measure (flagN B.d)} {𝓝 : Set (flagN B.d)} (hu : GlobalTheory.Per.IsUnitN B.V B.d.e ν 𝓝) (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ)
    (hφ : ∀ γ ∈ GQ B.A, ∀ g, φ (γ * g) = φ g) (hf : ∀ γ ∈ GQ B.V, ∀ g, f (γ * g) = f g) :
    besPer ψ 1 B.d B.o B.ζ μ 𝓕 ν 𝓝 φ f = B.per ψ φ f := by
  have hI : IsIsoSub B.V B.d.e := ⟨GlobalTheory.Core.Mi.PerCmp.hyp_linIndep B.d, by rw [cT_sig]; exact B.d.ee⟩
  obtain rfl : ν = B.vN.ν := unitN_unique hI hu B.vN.unit
  subst hA
  exact (GlobalTheory.Core.Mi.PerCmp.besPer_domN B.d B.o B.ζ hψ 1 _ _ B.vN.ν B.vN.unit.1 hu.2.1 B.vN.unit.2.1 φ f hf).trans
    (GlobalTheory.Core.Mi.PerCmp.besPer_domA B hψ h2 φ f hφ hf)

theorem hN_top {M : Vol G} {t : T} (hM : M.Is t) : NFlag (G.V (.grid D.R.m 0)) G.besTop.e = flagN (topLev G hM).d :=
  by
  set_option maxHeartbeats 20000000 in
   exact (nFlag_diag (GlobalTheory.RowUnf.rowBes G 0 (by have := D.R.two_le_m; omega) ((D.R.m - 2) / 2)
    (by have := top_idx (D := D); omega)).e (lam _) (lam_ne _)).symm

def topVNRow {M₀ : Vol G} (h₀ : M₀.IsRow) : GlobalTheory.Unf.VolN (besDecAt G 0 ((D.R.m - 2) / 2) top_idx) :=
  by
  set_option maxHeartbeats 20000000 in
   exact volNOf (d := GlobalTheory.RowUnf.rowBes G 0 (by have := D.R.two_le_m; omega) ((D.R.m - 2) / 2) (by have := top_idx (D := D); omega))
    (nFlag_diag _ (lam _) (lam_ne _)).symm
    (GlobalTheory.RowUnf.topVolN G M₀ h₀ (by have := D.R.two_le_m; omega) (by have := top_idx (D := D); omega))

theorem bplus_eq_besPer (W : G.Weil) {M₀ : Vol G} (h₀ : M₀.IsRow) {M : Vol G} {t : T} (hM : M.Is t) (φ : Fn G (.top 0))
    (F : Fn G (.grid D.R.m 0)) : Bplus W M₀ φ F = besPer W.ψ 1 (topLev G hM).d (topLev G hM).o (topLev G hM).ζ (M₀.ν (.top 0))
      (M₀.fd (.top 0)) (topVNRow h₀).ν (topVNRow h₀).𝓝 φ F := by
  have hN := hN_top hM
  show _ = ∫ h in M₀.fd (.top 0), ∫ n in trSet hN M₀.fdN,
      GlobalTheory.MixPer.besFun W.ψ 1 (topLev G hM).d (topLev G hM).o (topLev G hM).ζ φ F h n ∂(trMeas hN M₀.νN) ∂M₀.ν (.top 0)
  refine integral_congr_ae (ae_of_all _ fun h => ?_)
  refine (TopPer.integral_tr hN M₀.νN M₀.fdN fun g => φ h * F (g * embTop G h) * star (besChar W.ψ G.besTop g)).symm.trans ?_
  refine integral_congr_ae (ae_of_all _ fun n => ?_)
  show φ h * F (n.1 * embTop G h) * star (besChar W.ψ G.besTop n.1) =
    φ h * F ((show GA D (topLev G hM).V from n.1) * GlobalTheory.MixPer.embA (topLev G hM).d (topLev G hM).o h) *
      star (psiBes W.ψ (topLev G hM).d 1 (vecB (topLev G hM).o (topLev G hM).ζ) n.1)
  rw [TopPer.embA_topLev G hM h, TopPer.psiBes_topLev G hM W.ψ n.1 n.2]
  rfl

theorem meas_top {M₀ M : Vol G} (h₀ : M₀.IsRow) {t : T} (hM : M.Is t) : M₀.ν (.top 0) = (topLev G hM).vA.μ :=
  GlobalTheory.HaarNorm.vol_nu_eq_of_isAt M₀ M _ _ h₀.top hM.isRow.top

theorem bplus_indep (W : G.Weil) {M₀ M : Vol G} (h₀ : M₀.IsRow) {t : T} (hM : M.Is t) (φ : Fn G (.top 0))
    (F : Fn G (.grid D.R.m 0)) (hφ : ∀ γ ∈ GQ (G.V (.top 0)), ∀ g, φ (γ * g) = φ g)
    (hF : ∀ γ ∈ GQ (G.V (.grid D.R.m 0)), ∀ g, F (γ * g) = F g) : Bplus W M₀ φ F = Bplus W M φ F :=
  (bplus_eq_besPer W h₀ hM φ F).trans ((per_indep (topLev G hM) W.ψ_std.1 (meas_top h₀ hM) h₀.top.haar_fund.2
    (topVNRow h₀).unit φ F hφ hF).trans (TopPer.bplus_eq_topLev_per G W t _ hM φ F).symm)

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.FlipRun

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem bplus_add_right (W : G.Weil) (M : Vol G) {φ : Fn G (.top 0)} {F F' : Fn G (.grid D.R.m 0)} (h : BplusConv W M φ F)
    (h' : BplusConv W M φ F') : BplusConv W M φ (F + F') ∧ Bplus W M φ (F + F') = Bplus W M φ F + Bplus W M φ F' := by
  have e : ∀ x, besInt W φ (F + F') x = fun n => besInt W φ F x n + besInt W φ F' x n := fun x => funext fun n => by
    simp only [besInt, Pi.add_apply]; ring
  have ei : ∀ x, ∫ n in M.fdN, besInt W φ (F + F') x n ∂M.νN =
      (∫ n in M.fdN, besInt W φ F x n ∂M.νN) + ∫ n in M.fdN, besInt W φ F' x n ∂M.νN := fun x => by
    rw [e x]; exact integral_add (h.1 x) (h'.1 x)
  refine ⟨⟨fun x => ?_, ?_⟩, ?_⟩
  · rw [e x]; exact (h.1 x).add (h'.1 x)
  · simp only [ei]; exact h.2.add h'.2
  · simp only [Bplus, ei]; exact integral_add h.2 h'.2

theorem bplus_smul_right (W : G.Weil) (M : Vol G) (c : ℂ) {φ : Fn G (.top 0)} {F : Fn G (.grid D.R.m 0)} (h : BplusConv W M φ F) :
    BplusConv W M φ (c • F) ∧ Bplus W M φ (c • F) = c * Bplus W M φ F := by
  have e : ∀ x, besInt W φ (c • F) x = fun n => c * besInt W φ F x n := fun x => funext fun n => by
    simp only [besInt, Pi.smul_apply, smul_eq_mul]; ring
  have ei : ∀ x, ∫ n in M.fdN, besInt W φ (c • F) x n ∂M.νN = c * ∫ n in M.fdN, besInt W φ F x n ∂M.νN := fun x => by
    rw [e x]; exact integral_const_mul _ _
  refine ⟨⟨fun x => ?_, ?_⟩, ?_⟩
  · rw [e x]; exact (h.1 x).const_mul c
  · simp only [ei]; exact h.2.const_mul c
  · simp only [Bplus, ei]; exact integral_const_mul _ _

theorem bplus_sum_right (W : G.Weil) (M : Vol G) (φ : Fn G (.top 0)) {ι : Type} (s : Finset ι) (F : ι → Fn G (.grid D.R.m 0))
    (h : ∀ i ∈ s, BplusConv W M φ (F i)) :
    BplusConv W M φ (∑ i ∈ s, F i) ∧ Bplus W M φ (∑ i ∈ s, F i) = ∑ i ∈ s, Bplus W M φ (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have e : ∀ x, besInt W φ (0 : Fn G (.grid D.R.m 0)) x = fun _ => 0 := fun x => funext fun n => by simp [besInt]
    rw [Finset.sum_empty, Finset.sum_empty]
    refine ⟨⟨fun x => by rw [e x]; exact integrableOn_zero, ?_⟩, ?_⟩
    · simp only [e, integral_zero]; exact integrableOn_zero
    · simp only [Bplus, e, integral_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    obtain ⟨h1, h2⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    obtain ⟨h3, h4⟩ := bplus_add_right W M (h i (Finset.mem_insert_self _ _)) h1
    exact ⟨h3, by rw [h4, h2]⟩

theorem liftT_oppTens (W : G.Weil) (M : Vol G) (t : T) (τi : PolRow G × PolDown G →₀ ℂ) (τf : SchRow G × SchDown G t →₀ ℂ)
    (F : Fn G (.grid 0 D.R.m)) : liftT W M (oppPath t D.R.m) (oppTens W t τi τf) F =
      ∑ x ∈ τi.support ×ˢ τf.support, (τi x.1 * τf x.2) • liftP W M (oppPath t D.R.m) (oppPure W t x.1 x.2) F := by
  let l : TotT G (oppPath t D.R.m) →+ Fn G (.grid D.R.m 0) :=
    AddMonoidHom.mk' (fun τ => liftT W M (oppPath t D.R.m) τ F) fun τ τ' => liftT_add W M _ τ τ' F
  show l (oppTens W t τi τf) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [oppTens, Finsupp.sum, map_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun P _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finsupp.sum, map_sum]
  exact Finset.sum_congr rfl fun d _ => liftT_single W M _ _ _ F

theorem all_append {S : Arrow T → Type} {P : ∀ a, S a → Prop} {X Y : Node} {p : Path T X Y} {d : p.Fam S} (hd : Path.Fam.All P d) :
    ∀ {Z : Node} (q : Path T Y Z) (e : q.Fam S), Path.Fam.All P e → Path.Fam.All P (Path.Fam.append (q := q) d e)
  | _, .nil, _, _ => hd
  | _, .snoc _ q, e, he => ⟨all_append hd q e.1 he.1, he.2⟩

theorem all_downFam {S : Arrow T → Type} {P : ∀ a, S a → Prop} (t : T) (i : ℕ) :
    ∀ n (f : ∀ j : Fin n, S (.down t i j)), (∀ j, P _ (f j)) → Path.Fam.All P (downFam t i n f)
  | 0, _, _ => trivial
  | n + 1, f, h => all_append (p := Path.one (.down t i n)) (d := ((), f (Fin.last n))) ⟨trivial, h (Fin.last n)⟩ _ _
      (all_downFam t i n _ fun j => h j.castSucc)

variable (W : G.Weil) (M : Vol G) (t : T)

def rowLift (P : PolRow G) (d : SchRow G) (F : Fn G (.grid 0 D.R.m)) : Fn G (.grid D.R.m D.R.m) :=
  liftP W M (rowPath T D.R.m D.R.m) (rowFam D.R.m D.R.m fun i => W.fock (.chi i D.R.m) (d i) (P i)) F

def downPure (P : PolDown G) (d : SchDown G t) : PureT G (downPath t D.R.m D.R.m) :=
  downFam t D.R.m D.R.m fun j => W.fock (.mu t D.R.m j) (d j) (P j)


variable {M t} in
def oppPer (hM : M.Is t) (P : PolRow G × PolDown G) (d : SchRow G × SchDown G t) (φ : Fn G (.top 0)) (F : Fn G (.grid 0 D.R.m)) :
    (chain G W t hM).Var → ℂ :=
  GlobalTheory.RowChain.colPer W hM _ 0 top_idx (topVN hM) (chainData G W t hM (downPure W t P.2 d.2)) (rowLift W M P.1 d.1 F) φ 1

theorem pathLift_oppositePure (P : PolRow G × PolDown G) (d : SchRow G × SchDown G t) (F : Fn G (.grid 0 D.R.m)) :
    liftP W M (oppPath t D.R.m) (oppPure W t P d) F =
      liftP W M (downPath t D.R.m D.R.m) (downPure W t P.2 d.2) (rowLift W M P.1 d.1 F) :=
  pathLift_comp W M _ _ F _ _

theorem allTheta_downPure (ρ : RealMatch W) (e : AE D) (φ d : SchDown G t)
    (h : ∀ j : Fin D.R.m, IsLocVec W (.mu t D.R.m j) e (ρ.vT D.R.m j) (φ j) (d j)) (P : PolDown G) :
    AllTheta G W t (downPure W t P d) :=
  all_downFam t _ _ _ fun j => GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _
    (GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is (h j).2 (ρ.vT_is t _ j le_rfl j.2).2.theta) (P j)

variable {W M t}

theorem pure_core (hP : GlobalTheory.Published.CuspRapidDecay) {M₀ : Vol G} (h₀ : M₀.IsRow) (hM : M.Is t) {ρ : RealMatch W}
    (hS : CuspStep W M ρ t) {e : AE D} (he : IsIdemSum e (locPl G t)) (φ d : SchRow G × SchDown G t)
    (hr : ∀ i : Fin D.R.m, IsLocVec W (.chi i D.R.m) e (ρ.vX i D.R.m) (φ.1 i) (d.1 i))
    (hd : ∀ j : Fin D.R.m, IsLocVec W (.mu t D.R.m j) e (ρ.vT D.R.m j) (φ.2 j) (d.2 j)) (P : PolRow G × PolDown G)
    {F : Fn G (.grid 0 D.R.m)} (hF : IsCuspListed W.θ (.grid 0 D.R.m) F) {u : Fn G (.top 0)} (hu : GlobalTheory.Unf.IsContAut _ u) :
    IsCuspListed W.θ (.grid D.R.m D.R.m) (rowLift W M P.1 d.1 F) ∧
      IsCuspListed W.θ (.grid D.R.m 0) (liftP W M (oppPath t D.R.m) (oppPure W t P d) F) ∧
      (chain G W t hM).Iter (oppPer W hM P d u F) (Bplus W M₀ u (liftP W M (oppPath t D.R.m) (oppPure W t P d) F)) := by
  have hrow : IsCuspListed W.θ (.grid D.R.m D.R.m) (rowLift W M P.1 d.1 F) := by
    have H := GlobalTheory.ChainHyp.row_cusp hS he hF D.R.m le_rfl _ _
      (rowFam (S := fun a => PolF D (G.pT a.pair).rank (G.pS a.pair).rank) D.R.m D.R.m P.1)
      ((GlobalTheory.OppConv.vecAll_row ρ e _ _ φ.1 d.1).2 hr)
    rw [GlobalTheory.OppConv.zip_row] at H
    exact H
  have hz : downPure W t P.2 d.2 = Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) (downFam t D.R.m D.R.m d.2)
      (downFam (S := fun a => PolF D (G.pT a.pair).rank (G.pS a.pair).rank) t D.R.m D.R.m P.2) :=
    (GlobalTheory.OppConv.zip_down (fun a (f : Sch G a) (Q : PolF D (G.pT a.pair).rank (G.pS a.pair).rank) => W.fock a.pair f Q)
      t D.R.m D.R.m d.2 P.2).symm
  have hv := (GlobalTheory.OppConv.vecAll_down ρ e t _ _ φ.2 d.2).2 hd
  have hc := GlobalTheory.ChainHyp.chain_props hP G W W.θ_is t hM (downPure W t P.2 d.2) _ hrow (fun k hk F' hF' => by
    rw [hz, GlobalTheory.ChainHyp.getD_zip]
    exact (hS (.down t D.R.m k) (Or.inr ⟨D.R.m, k, le_rfl, hk, rfl⟩) e he _ _
      (GlobalTheory.ChainHyp.getD_loc ρ e t _ _ _ _ hv k hk) _ F' hF').2) _ 0 top_idx (topVN hM)
  have hdn := GlobalTheory.RowChainDown.chain_down_eq_liftP G W t M hM (downPure W t P.2 d.2) (rowLift W M P.1 d.1 F)
  have hc1 : IsCuspListed W.θ (.grid D.R.m 0)
      ((chain G W t hM).down (chainData G W t hM (downPure W t P.2 d.2)) (rowLift W M P.1 d.1 F)) := hc.1
  rw [pathLift_oppositePure, ← hdn]
  refine ⟨hrow, hc1, ?_⟩
  have hB := (bplus_indep W h₀ hM u _ hu.1 hc1.1.toIsAutFun.left).trans (TopPer.bplus_eq_topLev_per G W t M hM u _)
  rw [hB]
  exact iter_colPer W hM _ (allTheta_downPure W t ρ e φ.2 d.2 hd P.2) _
    ⟨hrow.1.toIsAutFun.left, hrow.1.toIsAutFun.cont⟩ u hu hc.2

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.FlipRun

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.FlipRun GlobalTheory.RowUnf GlobalTheory.RowVal

theorem nIter_meas_congr {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)] [∀ i, MeasurableSpace (H i)]
    {R : ∀ i, Subgroup (H i)} (ρ : ∀ i, Measure (R i)) {μ μ' : ∀ i, Measure (H i)} {q : (∀ i, H i) → ℂ} :
    ∀ (l : List ι) (h : ∀ i, H i) (z : ℂ), (∀ i ∈ l, μ i = μ' i) → NIter ρ μ q l h z → NIter ρ μ' q l h z
  | [], _, _, _, hz => hz
  | i :: l, _, _, e, ⟨f, hf, hr⟩ => ⟨f, e i (by simp) ▸ hf, fun g =>
      nIter_meas_congr ρ l _ _ (fun k hk => e k (List.mem_cons_of_mem _ hk)) (hr g)⟩

theorem exists_haar_heq {H : Type} [Group H] [TopologicalSpace H] [MeasurableSpace H] {R R' : Subgroup H} (e : R = R')
    (ρ' : Measure R') (h : ρ'.IsHaarMeasure) : ∃ ρ : Measure R, ρ.IsHaarMeasure ∧ HEq ρ ρ' := by
  subst e
  exact ⟨ρ', h, HEq.rfl⟩

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem exists_vol_top (j : ℕ) : ∃ v : GlobalTheory.Unf.Vol (G.V (.top j)), j ≤ D.R.m → ∀ t (M : Vol G), M.Is t → M.ν (.top j) = v.μ := by
  by_cases h : j ≤ D.R.m ∧ ∃ t, ∃ M : Vol G, M.Is t
  · obtain ⟨hj, t₀, M₀, h₀⟩ := h
    exact ⟨volAt h₀ (.top j) hj, fun _ t M hM => (vol_row_top_indep G t t₀ M M₀ hM h₀).2 j hj⟩
  · exact ⟨(GlobalTheory.Unf.Inhab.nonempty_vol _).some, fun hj t M hM => absurd ⟨hj, t, M, hM⟩ h⟩

theorem exists_vol_row (j : ℕ) : ∃ v : GlobalTheory.Unf.Vol (G.V (.grid D.R.m j)),
    1 ≤ j → j ≤ D.R.m → ∀ t (M : Vol G), M.Is t → M.ν (.grid D.R.m j) = v.μ := by
  by_cases h : 1 ≤ j ∧ j ≤ D.R.m ∧ ∃ t, ∃ M : Vol G, M.Is t
  · obtain ⟨h1, hj, t₀, M₀, h₀⟩ := h
    exact ⟨volAt h₀ (.grid D.R.m j) ⟨le_rfl, hj⟩, fun _ _ t M hM => (vol_row_top_indep G t t₀ M M₀ hM h₀).1 j h1 hj⟩
  · exact ⟨(GlobalTheory.Unf.Inhab.nonempty_vol _).some, fun h1 hj t M hM => absurd ⟨h1, hj, t, M, hM⟩ h⟩

theorem exists_rowMeas (j : ℕ) : ∃ ρ : Measure (rowGrp G j), (j < D.R.m → ρ.IsHaarMeasure) ∧ ∀ t (M : Vol G) (hM : M.Is t),
    (∀ σ (hj : j + 2 * σ + 1 = D.R.m), HEq ρ (jacAt G hM j σ hj).μR) ∧
      ∀ σ (hj : j + 2 * σ + 2 = D.R.m), HEq ρ (besAt G hM j σ hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some).μR := by
  obtain ⟨v, hv⟩ := exists_vol_top G j
  by_cases h : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m
  · let J : GlobalTheory.Unf.JacLev D ((D.R.m - 1 - j) / 2) :=
      ⟨G.V (.grid D.R.m j), G.V (.top j), rowJac G j (by omega) _ (by omega), cocpt_top G (by omega), v,
        (GlobalTheory.Unf.Inhab.nonempty_volN _).some⟩
    have e : rowGrp G j = jacGrp J.d := dif_pos h
    obtain ⟨ρ, h1, h2⟩ := exists_haar_heq e J.μR (GlobalTheory.QuotZero.jac_haar_inv J).2.1
    refine ⟨ρ, fun _ => h1, fun t M hM => ⟨fun σ hj => ?_, fun σ hj => by omega⟩⟩
    obtain rfl : σ = (D.R.m - 1 - j) / 2 := by omega
    refine h2.trans (heq_of_eq ?_)
    show semiMeas _ _ v.μ _ = semiMeas _ _ (M.ν (.top j)) _
    rw [hv (by omega) t M hM]
    rfl
  by_cases h' : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m
  · let B : GlobalTheory.Unf.BesLev D ((D.R.m - 2 - j) / 2) :=
      ⟨G.V (.grid D.R.m j), _, G.V (.top j), GlobalTheory.SeeSaw.Model.nLine D, besDecAt G j _ h', GlobalTheory.OrthSumExists.orthDecHsum D _ _,
        fun _ => D.host.xi0 ^ ((D.R.m - 2 - j) / 2),
        GlobalTheory.SeeSaw.Model.isLineVec_nLine (pow_ne_zero _ (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D)), cocpt_top G (by omega), v,
        (GlobalTheory.Unf.Inhab.nonempty_volN _).some⟩
    have e : rowGrp G j = besGrp B.d B.o := by
      simp only [rowGrp, dif_neg h, dif_pos h']
      rfl
    obtain ⟨ρ, h1, h2⟩ := exists_haar_heq e B.μR (GlobalTheory.QuotZero.bes_haar_inv B).2.1
    refine ⟨ρ, fun _ => h1, fun t M hM => ⟨fun σ hj => by omega, fun σ hj => ?_⟩⟩
    obtain rfl : σ = (D.R.m - 2 - j) / 2 := by omega
    refine h2.trans (heq_of_eq ?_)
    show semiMeas _ _ v.μ _ = semiMeas _ _ (M.ν (.top j)) _
    rw [hv (by omega) t M hM]
    rfl
  · exact ⟨0, fun _ => by omega, fun t M hM => ⟨fun σ hj => by omega, fun σ hj => by omega⟩⟩

theorem mem_idx {j : ℕ} (hj : j ∈ idx D) : 1 ≤ j ∧ j < D.R.m := by
  simp only [idx, List.mem_range'_1] at hj
  omega

end GlobalTheory.RowChain

end
