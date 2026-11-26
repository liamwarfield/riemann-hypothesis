module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionBoundaryNormalCrossing
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalOrbitChart
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjChartSetEqSetChartSet

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncModelEmbeddedLogResolution
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncModelEmbeddedLogResolution
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isUnit_algebraMap_locRing {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (pt : Fin n → ℂ)
    (g : MvPolynomial (Fin n) ℂ) (hg : eval pt g ≠ 0) :
    IsUnit (algebraMap _ (ReciprocityTheory.AnForm.R.locRing I pt) g) := by
  have := (IsLocalization.map_units (ReciprocityTheory.AnForm.R.locPt pt)
    (⟨g, fun h => hg (RingHom.mem_ker.mp h)⟩ : (ReciprocityTheory.AnForm.R.ptIdeal pt).primeCompl)).map
    (algebraMap (ReciprocityTheory.AnForm.R.locPt pt) (ReciprocityTheory.AnForm.R.locRing I pt))
  rwa [← IsScalarTower.algebraMap_apply] at this

theorem not_mem_conePts_top (z : (Σ k, ι k) → ℂ) :
    z ∉ ReciprocityTheory.AnForm.R.conePts (⊤ : Ideal (MvPolynomial (Σ k, ι k) ℂ)) :=
  fun hz => by simpa using hz.2 1 Submodule.mem_top

theorem exists_isEmbedded_of_algRes {P J : Ideal (MRing ι)} {e : ℕ} (hJ : IsMultiHomogIdeal J)
    (hJP : ¬ J ≤ P) (hPC : ∀ f : MRing ι, map (Int.castRingHom ℂ) f ∈ pC P → f ∈ P)
    (R : ReciprocityTheory.AnForm.R.AlgRes (ι := ι) (pC P) (pC J) e)
    (hsurj : ∀ z ∈ ReciprocityTheory.AnForm.R.conePts (pC P), ∃ i, ∃ x ∈ R.src i,
      ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (R.coord i x) (R.lift i q)) z)
    (hinj : ∀ i j, ∀ x ∈ R.src i, ∀ x' ∈ R.src j,
      ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (R.coord i x) (R.lift i q))
        (fun q => eval (R.coord j x') (R.lift j q)) → x = x')
    (hinv : ∀ i, ∀ x ∈ R.src i, ∀ p : (k : K) → ι k, (∀ k, eval (R.coord i x) (R.lift i ⟨k, p k⟩) ≠ 0) →
      ∃ O : Set R.M, IsOpen O ∧ x ∈ O ∧ O ⊆ R.src i ∧ ∃ (q : MvPolynomial (Σ k, ι k) ℂ)
        (F : Fin (R.amb i) → MvPolynomial (Σ k, ι k) ℂ), ∀ y ∈ O,
          (∀ k, eval (R.coord i y) (R.lift i ⟨k, p k⟩) ≠ 0) ∧
          eval (ReciprocityTheory.AnForm.R.affCoord p fun q => eval (R.coord i y) (R.lift i q)) q ≠ 0 ∧
          ∀ l, R.coord i y l * eval (ReciprocityTheory.AnForm.R.affCoord p fun q => eval (R.coord i y) (R.lift i q)) q =
            eval (ReciprocityTheory.AnForm.R.affCoord p fun q => eval (R.coord i y) (R.lift i q)) (F l)) :
    ∃ R' : AnLogRes P J e, IsEmbedded R'.A P R'.U R'.lift := by
  classical
  let R0 : ReciprocityTheory.AnForm.R.AlgRes (ι := ι) (pC P) ⊤ e :=
    { M := R.M
      n := R.n
      amb := R.amb
      ideal := R.ideal
      src := R.src
      isOpen_alt_bis := R.isOpen_alt_bis
      cover := R.cover
      coord := R.coord
      isEmbedding := R.isEmbedding
      image := R.image
      trans := R.trans
      regular := R.regular
      dim := R.dim
      lift := R.lift
      lift_one := R.lift_one
      lift_mem := R.lift_mem
      compat := R.compat
      surj := fun z hz _ => hsurj z hz
      inj := fun i j x hx x' hx' _ h => hinj i j x hx x' hx' h
      inv := fun i x hx _ p hp => hinv i x hx p hp
      bd := fun _ => ⊤
      le_bd := fun _ => le_top
      zero_bd := fun i x hx =>
        ⟨fun h => absurd (h 1 Submodule.mem_top) (by simp), fun h => absurd h (not_mem_conePts_top _)⟩
      rc := 0
      comp := Fin.elim0
      sncAt := fun i x hx =>
        { r := (R.sncAt i x hx).r
          J := ∅
          h := 1
          σ := fun _ => none
          σ_injOn := by simp
          σ_eq_none := by simp
          span_eq := (R.sncAt i x hx).span_eq
          eval_h := by simp
          mem_bd := Submodule.mem_top
          le_span := fun g _ => by simp }
      comp_eq := fun i x hx => ⟨R.src i, R.isOpen_alt_bis i, hx, subset_rfl, fun k => k.elim0⟩
      mult := fun f a hf hfP hz => ⟨Fin.elim0, fun i x hx =>
        ⟨_, isUnit_algebraMap_locRing _ _ _ (by
          rw [ReciprocityTheory.AnForm.R.eval_bind_one]
          intro h0
          exact not_mem_conePts_top _ (hz _ (R.lift_mem i x hx) h0)), by simp⟩⟩ }
  obtain ⟨A, hA⟩ := R0.exists_atlas
  have hA' : R.IsGoodAtlas A := hA
  choose idx hidx using R.cover
  let R' : AnLogRes P J e :=
    { homog := hJ
      nondeg := hJP
      X := R.M
      A := A
      U := fun x => R.src (idx x)
      isOpen_U := fun x => R.isOpen_alt_bis (idx x)
      mem_U := hidx
      lift := fun x y q => eval (R.coord (idx x) y) (R.lift (idx x) q)
      holo := fun x p => hA'.1 (idx x) (R.lift (idx x) p)
      mem := fun x y hy => by
        rw [mem_mcPts_iff_conePts_pC]
        exact R.lift_mem (idx x) y hy
      compat := fun x x' y hy => R.compat (idx x) (idx x') y hy
      surj := fun z hz _ => by
        rw [mem_mcPts_iff_conePts_pC] at hz
        obtain ⟨i, x, hx, hxz⟩ := hsurj z hz
        exact ⟨x, sameOrbit_trans (R.compat (idx x) i x ⟨hidx x, hx⟩) hxz⟩
      inj := fun x x' _ hxx => hinj (idx x) (idx x') x (hidx x) x' (hidx x') hxx
      immersion := fun x _ p hp j hj =>
        R0.fderiv_affCoord_ker_eq_bot A hA (idx x) x (hidx x) (not_mem_conePts_top _) p hp j hj
      snc := fun f a hfP hf hz => by
        have hf' : ReciprocityTheory.AnForm.R.IsMultiHomog (map (Int.castRingHom ℂ) f) a :=
          fun m hm k => hf m (support_map_subset _ _ hm) k
        have hfP' : map (Int.castRingHom ℂ) f ∉ pC P := fun h => hfP (hPC f h)
        have hz' : ∀ z ∈ ReciprocityTheory.AnForm.R.conePts (pC P), eval z (map (Int.castRingHom ℂ) f) = 0 →
            z ∈ ReciprocityTheory.AnForm.R.conePts (pC J) := by
          intro z hz1 hz2
          rw [← mem_mcPts_iff_conePts_pC] at hz1 ⊢
          exact hz z hz1 hz2
        obtain ⟨m, hm⟩ := R.isSNC_pullback A hA' idx hidx (fun _ _ => 0) _ a hf' hfP' hz'
        exact ⟨R.rc, m, R.comp, hm⟩
      null := fun j => by
        refine MeasureTheory.measure_mono_null ?_ (R.volume_preimage_eq_zero A hA' j)
        rintro y ⟨hy1, hy2⟩
        refine ⟨hy1, idx _, hidx _, ?_⟩
        simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hy2 ⊢
        rw [← mem_mcPts_iff_conePts_pC]
        exact hy2 }
  refine ⟨R', ?_⟩
  exact
    { isOpen := fun x => R.isOpen_alt_bis (idx x)
      mem_U := hidx
      holo := fun x p => hA'.1 (idx x) (R.lift (idx x) p)
      mem := R'.mem
      compat := R'.compat
      surj := fun z hz => by
        rw [mem_mcPts_iff_conePts_pC] at hz
        obtain ⟨i, x, hx, hxz⟩ := hsurj z hz
        exact ⟨x, sameOrbit_trans (R.compat (idx x) i x ⟨hidx x, hx⟩) hxz⟩
      inj := fun x x' hxx => hinj (idx x) (idx x') x (hidx x) x' (hidx x') hxx
      immersion := fun x p hp j hj =>
        R0.fderiv_affCoord_ker_eq_bot A hA (idx x) x (hidx x) (not_mem_conePts_top _) p hp j hj }

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
  GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

theorem isEmbedded_of_isSncModel : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomogIdeal J → ¬ J ≤ mCoordIdeal y → IsSncModel y e J → ∃ R : AnLogRes (mCoordIdeal y) J e, IsEmbedded R.A (mCoordIdeal y) R.U R.lift := by
  intro K _ ι _ Ω _ _ y e J hP hJ hJP hsnc
  classical
  have hPh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) := isMultiHomogIdeal_pC hP.2.1.2.1
  have hDh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC J) := isMultiHomogIdeal_pC hJ
  obtain ⟨hcpt, hsrc⟩ := Top.compact_open_embedding K ι _ hPh
  obtain ⟨himage, htrans⟩ := chart_image_and_trans K ι _ hPh
  obtain ⟨hcover, hliftmem, hcompat, hsurj, hinj, hzero⟩ := chart_lifts_package K ι _ _ hPh hDh
  have hinv := ChartInv.chart_coord_ratio K ι _ hPh
  have hreg := GlobalTheory.T.snc_resolution_regular_local_ring K ι Ω y e J hP hsnc
  have hsc := GlobalTheory.T.snc_resolution_boundary_normal_crossing K ι Ω y e J hP hJ hJP hsnc
  let E := Fintype.equivFin ((k : K) → ι k)
  let R : ReciprocityTheory.AnForm.R.AlgRes (ι := ι) (pC (mCoordIdeal y)) (pC J) e :=
    { M := Pts (pC (mCoordIdeal y))
      compact := hcpt
      n := Fintype.card ((k : K) → ι k)
      amb := fun _ => Fintype.card (Σ k, ι k)
      ideal := fun i => ideal _ (E.symm i)
      src := fun i => src _ (E.symm i)
      isOpen_alt_bis := fun i => (hsrc _).1
      cover := fun x => by
        obtain ⟨p, hp⟩ := hcover x
        obtain ⟨i, rfl⟩ := E.symm.surjective p
        exact ⟨i, hp⟩
      coord := fun i => coord _ (E.symm i)
      isEmbedding := fun i => (hsrc _).2
      image := fun i => himage _
      trans := fun i j => htrans _ _
      regular := fun i x hx => (hreg _ x hx).1
      dim := fun i x hx => (hreg _ x hx).2
      lift := fun i => lift (E.symm i)
      lift_one := fun i => ⟨E.symm i, fun k => by simp [lift]⟩
      lift_mem := fun i => hliftmem _
      compat := fun i j => hcompat _ _
      surj := fun z hz _ => by
        obtain ⟨p, x, hx, h⟩ := hsurj z hz
        obtain ⟨i, rfl⟩ := E.symm.surjective p
        exact ⟨i, x, hx, h⟩
      inj := fun i j x hx x' hx' _ h => hinj _ _ x hx x' hx' h
      inv := fun i x hx _ p' hp' => hinv _ x hx p' hp'
      bd := fun i => bd _ (pC J) (E.symm i)
      le_bd := fun i => le_trans (Ideal.map_mono (sup_le_sup_right le_sup_left _)) Ideal.le_radical
      zero_bd := fun i => hzero _
      rc := rc _ (pC J)
      comp := comp _ (pC J)
      sncAt := fun i x hx => (hsc _ x hx).choose
      comp_eq := fun i x hx => (hsc _ x hx).choose_spec.1
      mult := fun f a hf hfP hz => ⟨fun k => ordAlong (compIdeal _ (pC J) k) _ f,
        fun i x hx => (hsc _ x hx).choose_spec.2 f a hf hfP hz⟩ }
  refine exists_isEmbedded_of_algRes hJ hJP (pcContract K ι _ e hP) R ?_ ?_ ?_
  · intro z hz
    obtain ⟨p, x, hx, h⟩ := hsurj z hz
    obtain ⟨i, rfl⟩ := E.symm.surjective p
    exact ⟨i, x, hx, h⟩
  · intro i j x hx x' hx' h
    exact hinj _ _ x hx x' hx' h
  · intro i x hx p' hp'
    exact hinv _ x hx p' hp'

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncModelEmbeddedLogResolutionStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_model_embedded_log_resolution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomogIdeal J → ¬ J ≤ mCoordIdeal y → IsSncModel y e J → ∃ R : AnLogRes (mCoordIdeal y) J e, IsEmbedded R.A (mCoordIdeal y) R.U R.lift := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.isEmbedded_of_isSncModel | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.isEmbedded_of_isSncModel | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.isEmbedded_of_isSncModel <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsAnalytic
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsAnalytic
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Pr

theorem holoMap_comp' {e₁ e₂ e₃ : ℕ} {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {C : FinHolAtlas e₁ Z} {B : FinHolAtlas e₂ Y} {A : FinHolAtlas e₃ X}
    {g : Z → Y} {f : Y → X} (hg : HoloMap C B g) (hf : HoloMap B A f) : HoloMap C A (f ∘ g) := by
  refine ⟨hf.1.comp hg.1, fun j k t ht => ?_⟩
  obtain ⟨ht1, ht2⟩ := ht
  obtain ⟨m, hm⟩ := B.cover (g ((C.chart j).symm t))
  have h1 : AnalyticAt ℂ (B.chart m ∘ g ∘ (C.chart j).symm) t := hg.2 j m t ⟨ht1, hm⟩
  have hu : (B.chart m).symm ((B.chart m ∘ g ∘ (C.chart j).symm) t) = g ((C.chart j).symm t) :=
    (B.chart m).left_inv hm
  have h2 : AnalyticAt ℂ (A.chart k ∘ f ∘ (B.chart m).symm)
      ((B.chart m ∘ g ∘ (C.chart j).symm) t) :=
    hf.2 m k _ ⟨(B.chart m).map_source hm, by
      rw [Set.mem_preimage, hu]; exact ht2⟩
  refine (h2.comp h1).congr ?_
  have hc : ContinuousAt (g ∘ (C.chart j).symm) t :=
    hg.1.continuousAt.comp ((C.chart j).continuousAt_symm ht1)
  filter_upwards [hc ((B.chart m).open_source.mem_nhds hm)] with t' ht'
  have ht'' : g ((C.chart j).symm t') ∈ (B.chart m).source := ht'
  simp only [Function.comp]
  rw [(B.chart m).left_inv ht'']

theorem injective_of_degree_one {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {π : Y → X} (hd : IsDegreeOff A B π 1 ∅) :
    Function.Injective π := by
  intro u w huw
  obtain ⟨c, hc⟩ := Set.ncard_eq_one.1 (hd.2.2.2.2.1 (π u) (Set.notMem_empty _))
  have hu : u ∈ π ⁻¹' {π u} := rfl
  have hw : w ∈ π ⁻¹' {π u} := huw.symm
  rw [hc] at hu hw
  exact hu.trans hw.symm

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_holo_of_centre {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k, ι' k)) {P : Ideal (MRing ι)} {J : Ideal (MRing ι)}
    {P' J' : Ideal (MRing ι')} {D D' : ℕ} (hJ : J = ⊤) (R : AnLogRes P J D)
    (R' : AnLogRes P' J' D') (hb : IsBlockMap κ v) (hP : P ≤ imageZ v P') :
    ∃ h : R'.X → R.X, HoloMap R'.A R.A h ∧ ∀ x, SameOrbit (R.lift (h x) (h x)) (R'.lift x x ∘ v) := by
  subst hJ
  exact Proj.holoMap_of_blockProj K ι K' ι' κ v P P' J' D D' R R' hb hP

theorem isBlockMap_v₀ (k₀ : K) :
    IsBlockMap (some : K → Option K) (v₀ (ι := ι) k₀) := by
  refine ⟨Option.some_injective _, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, m⟩ ⟨k', m'⟩ h
    have h1 : k = k' := Option.some.inj (congrArg Sigma.fst h)
    subst h1
    have h2 : m = m' := eq_of_heq (Sigma.mk.inj h).2
    rw [h2]
  · rintro ⟨o, m⟩ ⟨k, rfl⟩
    exact ⟨⟨k, m⟩, rfl⟩

def κ₁ (k₀ k : K) : Option K := if k = k₀ then none else some k

theorem isBlockMap_v₁ (k₀ : K) : IsBlockMap (κ₁ k₀) (v₁ (ι := ι) k₀) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u w h
    by_cases hu : u = k₀ <;> by_cases hw : w = k₀ <;> simp_all [κ₁]
  · rintro ⟨k, m⟩ ⟨k', m'⟩ h
    by_cases hk : k = k₀
    · subst hk
      by_cases hk' : k' = k
      · subst hk'
        rw [v₁_self, v₁_self] at h
        have h2 : m = m' := eq_of_heq (Sigma.mk.inj h).2
        rw [h2]
      · rw [v₁_self, v₁_ne (p := ⟨k', m'⟩) hk'] at h
        exact absurd (congrArg Sigma.fst h) (by simp)
    · by_cases hk' : k' = k₀
      · subst hk'
        rw [v₁_self, v₁_ne (p := ⟨k, m⟩) hk] at h
        exact absurd (congrArg Sigma.fst h) (by simp)
      · rw [v₁_ne (p := ⟨k, m⟩) hk, v₁_ne (p := ⟨k', m'⟩) hk'] at h
        have h1 : k = k' := Option.some.inj (congrArg Sigma.fst h)
        subst h1
        have h2 : m = m' := eq_of_heq (Sigma.mk.inj h).2
        rw [h2]
  · rintro ⟨k, m⟩
    by_cases hk : k = k₀
    · subst hk
      rw [v₁_self]
      simp [κ₁]
    · rw [v₁_ne (p := ⟨k, m⟩) hk]
      simp [κ₁, hk]
  · rintro ⟨o, m⟩ ⟨k, hk⟩
    by_cases e : k = k₀
    · subst e
      have ho : o = none := by
        have hk' : κ₁ k k = o := hk
        rw [← hk']; simp [κ₁]
      subst ho
      exact ⟨⟨k, m⟩, v₁_self k m⟩
    · have ho : o = some k := by
        have hk' : κ₁ k₀ k = o := hk
        rw [← hk']; simp [κ₁, e]
      subst ho
      exact ⟨⟨k, m⟩, v₁_ne (p := ⟨k, m⟩) e⟩

theorem basePart_orbit {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ}
    (h : SameOrbit z z') : SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc _, rfl⟩

theorem basePart_snd {σ : Type} {blk : σ → Option K} {k₀ : K} {s : σ} (hs : blk s = some k₀)
    (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) :
    basePart blk (sndPt k₀ z) = basePart blk (fstPt k₀ z) := by
  funext ⟨k, m⟩
  have hk : k.1 ≠ k₀ := fun e => k.2 s (by rw [hs, e])
  change z (v₁ k₀ ⟨k.1, m⟩) = z (v₀ k₀ ⟨k.1, m⟩)
  rw [v₁_ne (p := ⟨k.1, m⟩) hk]
  rfl

theorem orbit_of_two {k₀ : K} {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ}
    (h₀ : SameOrbit (fstPt k₀ z) (fstPt k₀ z')) (h₁ : SameOrbit (sndPt k₀ z) (sndPt k₀ z')) :
    SameOrbit z z' := by
  obtain ⟨c₀, hc₀, e₀⟩ := h₀
  obtain ⟨c₁, hc₁, e₁⟩ := h₁
  refine ⟨fun o => o.elim (c₁ k₀) c₀, ?_, ?_⟩
  · rintro (_ | k)
    · exact hc₁ k₀
    · exact hc₀ k
  · funext ⟨o, m⟩
    cases o with
    | none =>
      have := congrFun e₁ ⟨k₀, m⟩
      simpa [sndPt, v₁_self] using this
    | some k =>
      have := congrFun e₀ ⟨k, m⟩
      simpa [fstPt, v₀] using this

theorem two_projections : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2) → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (pr : RW.X → BM.Rb.X), HoloMap RW.A BM.Rb.A pr → (∀ x, SameOrbit (BM.Rb.lift (pr x) (pr x)) (basePart M.blk (fstPt k₀ (RW.lift x x)))) → ∃ q : Fin 2 → RW.X → FA.S.X, (∀ i, HoloMap RW.A FA.S.A (q i)) ∧ (∀ i, FA.pr ∘ q i = pr) ∧ (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) ∧ (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) ∧ (Function.Injective fun w => (q 0 w, q 1 w)) ∧ ∀ p, p ≠ (τ, a) → FA.S.ph (some p) ∘ q 0 = FA.S.ph (some p) ∘ q 1 ∧ ∀ t, FA.S.phT (some p) t ∘ q 0 = FA.S.phT (some p) t ∘ q 1 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hb hab hk ha hcb hy RW pr hpr hbase
  obtain ⟨-, -, -, hi₀, hi₁⟩ := GlobalTheory.T.flag_adjacent_swap_varieties_arithmetic K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk ha hcb hy
  have hi₁' := hi₁ (v₁ k₀) (fun p hp => v₁_ne hp) (fun m => v₁_self k₀ m)
  obtain ⟨h₀, hh₀, ho₀⟩ := exists_holo_of_centre some (v₀ k₀) FA.J_top FA.Re.R RW
    (isBlockMap_v₀ k₀) hi₀.ge
  obtain ⟨h₁, hh₁, ho₁⟩ := exists_holo_of_centre (κ₁ k₀) (v₁ k₀) FA.J_top FA.Re.R RW
    (isBlockMap_v₁ k₀) hi₁'.ge
  have hdeg := FA.Re.degree
  rw [FA.deg_one, FA.br_empty] at hdeg
  have hπ : Function.Injective FA.Re.π := injective_of_degree_one hdeg
  have hpr' : ∀ (x₁ : FA.Re.R.X) (w : RW.X) (zz : (Σ k, ι k) → ℂ),
      SameOrbit (FA.Re.R.lift x₁ x₁) zz →
      basePart M.blk zz = basePart M.blk (fstPt k₀ (RW.lift w w)) → FA.pr (FA.Re.π x₁) = pr w := by
    intro x₁ w zz h1 h2
    refine BM.Rb.inj _ _ (Proj.not_mem_mcPts_top _) ?_
    have h3 := basePart_orbit M.blk h1
    rw [h2] at h3
    exact orbit_trans (orbit_symm (FA.pr_eq x₁)) (orbit_trans h3 (orbit_symm (hbase w)))
  have hb₀ : ∀ w, FA.pr (FA.Re.π (h₀ w)) = pr w := fun w => hpr' _ w _ (ho₀ w) rfl
  have hb₁ : ∀ w, FA.pr (FA.Re.π (h₁ w)) = pr w := fun w =>
    hpr' _ w _ (ho₁ w) (basePart_snd hk (RW.lift w w))
  refine ⟨![FA.Re.π ∘ h₀, FA.Re.π ∘ h₁], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have c₀ := holoMap_comp' hh₀ FA.Re.holo
    have c₁ := holoMap_comp' hh₁ FA.Re.holo
    exact Fin.forall_fin_two.2 ⟨c₀, c₁⟩
  · exact Fin.forall_fin_two.2 ⟨funext hb₀, funext hb₁⟩
  · intro x x₀ e
    have : x₀ = h₀ x := hπ e
    subst this
    exact ho₀ x
  · intro x x₀ e
    have : x₀ = h₁ x := hπ e
    subst this
    exact ho₁ x
  · intro w w' e
    have e₀ : FA.Re.π (h₀ w) = FA.Re.π (h₀ w') := congrArg Prod.fst e
    have e₁ : FA.Re.π (h₁ w) = FA.Re.π (h₁ w') := congrArg Prod.snd e
    have f₀ := hπ e₀
    have f₁ := hπ e₁
    have g₀ : SameOrbit (fstPt k₀ (RW.lift w w)) (fstPt k₀ (RW.lift w' w')) := by
      have := ho₀ w'
      rw [← f₀] at this
      exact orbit_trans (orbit_symm (ho₀ w)) this
    have g₁ : SameOrbit (sndPt k₀ (RW.lift w w)) (sndPt k₀ (RW.lift w' w')) := by
      have := ho₁ w'
      rw [← f₁] at this
      exact orbit_trans (orbit_symm (ho₁ w)) this
    exact RW.inj w w' (Proj.not_mem_mcPts_top _) (orbit_of_two g₀ g₁)
  · intro p hp
    have key : ∀ w, FA.S.ph (some p) (FA.Re.π (h₀ w)) = FA.S.ph (some p) (FA.Re.π (h₁ w)) ∧
        ∀ t, FA.S.phT (some p) t (FA.Re.π (h₀ w)) = FA.S.phT (some p) t (FA.Re.π (h₁ w)) := by
      intro w
      refine FA.step_ph p (h₀ w) (h₁ w) ((hb₀ w).trans (hb₁ w).symm) ?_
      intro k hkp
      have hne : k ≠ k₀ := fun e => hp (M.blk_inj p (τ, a) k₀ (e ▸ hkp) hk)
      obtain ⟨c₀, -, e₀⟩ := ho₀ w
      obtain ⟨c₁, hc₁, e₁⟩ := ho₁ w
      refine ⟨c₀ k / c₁ k, fun m => ?_⟩
      have a₀ := congrFun e₀ ⟨k, m⟩
      have a₁ := congrFun e₁ ⟨k, m⟩
      simp only [Function.comp] at a₀ a₁
      rw [v₁_ne (p := ⟨k, m⟩) hne] at a₁
      rw [a₀, a₁]
      have := hc₁ k
      simp only [v₀]
      field_simp
    exact ⟨funext fun w => (key w).1, fun t => funext fun w => (key w).2 t⟩

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Pr
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsAnalyticStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_rows_analytic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2) → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (pr : RW.X → BM.Rb.X), HoloMap RW.A BM.Rb.A pr → (∀ x, SameOrbit (BM.Rb.lift (pr x) (pr x)) (basePart M.blk (fstPt k₀ (RW.lift x x)))) → ∃ q : Fin 2 → RW.X → FA.S.X, (∀ i, HoloMap RW.A FA.S.A (q i)) ∧ (∀ i, FA.pr ∘ q i = pr) ∧ (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) ∧ (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) ∧ (Function.Injective fun w => (q 0 w, q 1 w)) ∧ ∀ p, p ≠ (τ, a) → FA.S.ph (some p) ∘ q 0 = FA.S.ph (some p) ∘ q 1 ∧ ∀ t, FA.S.phT (some p) t ∘ q 0 = FA.S.phT (some p) t ∘ q 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Pr.two_projections | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Pr.two_projections | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Pr.two_projections <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SetSegreConeSmul
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver segre scaleBlock)
open ReciprocityTheory.AnForm.R (conePts)

open GoodChartDim SegreChartDim

section Dim

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem segChart_dim {Q : Ideal (MRingOver ℂ ι)} (hQp : Q.IsPrime) (hPCh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q)
    {e : ℕ} (hdim : ringKrullDim (MRingOver ℂ ι ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)) {m : ℕ}
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) {J : Ideal (MvPolynomial (Fin m) ℂ)}
    (hJ : J ∈ (setSegChartIdeal (conePts Q) σ i).minimalPrimes) :
    ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ) := by
  classical
  have hdim' : ∀ Q' ∈ Q.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q') = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    intro Q' hQ'
    rw [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff] at hQ'
    rw [hQ']
    exact hdim

  set T : Set ((Σ k, ι k) → ℂ) := MvPolynomial.zeroLocus ℂ (ReciprocityTheory.AnForm.R.chartIdeal Q i) with hT
  set S := setSegChartSet (conePts Q) σ i with hS
  have hTmem : ∀ y, y ∈ T ↔ ∀ h ∈ ReciprocityTheory.AnForm.R.chartIdeal Q i, eval y h = 0 := fun y => by
    simp [hT, MvPolynomial.mem_zeroLocus_iff]
  have hsegT : ∀ y ∈ T, (fun a => segre y (σ a)) ∈ S := by
    intro y hy
    obtain ⟨hc, h1, -⟩ := ReciprocityTheory.AnForm.R.conePts_of_chartIdeal hPCh i y ((hTmem y).1 hy)
    exact ⟨y, hc, by simp [ReciprocityTheory.ChartRestriction.G.Geo.segre, h1], rfl⟩
  have hlift_apply : ∀ z : (Σ k, ι k) → ℂ, segre z i = 1 →
      chartLift σ i (fun a => segre z (σ a)) = ReciprocityTheory.AnForm.R.affCoord i z := by
    intro z hz
    funext q
    rw [chartLift_segre_apply σ i z hz q.1 q.2]
    simp [ReciprocityTheory.AnForm.R.affCoord, div_eq_mul_inv]
  have hliftS : ∀ x ∈ S, chartLift σ i x ∈ T := by
    rintro _ ⟨z, hz, hzi, rfl⟩
    have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := fun k h0 => by
      have : segre z i = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
      rw [hzi] at this
      exact one_ne_zero this
    rw [hTmem, hlift_apply z hzi]
    exact (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hPCh i z hne).1 hz
  have hsegLift : ∀ x ∈ S, (fun a => segre (chartLift σ i x) (σ a)) = x := by
    rintro _ ⟨z, -, hzi, rfl⟩
    rw [segre_chartLift σ i z hzi]
  have hliftSeg : ∀ y ∈ T, chartLift σ i (fun a => segre y (σ a)) = y := by
    intro y hy
    obtain ⟨-, h1, -⟩ := ReciprocityTheory.AnForm.R.conePts_of_chartIdeal hPCh i y ((hTmem y).1 hy)
    have hyi : segre y i = 1 := by simp [ReciprocityTheory.ChartRestriction.G.Geo.segre, h1]
    funext q
    rw [chartLift_segre_apply σ i y hyi q.1 q.2, h1, inv_one, mul_one]

  let α : MvPolynomial (Fin m) ℂ →ₐ[ℂ] MvPolynomial (Σ k, ι k) ℂ :=
    aeval fun a => ∏ k, X ⟨k, σ a k⟩
  let β : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] MvPolynomial (Fin m) ℂ :=
    aeval fun q => X (σ.symm (Function.update i q.1 q.2))
  have hα : ∀ (y : (Σ k, ι k) → ℂ) f, eval y (α f) = eval (fun a => segre y (σ a)) f := by
    intro y f
    induction f using MvPolynomial.induction_on with
    | C c => simp [α]
    | add f g hf hg => simp [hf, hg]
    | mul_X f a hf =>
      rw [map_mul, map_mul, map_mul, hf]
      simp [α, ReciprocityTheory.ChartRestriction.G.Geo.segre, map_prod]
  have hβ : ∀ (x : Fin m → ℂ) g, eval x (β g) = eval (chartLift σ i x) g := by
    intro x g
    induction g using MvPolynomial.induction_on with
    | C c => simp [β]
    | add f g hf hg => simp [hf, hg]
    | mul_X f q hf =>
      rw [map_mul, map_mul, map_mul, hf]
      simp [β, chartLift]
  have hvanS : ∀ f, f ∈ setSegChartIdeal (conePts Q) σ i ↔ ∀ x ∈ S, eval x f = 0 := fun f => by
    simp [setSegChartIdeal, hS, MvPolynomial.mem_vanishingIdeal_iff]
  have hvanT : ∀ g, g ∈ MvPolynomial.vanishingIdeal ℂ T ↔ ∀ y ∈ T, eval y g = 0 := fun g => by
    simp [MvPolynomial.mem_vanishingIdeal_iff]
  have htr := minimalPrimes_transfer α.toRingHom β.toRingHom (setSegChartIdeal (conePts Q) σ i)
    (MvPolynomial.vanishingIdeal ℂ T)
    (fun f hf => by
      rw [Ideal.mem_comap, hvanT]
      intro y hy
      show eval y (α f) = 0
      rw [hα]
      exact (hvanS f).1 hf _ (hsegT y hy))
    (fun g hg => by
      rw [Ideal.mem_comap, hvanS]
      intro x hx
      show eval x (β g) = 0
      rw [hβ]
      exact (hvanT g).1 hg _ (hliftS x hx))
    (fun f => by
      rw [hvanS]
      intro x hx
      show eval x (β (α f) - f) = 0
      rw [map_sub, hβ, hα, hsegLift x hx, sub_self])
    (fun g => by
      rw [hvanT]
      intro y hy
      show eval y (α (β g) - g) = 0
      rw [map_sub, hα, hβ, hliftSeg y hy, sub_self])
    J hJ
  obtain ⟨hmin, hd⟩ := htr
  rw [hd]
  rw [hT, MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, Ideal.radical_minimalPrimes] at hmin
  exact ringKrullDim_of_mem_minimalPrimes_chartIdeal hPCh e hdim' i hmin

theorem setSegreCone_smul {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) [Nonempty K]
    {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) :
    ∀ c ∈ setSegreCone (conePts Q) σ, ∀ a : ℂ, a ≠ 0 → a • c ∈ setSegreCone (conePts Q) σ := by
  rintro _ ⟨z, hz, rfl⟩ a ha
  obtain ⟨z', hz', hseg⟩ := exists_segre_smul hQ hz ha
  exact ⟨z', hz', funext fun b => by simp [hseg]⟩

theorem chart_eq (S : Set ((Σ k, ι k) → ℂ)) {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    setChartSet S σ Ψ = {x | x ∈ setSegreCone S σ ∧ eval x (GroundTheory.Heights₂.Heights.linForm (psiCoeffs σ Ψ)) = 1} := by
  have hl : ∀ z : (Σ k, ι k) → ℂ,
      eval (fun a => segre z (σ a)) (GroundTheory.Heights₂.Heights.linForm (psiCoeffs σ Ψ)) = Ψ (segre z) 0 := fun z => by
    rw [show GroundTheory.Heights₂.Heights.linForm (psiCoeffs σ Ψ) = GoodChartZeroSet.linForm σ Ψ from rfl, GoodChartZeroSet.eval_linForm]
    simp
  ext x
  constructor
  · rintro ⟨z, hz, h1, rfl⟩
    exact ⟨⟨z, hz, rfl⟩, (hl z).trans h1⟩
  · rintro ⟨⟨z, hz, rfl⟩, h1⟩
    exact ⟨z, hz, (hl z).symm.trans h1, rfl⟩


omit [∀ k, Fintype (ι k)] in
theorem segChart_eq (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (a : Fin m) :
    setSegChartSet S σ (σ a) = {x | x ∈ setSegreCone S σ ∧ eval x (GroundTheory.Heights₂.Heights.linForm (Pi.single a (1 : ℂ))) = 1} := by
  ext x
  simp only [setSegChartSet, setSegreCone, Set.mem_ofPred_eq, linForm_single', eval_X]
  constructor
  · rintro ⟨z, hz, h1, rfl⟩
    exact ⟨⟨z, hz, rfl⟩, h1⟩
  · rintro ⟨⟨z, hz, rfl⟩, h1⟩
    exact ⟨z, hz, h1, rfl⟩

theorem chart_dim {Q : Ideal (MRingOver ℂ ι)} (hQp : Q.IsPrime) (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q)
    [Nonempty K] {e : ℕ} (hdim : ringKrullDim (MRingOver ℂ ι ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞))
    {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : J ∈ (setChartIdeal (conePts Q) σ Ψ).minimalPrimes) :
    ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ) := by
  classical
  have hC := setSegreCone_smul hQ σ
  set t := psiCoeffs σ Ψ
  have hS : setChartSet (conePts Q) σ Ψ = {x | x ∈ setSegreCone (conePts Q) σ ∧ eval x (GroundTheory.Heights₂.Heights.linForm t) = 1} := chart_eq _ σ Ψ
  have hJp : J.IsPrime := hJ.1.1
  have hIJ : setChartIdeal (conePts Q) σ Ψ ≤ J := hJ.1.2
  set H := vanishingIdeal ℂ (setSegreCone (conePts Q) σ)
  have hH : IsHomogIdeal H := ConeVanishingHomog.proof m _ hC
  have hHI : H ≤ setChartIdeal (conePts Q) σ Ψ := by
    rw [setChartIdeal, hS]; exact vanishingIdeal_anti_mono fun x hx => hx.1
  have hℓ1 : GroundTheory.Heights₂.Heights.linForm t - 1 ∈ setChartIdeal (conePts Q) σ Ψ := by
    rw [setChartIdeal, hS, mem_vanishingIdeal_iff]
    intro x hx
    simp [hx.2]

  obtain ⟨W, hW, hℓW, hWJ, hWcore⟩ := ChartHomogenise.proof ℂ m J t hJp (hIJ hℓ1)
  have hHW : H ≤ W := hWcore H hH (hHI.trans hIJ)
  obtain ⟨a, ha⟩ := exists_X_not_mem hℓW
  set u : Fin m → ℂ := Pi.single a 1
  have huW : GroundTheory.Heights₂.Heights.linForm u ∉ W := by rw [linForm_single']; exact ha
  have hT : setSegChartSet (conePts Q) σ (σ a) = {x | x ∈ setSegreCone (conePts Q) σ ∧ eval x (GroundTheory.Heights₂.Heights.linForm u) = 1} :=
    segChart_eq _ σ a

  have := ChartDehomogPrime.proof ℂ m W u hW huW
  have hTJ' : setSegChartIdeal (conePts Q) σ (σ a) ≤ W ⊔ Ideal.span {GroundTheory.Heights₂.Heights.linForm u - 1} := by
    rw [setSegChartIdeal, hT]; exact ConeSliceIdeal.proof m _ u W hC hHW
  obtain ⟨Q₀, hQ₀, hQ₀J'⟩ := Ideal.exists_minimalPrimes_le hTJ'
  have hdimQ₀ := segChart_dim hQp hQ hdim σ (σ a) hQ₀
  have hu1 : GroundTheory.Heights₂.Heights.linForm u - 1 ∈ setSegChartIdeal (conePts Q) σ (σ a) := by
    rw [setSegChartIdeal, hT, mem_vanishingIdeal_iff]
    intro x hx
    simp [hx.2]
  have hHT : H ≤ setSegChartIdeal (conePts Q) σ (σ a) := by
    rw [setSegChartIdeal, hT]; exact vanishingIdeal_anti_mono fun x hx => hx.1
  obtain ⟨V, hV, huV, hVQ₀, hVcore⟩ := ChartHomogenise.proof ℂ m Q₀ u hQ₀.1.1 (hQ₀.1.2 hu1)
  have hHV : H ≤ V := hVcore H hH (hHT.trans hQ₀.1.2)
  have hVW : V ≤ W := le_of_homog_le_sup hV.isHomog hW.isPrime hW.isHomog huW
    ((le_sup_left.trans hVQ₀.le).trans hQ₀J')

  have hIV : setChartIdeal (conePts Q) σ Ψ ≤ V ⊔ Ideal.span {GroundTheory.Heights₂.Heights.linForm t - 1} := by
    rw [setChartIdeal, hS]; exact ConeSliceIdeal.proof m _ t V hC hHV
  have hVJ : V ⊔ Ideal.span {GroundTheory.Heights₂.Heights.linForm t - 1} ≤ J :=
    sup_le (hVW.trans (le_sup_left.trans hWJ.le)) ((Ideal.span_singleton_le_iff_mem _).2 (hIJ hℓ1))
  have hJmin : J ∈ (V ⊔ Ideal.span {GroundTheory.Heights₂.Heights.linForm t - 1}).minimalPrimes :=
    ⟨⟨hJp, hVJ⟩, fun Z hZ hZJ => hJ.2 ⟨hZ.1, hIV.trans hZ.2⟩ hZJ⟩
  have hQ₀min : Q₀ ∈ (V ⊔ Ideal.span {GroundTheory.Heights₂.Heights.linForm u - 1}).minimalPrimes := by
    have := hQ₀.1.1
    rw [hVQ₀, Ideal.minimalPrimes_eq_subsingleton_self]
    rfl

  have d₁ := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.dimPIT ℂ (Fin m) V J (GroundTheory.Heights₂.Heights.linForm t - 1) hV.isPrime
    (linForm_sub_one_not_mem hV.isHomog hV.isPrime.ne_top t) hJmin
  have d₂ := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.dimPIT ℂ (Fin m) V Q₀ (GroundTheory.Heights₂.Heights.linForm u - 1) hV.isPrime
    (linForm_sub_one_not_mem hV.isHomog hV.isPrime.ne_top u) hQ₀min
  rw [← d₂, hdimQ₀] at d₁
  exact eq_of_add_one_eq d₁

end Dim

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end
