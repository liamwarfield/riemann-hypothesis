module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerMeasureNormalisationSymm
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.FiniteDimensionalOfOrtho
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Counterexamples.TransversalityLocal.FramePairFixatorUnitaryAndFixesFrame

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteLatticeDiscriminantModuleCardDetSq
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteLatticeDiscriminantModuleCardDetSq
namespace GlobalTheory.LoopC.DetCard

section General

open NumberField GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.MainNotions.S

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V] [Module K V]
  [IsScalarTower (𝓞 K) K V]

theorem map_latIn {U : Submodule K V} {N : Submodule (𝓞 K) V} (hN : ∀ x ∈ N, x ∈ U) :
    N.toAddSubgroup = (latIn U N).toAddSubgroup.map U.subtype.toAddMonoidHom := by
  ext x
  constructor
  · intro h1
    exact ⟨⟨x, hN x h1⟩, h1, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

theorem idxN_latIn {U : Submodule K V} {A B : Submodule (𝓞 K) V} (hA : ∀ x ∈ A, x ∈ U)
    (hB : ∀ x ∈ B, x ∈ U) : idxN A B = idxN (latIn U A) (latIn U B) := by
  rw [idxN, idxN, map_latIn hA, map_latIn hB, AddSubgroup.relIndex_map_map_of_injective _ _ U.injective_subtype]

theorem isLattice_latIn_span {U : Submodule K V} {N : Submodule (𝓞 K) V} (hN : N.FG)
    (hU : Submodule.span K (N : Set V) = U) : Submodule.IsFullLattice K (latIn U N) := by
  haveI : Submodule.IsLattice K (latIn U N) := by
    apply Submodule.IsLattice.of_fg K
    refine Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars (𝓞 K)) U.injective_subtype ?_
    exact Submodule.FG.of_le hN (Submodule.map_comap_le _ _)
  refine ⟨?_⟩
  apply Submodule.map_injective_of_injective U.injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  rw [← hU]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hU ▸ Submodule.subset_span hx⟩, hx, rfl⟩

variable [StarRing K]

theorem latIn_dualInH (h : V →ₗ⋆[K] V →ₗ[K] K) {U : Submodule K V} {N : Submodule (𝓞 K) V}
    (hU : Submodule.span K (N : Set V) = U) :
    latIn U (Lat.dualInH h N) = dual (hRes h U) (latIn U N) := by
  ext x
  constructor
  · rintro ⟨h1, -⟩
    exact (dualBasic_mem_dual _ _ _).2 fun y hy => (dualBasic_mem_dual _ _ _).1 h1 y hy
  · intro hx
    refine ⟨(dualBasic_mem_dual _ _ _).2 fun z hz => ?_, ?_⟩
    · exact (dualBasic_mem_dual _ _ _).1 hx ⟨z, hU ▸ Submodule.subset_span hz⟩ hz
    · change (x : V) ∈ Submodule.span K (N : Set V)
      rw [hU]
      exact x.2

theorem idxN_dualInH (h : V →ₗ⋆[K] V →ₗ[K] K) {U : Submodule K V} {N : Submodule (𝓞 K) V}
    (hU : Submodule.span K (N : Set V) = U) :
    idxN (Lat.dualInH h N) N = discN (hRes h U) (latIn U N) := by
  rw [idxN_latIn (U := U) (A := Lat.dualInH h N) (B := N) (fun x hx => hU ▸ (Submodule.mem_inf.1 hx).2) (fun x hx => hU ▸ Submodule.subset_span hx),
    latIn_dualInH h hU, discN]

theorem general [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hK : IsCMUnram K) (hs : h.IsSymm) (hp : PD h)
    (M : Submodule (𝓞 K) V) (hM : M.FG) (hI : IsIntegralLat h M) :
    1 ≤ idxN (Lat.dualInH h M) M ∧ (idxN (Lat.dualInH h M) M : ℝ) = Lat.latDetH h M ^ 2 ∧
      ∀ P : Submodule (𝓞 K) V, P ≤ M →
        Module.finrank K (Submodule.span K (P : Set V)) = Module.finrank K (Submodule.span K (M : Set V)) →
        1 ≤ idxN M P ∧ Lat.latDetH h P = Lat.latDetH h M * idxN M P := by
  set U := Submodule.span K (M : Set V) with hUdef
  have hsU : (hRes h U).IsSymm := ⟨fun x y => hs.eq x y⟩
  have hpU : PD (hRes h U) := fun τ x hx => hp τ x fun e => hx (Subtype.ext e)
  have hnU := DetAgree.nondeg_of_pd hpU
  have key : ∀ N : Submodule (𝓞 K) V, N ≤ M → Submodule.span K (N : Set V) = U →
      IsIntLat (hRes h U) (latIn U N) ∧ discN (hRes h U) (latIn U N) ≠ 0 ∧
        Lat.latDetH h N = Real.sqrt (discN (hRes h U) (latIn U N) : ℝ) := by
    intro N hN hU
    have a : IsIntLat (hRes h U) (latIn U N) :=
      ⟨isLattice_latIn_span (hM.of_le hN) hU, fun x hx y hy => hI x (hN hx) y (hN hy)⟩
    have n0 := (DiscOrder.main K U _ hK hsU hnU _ a).1
    refine ⟨a, n0, ?_⟩
    rw [← idxN_dualInH h hU] at n0 ⊢
    rw [Lat.latDetH, DetAgree.genIdxH_eq_idxN _ n0]
    intro x hx
    exact ⟨(dualBasic_mem_dual _ _ _).2 fun y hy => hI y (hN hy) x (hN hx), Submodule.subset_span hx⟩
  obtain ⟨m1, m2, m3⟩ := key M le_rfl rfl
  refine ⟨?_, ?_, fun P hP hr => ?_⟩
  · rw [idxN_dualInH h hUdef.symm]
    exact Nat.pos_of_ne_zero m2
  · rw [idxN_dualInH h hUdef.symm, m3, Real.sq_sqrt (Nat.cast_nonneg _)]
  · have hU : Submodule.span K (P : Set V) = U :=
      Submodule.eq_of_le_of_finrank_eq (Submodule.span_mono hP) hr
    obtain ⟨p1, -, p3⟩ := key P hP hU
    obtain ⟨q1, q2⟩ := (DiscOrder.main K U _ hK hsU hnU _ p1).2.2.1 _ m1 (Submodule.comap_mono hP)
    rw [← idxN_latIn (U := U) (fun x hx => Submodule.subset_span hx)
      (fun x hx => Submodule.subset_span (hP hx))] at q1 q2
    refine ⟨Nat.pos_of_ne_zero q1, ?_⟩
    rw [p3, m3, q2, Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul (Nat.cast_nonneg _),
      Real.sqrt_sq (Nat.cast_nonneg _)]

end General

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem main : ∀ (D : D7) (M : LatW D), M.FG → IsPosDef (D.sp.X 0).hT → Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT M → 1 ≤ idxW D (dualInH (D.sp.X 0).hT M) M ∧ (idxW D (dualInH (D.sp.X 0).hT M) M : ℝ) = detW D M ^ 2 ∧ ∀ P : LatW D, P ≤ M → rkW D P = rkW D M → 1 ≤ idxW D M P ∧ detW D P = detW D M * idxW D M P := by
  intro D M hM hp hI
  exact general (D.sp.X 0).hT D.sp.cm.cmUnram (D.sp.X 0).herm hp M hM hI

end GlobalTheory.LoopC.DetCard
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteLatticeDiscriminantModuleCardDetSqStatement
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteLattice_discriminantModule_card_det_sq : ∀ (D : D7) (M : LatW D), M.FG → IsPosDef (D.sp.X 0).hT → Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT M → 1 ≤ idxW D (dualInH (D.sp.X 0).hT M) M ∧ (idxW D (dualInH (D.sp.X 0).hT M) M : ℝ) = detW D M ^ 2 ∧ ∀ P : LatW D, P ≤ M → rkW D P = rkW D M → 1 ≤ idxW D M P ∧ detW D P = detW D M * idxW D M P := by
  first | exact @GlobalTheory.LoopC.DetCard.main | exact GlobalTheory.LoopC.DetCard.main | (intros; apply GlobalTheory.LoopC.DetCard.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StdLatIsOrthoLatticeAndMassProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StdLatIsOrthoLatticeAndMassProperties
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical

namespace GlobalTheory.Mass.StdMass

theorem _root_.GlobalTheory.Mass.StdMass.isSymm_of_ortho {K V : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {n : ℕ} (hL : _root_.Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) :
    h.IsSymm := by
  unfold _root_.Formalism.HermitianLatticesTheory.IsOrthoLattice at hL
  obtain ⟨e, -, hspan, -, horth⟩ := hL
  refine LinearMap.IsSymm.mk fun x y => ?_
  obtain ⟨c, rfl⟩ := _root_.ReciprocityTheory.ChartRestriction.L3.StandardSymmetricSums.exists_coord hspan x
  obtain ⟨d, rfl⟩ := _root_.ReciprocityTheory.ChartRestriction.L3.StandardSymmetricSums.exists_coord hspan y
  rw [_root_.ReciprocityTheory.ChartRestriction.L3.StandardSymmetricSums.form_sum horth, _root_.ReciprocityTheory.ChartRestriction.L3.StandardSymmetricSums.form_sum horth]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, starRingEnd_apply, star_mul, star_star]

private theorem massU_zero_eq_one (K : Type) [Field K] [NumberField K] [StarRing K] :
    _root_.Formalism.MainNotions.S.Cnt.massU K 0 = 1 := by
  have hsub : ∀ M N : Submodule (𝓞 K) (Fin 0 → K), M = N := fun M N => Subsingleton.elim M N
  haveI : Subsingleton ((Fin 0 → K) ≃ₗ[K] (Fin 0 → K)) :=
    ⟨fun f g => LinearEquiv.ext fun x => Subsingleton.elim _ _⟩
  have hlat : Submodule.IsLattice K (_root_.Formalism.MainNotions.S.Cnt.stdLat K 0) := _root_.ReciprocityTheory.ChartRestriction.L3.isLattice_of_ortho (_root_.Formalism.MainNotions.StandardLattice.stdLat_ortho K 0)
  have hfull : Submodule.IsFullLattice K (_root_.Formalism.MainNotions.S.Cnt.stdLat K 0) :=
    { toIsLattice := hlat, span_eq_top := Subsingleton.elim _ _ }
  have hgen : _root_.Formalism.MainNotions.S.Cnt.stdLat K 0 ∈ _root_.Formalism.HermitianLatticesTheory.genus (_root_.Formalism.MainNotions.S.Cnt.stdH K 0) (_root_.Formalism.MainNotions.S.Cnt.stdLat K 0) := by
    unfold _root_.Formalism.HermitianLatticesTheory.genus _root_.Formalism.HermitianLatticesTheory.SameGenus
    exact ⟨hfull, fun p _ => ⟨1, one_mem _, hsub _ _⟩⟩
  have hs : ∃ s, _root_.Formalism.ThetaLiftIndependence.IsClassReps (_root_.Formalism.MainNotions.S.Cnt.stdH K 0) (_root_.Formalism.MainNotions.S.Cnt.stdLat K 0) s := by
    refine ⟨{_root_.Formalism.MainNotions.S.Cnt.stdLat K 0}, ?_⟩
    unfold _root_.Formalism.ThetaLiftIndependence.IsClassReps
    refine ⟨fun M hM => ?_, fun M _ => ⟨_root_.Formalism.MainNotions.S.Cnt.stdLat K 0,
      ⟨Finset.mem_singleton_self _, 1, one_mem _, hsub _ _⟩,
      fun N hN => Finset.mem_singleton.mp hN.1⟩⟩
    rw [Finset.mem_singleton.mp hM]
    exact hgen
  have hchoose : hs.choose = {_root_.Formalism.MainNotions.S.Cnt.stdLat K 0} := by
    have hspec := hs.choose_spec
    unfold _root_.Formalism.ThetaLiftIndependence.IsClassReps at hspec
    obtain ⟨N, ⟨hN, -⟩, -⟩ := hspec.2 _ hgen
    rw [Finset.eq_singleton_iff_unique_mem]
    refine ⟨?_, fun M _ => hsub _ _⟩
    have hN' : N = _root_.Formalism.MainNotions.S.Cnt.stdLat K 0 := hsub _ _
    exact hN' ▸ hN
  have hcard : Nat.card (_root_.Formalism.ThetaLiftIndependence.autL (_root_.Formalism.MainNotions.S.Cnt.stdH K 0) (_root_.Formalism.MainNotions.S.Cnt.stdLat K 0)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨inferInstance, ⟨⟨1, ?_⟩⟩⟩
    unfold _root_.Formalism.ThetaLiftIndependence.autL
    exact ⟨one_mem _, hsub _ _⟩
  unfold _root_.Formalism.MainNotions.S.Cnt.massU
  rw [_root_.Formalism.HermitianLatticesTheory.massBasic_mass_eq _ _ hs, hchoose, Finset.sum_singleton, hcard]
  norm_num

theorem _root_.GlobalTheory.Mass.StdMass.main : ∀ (K : Type) [Field K] [NumberField K]
    [StarRing K], _root_.Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ j : ℕ, (_root_.Formalism.MainNotions.S.Cnt.stdH K j).IsSymm ∧
      _root_.Formalism.HermitianLatticesTheory.IsOrthoLattice (_root_.Formalism.MainNotions.S.Cnt.stdH K j) (_root_.Formalism.MainNotions.S.Cnt.stdLat K j) j ∧ 0 < _root_.Formalism.MainNotions.S.Cnt.massU K j ∧ _root_.Formalism.MainNotions.S.Cnt.massU K 0 = 1 ∧
      ∀ (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
        (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V), _root_.Formalism.HermitianLatticesTheory.IsOrthoLattice h L j →
        _root_.Formalism.HermitianLatticesTheory.mass h L = _root_.Formalism.MainNotions.S.Cnt.massU K j ∧ _root_.GlobalTheory.Mass.PD h := by
  intro K _ _ _ hK j
  have hsymm : (_root_.Formalism.MainNotions.S.Cnt.stdH K j).IsSymm := _root_.ReciprocityTheory.ChartRestriction.L3.stdForm_isSymm K j
  have hortho : _root_.Formalism.HermitianLatticesTheory.IsOrthoLattice (_root_.Formalism.MainNotions.S.Cnt.stdH K j) (_root_.Formalism.MainNotions.S.Cnt.stdLat K j) j := _root_.Formalism.MainNotions.StandardLattice.stdLat_ortho K j
  refine ⟨hsymm, hortho, ?_, massU_zero_eq_one K, fun V _ _ _ _ h L hL => ⟨?_, ?_⟩⟩
  · unfold _root_.Formalism.MainNotions.S.Cnt.massU
    exact _root_.ReciprocityTheory.ChartRestriction.L3.mass_pos_of_ortho hK hsymm hortho
  · exact (_root_.Formalism.MainNotions.StandardLattice.mass_ortho K hK j V h L hL).trans rfl
  · have hpos := _root_.ReciprocityTheory.ChartRestriction.L3.isTotPosDef_of_ortho hK (_root_.GlobalTheory.Mass.StdMass.isSymm_of_ortho hL) hL
    unfold _root_.ReciprocityTheory.ChartRestriction.L3.IsTotPosDef at hpos
    unfold _root_.GlobalTheory.Mass.PD
    exact fun τ x hx => hpos x hx τ

end GlobalTheory.Mass.StdMass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StdLatIsOrthoLatticeAndMassPropertiesStatement
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdLat_isOrthoLattice_and_mass_properties : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], IsCMUnram K → ∀ j : ℕ, (Cnt.stdH K j).IsSymm ∧ IsOrthoLattice (Cnt.stdH K j) (Cnt.stdLat K j) j ∧ 0 < Cnt.massU K j ∧ Cnt.massU K 0 = 1 ∧ ∀ (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V), IsOrthoLattice h L j → mass h L = Cnt.massU K j ∧ PD h := by
  first | exact @GlobalTheory.Mass.StdMass.main | exact GlobalTheory.Mass.StdMass.main | (intros; apply GlobalTheory.Mass.StdMass.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamPSizesRecord
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem sizes_record_at {D : D7} (L : SizeData₂ D) (h : SizesAt L) (Cs : ℝ) (hCs : 5 ≤ Cs)
    (hx : 16 ≤ L.sc.x) (j : Fin 2) :
    Real.exp (8 * L.sc.x ^ L.sc.eps) ≤ (D.host.g j : ℝ) ∧ L.sc.x ^ 2 ≤ (D.R.f : ℝ) ∧
      (D.R.f : ℝ) ≤ L.sc.x ^ Cs ∧ (D.R.m : ℝ) ≤ L.sc.x ^ Cs ∧ 100 ≤ D.R.r ∧
      (D.R.r : ℝ) ≤ L.sc.x ^ Cs ∧
      Real.exp (L.sc.x ^ (L.sc.ez / 6)) ≤ ((min D.host.q D.host.d : ℕ) : ℝ) := by
  obtain ⟨hN, -, hK, -, -, -, hQ, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -⟩ := h
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he0 := L.sc.eps_pos
  have he1 := L.sc.eps_lt
  have hmk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hfk : D.R.f ≤ D.R.k := D.R.f_le_k
  have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hkb : (D.R.k : ℝ) ≤ L.sc.x ^ (19 / 4 : ℝ) := by
    refine hK.2.trans (Real.rpow_le_rpow_of_exponent_le hx1.le ?_)
    unfold szTh
    linarith
  have h2 : (2 : ℝ) ≤ L.sc.x ^ (1 / 4 : ℝ) := by
    have e : (2 : ℝ) = (16 : ℝ) ^ (1 / 4 : ℝ) := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [e]
    exact Real.rpow_le_rpow (by norm_num) hx (by norm_num)
  have h2k : 2 * (D.R.k : ℝ) ≤ L.sc.x ^ Cs := by
    calc 2 * (D.R.k : ℝ) ≤ L.sc.x ^ (1 / 4 : ℝ) * L.sc.x ^ (19 / 4 : ℝ) :=
          mul_le_mul h2 hkb (by linarith) (by linarith)
      _ = L.sc.x ^ (5 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
      _ ≤ L.sc.x ^ Cs := Real.rpow_le_rpow_of_exponent_le hx1.le hCs
  have hn : L.sc.x ^ 2 ≤ (D.R.n : ℝ) := by
    refine le_trans ?_ hN.1
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hx1.le
    unfold szTh
    push_cast
    linarith
  have hf : L.sc.x ^ 2 ≤ (D.R.f : ℝ) := by
    refine hn.trans ?_
    exact_mod_cast (by unfold Ranks.f; omega : D.R.n ≤ D.R.f)
  have hfk' : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast hfk
  have hmk' : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hr : (D.R.r : ℝ) ≤ 2 * (D.R.k : ℝ) := by
    exact_mod_cast (by unfold Ranks.r; omega : D.R.r ≤ 2 * D.R.k)
  have hf100 : 100 ≤ D.R.f := by
    have : (100 : ℝ) ≤ D.R.f := by nlinarith
    exact_mod_cast this
  refine ⟨?_, hf, by linarith, by linarith, by unfold Ranks.r; omega, by linarith, ?_⟩
  · refine le_trans ?_ (hG j j).1
    have e : Real.exp (8 * L.sc.x ^ L.sc.eps) = L.sc.b ^ 8 := by
      unfold Scale.b Scale.L
      rw [← Real.exp_nat_mul]
      norm_num
    have hb : 0 < L.sc.b := Real.exp_pos _
    rw [e]
    exact pow_le_pow_left₀ hb.le (le_mul_of_one_le_left hb.le hk1) 8
  · have hq : (0 : ℝ) < D.host.q := by
      have := D.host.qd_big.1
      exact_mod_cast (by omega : 0 < D.host.q)
    have hd : (0 : ℝ) < D.host.d := by
      have := D.host.qd_big.2
      exact_mod_cast (by omega : 0 < D.host.d)
    rw [Nat.cast_min]
    refine le_min ((Real.le_log_iff_exp_le hq).1 hQ.1) ((Real.le_log_iff_exp_le hd).1 ?_)
    refine le_trans (Real.rpow_le_rpow_of_exponent_le hx1.le ?_) hQ.2.2.2.1
    have := L.sc.ez_pos
    linarith

theorem family_eventually_size_bounds : ∀ (eps : ℝ) (Fm : FamP eps) (Cs : ℝ), 5 ≤ Cs → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (j : Fin 2), Real.exp (8 * x ^ eps) ≤ ((Fm.D x i).host.g j : ℝ) ∧ x ^ 2 ≤ ((Fm.D x i).R.f : ℝ) ∧ ((Fm.D x i).R.f : ℝ) ≤ x ^ Cs ∧ ((Fm.D x i).R.m : ℝ) ≤ x ^ Cs ∧ 100 ≤ (Fm.D x i).R.r ∧ ((Fm.D x i).R.r : ℝ) ≤ x ^ Cs ∧ Real.exp (x ^ (Fm.ez / 6)) ≤ ((min (Fm.D x i).host.q (Fm.D x i).host.d : ℕ) : ℝ) := by
  intro eps Fm Cs hCs
  refine ⟨max 16 (Fm.x1 + 1), fun x hx i j => ?_⟩
  have h16 : 16 ≤ x := (le_max_left _ _).trans hx
  have hx1 : Fm.x1 < x := by linarith [(le_max_right _ _).trans hx]
  have := sizes_record_at (Fm.L x i) (Fm.sizes x hx1 i) Cs hCs (by rw [Fm.L_x x i hx1]; exact h16) j
  rw [Fm.L_x x i hx1, Fm.L_eps x i, Fm.L_ez x i] at this
  exact this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitRepsOver
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.LocOver

theorem orbit_reps_over : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V]
    [Module E V] (H : HermSp M V) (r : ℕ), ∀ P : FPair H r, Equivalence (Datum.Rel (P := P)) ∧ Nonempty (Reps P) ∧
    ∀ (d d' : Datum P) (t : Term V M r), Datum.Rel d d' → Over P d t → Over P d' t := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ H r P
  have he := GlobalTheory.NonGenericLocalCheck.rel_equiv P
  refine ⟨he, GlobalTheory.NonGenericLocalCheck.reps_nonempty P, ?_⟩
  rintro d d' t hdd' ⟨g, hg, d'', h1, h2⟩
  exact ⟨g, hg, d'', he.trans (he.symm hdd') h1, h2⟩

end GlobalTheory.LocOver
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinprodPlacesOverTypePrimesSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinprodPlacesOverTypePrimesSplit
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory.TypedPlacesProduct

theorem finite_over {K : Type*} [Field K] [NumberField K] {n : ℕ} (hn : n ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | ((n : ℕ) : 𝓞 K) ∈ v.asIdeal}.Finite := by
  have hI : Ideal.span {((n : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr hn
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem finprod_over {K : Type*} [Field K] [NumberField K] {n f : ℕ} (hn : n ≠ 0) (φ : ℝ → ℝ)
    (hc : Nat.card {v : HeightOneSpectrum (𝓞 K) // ((n : ℕ) : 𝓞 K) ∈ v.asIdeal} = f)
    (hq : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal →
      Nat.card (𝓞 K ⧸ v.asIdeal) = n) :
    (∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 K) | ((n : ℕ) : 𝓞 K) ∈ p.asIdeal},
      φ (Ideal.absNorm p.asIdeal : ℝ)) = φ n ^ f := by
  have hs := finite_over (K := K) hn
  have hnorm : ∀ p ∈ {p : HeightOneSpectrum (𝓞 K) | ((n : ℕ) : 𝓞 K) ∈ p.asIdeal},
      φ (Ideal.absNorm p.asIdeal : ℝ) = φ n := by
    intro p hp
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, hq p hp]
  rw [finprod_mem_congr rfl hnorm, finprod_mem_eq_finite_toFinset_prod _ hs, Finset.prod_const,
    ← Nat.card_eq_card_finite_toFinset hs]
  exact congrArg _ hc

private lemma disjoint_primes_dvd_of_coprime {K : Type*} [Field K] [NumberField K] {a b : ℕ} (hab : Nat.Coprime a b) :
    Disjoint {p : HeightOneSpectrum (𝓞 K) | ((a : ℕ) : 𝓞 K) ∈ p.asIdeal}
      {p : HeightOneSpectrum (𝓞 K) | ((b : ℕ) : 𝓞 K) ∈ p.asIdeal} := by
  rw [Set.disjoint_left]
  intro p ha hb
  obtain ⟨u, w, huw⟩ := (Nat.isCoprime_iff_coprime.mpr hab).map (Int.castRingHom (𝓞 K))
  have h1 : (1 : 𝓞 K) ∈ p.asIdeal := by
    rw [← huw]
    simp only [eq_intCast, Int.cast_natCast]
    exact p.asIdeal.add_mem (p.asIdeal.mul_mem_left _ ha) (p.asIdeal.mul_mem_left _ hb)
  exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem finprod_typed_places : ∀ (D : D7) (φ : ℝ → ℝ), (∀ i, StandardLattice.SplitsF D (D.host.g i)) → (∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal ∨ ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}, φ (Ideal.absNorm p.asIdeal : ℝ)) = φ (D.host.g 0) ^ D.R.f * φ (D.host.g 1) ^ D.R.f := by
  intro D φ hs
  have hp := D.host.g_prime
  have hne : D.host.g 0 ≠ D.host.g 1 := D.host.g_ne
  have hcop : Nat.Coprime (D.host.g 0) (D.host.g 1) := (Nat.coprime_primes (hp 0) (hp 1)).mpr hne
  rw [Set.setOf_or, finprod_mem_union (disjoint_primes_dvd_of_coprime hcop) (finite_over (hp 0).ne_zero)
    (finite_over (hp 1).ne_zero), finprod_over (hp 0).ne_zero φ (hs 0).1 (hs 0).2,
    finprod_over (hp 1).ne_zero φ (hs 1).1 (hs 1).2]

end GlobalTheory.TypedPlacesProduct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinprodPlacesOverTypePrimesSplitStatement
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finprod_places_over_typePrimes_split : ∀ (D : D7) (φ : ℝ → ℝ), (∀ i, StandardLattice.SplitsF D (D.host.g i)) → (∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal ∨ ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}, φ (Ideal.absNorm p.asIdeal : ℝ)) = φ (D.host.g 0) ^ D.R.f * φ (D.host.g 1) ^ D.R.f := by
  first | exact @GlobalTheory.TypedPlacesProduct.finprod_typed_places | exact GlobalTheory.TypedPlacesProduct.finprod_typed_places | (intros; apply GlobalTheory.TypedPlacesProduct.finprod_typed_places <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTermLocalTermMoveOfIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTermLocalTermMoveOfIsometry
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.LocOver.MoveTerm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem mem_img (g : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) (x : V) : x ∈ img g Λ ↔ g.symm x ∈ Λ := by
  unfold img
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨g.symm x, h, by simp⟩

theorem map_mem_span_range {R : Type} [Semiring R] [Module R V] (φ : V →ₗ[R] V) {ι : Type} (v : ι → V)
    {x : V} (hx : x ∈ Submodule.span R (Set.range v)) :
    φ x ∈ Submodule.span R (Set.range fun a => φ (v a)) := by
  have := Submodule.apply_mem_span_image_of_mem_span φ hx
  rwa [← Set.range_comp] at this

variable (H : HermSp M V)

theorem h_symm {g : V ≃ₗ[E] V} (hg : IsUnitary H g) (x y : V) : H.h (g.symm x) (g.symm y) = H.h x y := by
  rw [← hg]; simp

theorem isSelfDual_img {g : V ≃ₗ[E] V} (hg : IsUnitary H g) {Λ : Submodule M.L.O V}
    (h : H.IsSelfDual Λ) : H.IsSelfDual (img g Λ) := by
  obtain ⟨hfg, hspan, hdual⟩ := h
  refine ⟨hfg.map _, ?_, fun x => ?_⟩
  · rw [eq_top_iff]
    intro x _
    have h1 : g.symm x ∈ Submodule.span E (Λ : Set V) := by rw [hspan]; trivial
    have h2 := Submodule.apply_mem_span_image_of_mem_span (g : V →ₗ[E] V) h1
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_img g Λ _).2 (by simpa using hy)
  · rw [mem_img, hdual (g.symm x)]
    constructor
    · intro h y hy
      have := h _ ((mem_img g Λ y).1 hy)
      rwa [h_symm H hg] at this
    · intro h y hy
      have := h (g y) ((mem_img g Λ _).2 (by simpa using hy))
      rw [← hg (g.symm x) y, LinearEquiv.apply_symm_apply]; exact this

theorem prim_img (g : V ≃ₗ[E] V) {Λ : Submodule M.L.O V} {ι : Type} {v : ι → V}
    (h : H.Prim Λ v) : H.Prim (img g Λ) (fun a => g (v a)) := by
  obtain ⟨hmem, hli, hsat⟩ := h
  refine ⟨fun a => (mem_img g Λ _).2 (by simpa using hmem a), ?_, fun x hx hxs => ?_⟩
  · exact hli.map' (g : V →ₗ[E] V) (LinearEquiv.ker g)
  · have h1 : g.symm x ∈ Submodule.span E (Set.range v) := by
      have := map_mem_span_range (g.symm : V →ₗ[E] V) _ hxs
      simpa using this
    have h2 := hsat _ ((mem_img g Λ x).1 hx) h1
    have h3 := map_mem_span_range ((g : V →ₗ[E] V).restrictScalars M.L.O) _ h2
    simpa using h3

theorem isFrame_img {g : V ≃ₗ[E] V} (hg : IsUnitary H g) {Λ : Submodule M.L.O V} {r : ℕ}
    {f : Fin (r + 1) → V} {T : F} (h : H.IsFrame Λ r f T) :
    H.IsFrame (img g Λ) r (fun a => g (f a)) T := by
  obtain ⟨hp, hiso, hz, hT, hT0⟩ := h
  refine ⟨prim_img H g hp, fun a b hab => ?_, ?_, hT, hT0⟩
  · rw [hg]; exact hiso a b hab
  · rw [hg]; exact hz

theorem smulLat_img (g : V ≃ₗ[E] V) (c : E) {Λ : Submodule M.L.O V} {y : V}
    (hy : y ∈ H.smulLat c Λ) : g y ∈ H.smulLat c (img g Λ) := by
  unfold HermSp.smulLat at hy ⊢
  have := Submodule.apply_mem_span_image_of_mem_span ((g : V →ₗ[E] V).restrictScalars M.L.O) hy
  refine Submodule.span_mono ?_ (by simpa using this)
  rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  exact ⟨g w, (mem_img g Λ _).2 (by simpa using hw), by simp⟩

theorem zhat_move {g : V ≃ₗ[E] V} (hg : IsUnitary H g) {r : ℕ} (f f' : Fin (r + 1) → V) :
    H.Zhat (fun a => g (f a)) (fun b => g (f' b)) = H.Zhat f f' := by
  ext a b
  exact hg _ _

theorem isTerm_move {r : ℕ} (g : V ≃ₗ[E] V) (t : Term V M r) (hg : IsUnitary H g) (ht : H.IsTerm t) :
    H.IsTerm (GlobalTheory.LocOver.move g t) := by
  obtain ⟨hSD, hF, hF', hU, hG, hsplit⟩ := ht
  have hD : ∀ l, H.Dl (GlobalTheory.LocOver.move g t).f (GlobalTheory.LocOver.move g t).f' l = H.Dl t.f t.f' l := by
    intro l
    unfold HermSp.Dl
    rw [show (GlobalTheory.LocOver.move g t).f = fun a => g (t.f a) from rfl,
      show (GlobalTheory.LocOver.move g t).f' = fun a => g (t.f' a) from rfl, zhat_move H hg]
  refine ⟨isSelfDual_img H hg hSD, isFrame_img H hg hF, isFrame_img H hg hF', ?_, ?_, fun gs hgs => ?_⟩
  · rw [hD]; exact hU
  · unfold HermSp.Gdet
    rw [hD, hD]
    exact hG
  · obtain ⟨h1, h2, h3⟩ := hsplit gs hgs
    refine ⟨h1, h2, fun b => ?_⟩
    show g (t.f' b) - g (t.f b) ∈ H.smulLat _ (img g t.abelian₂)
    rw [← map_sub]
    exact smulLat_img H g _ (h3 b)

end GlobalTheory.LocOver.MoveTerm

theorem GlobalTheory.LocOver.isTerm_move_of_unitary : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ} (g : V ≃ₗ[E] V) (t : Term V M r), IsUnitary H g → H.IsTerm t → H.IsTerm (GlobalTheory.LocOver.move g t) :=
  fun H _ g t hg ht => GlobalTheory.LocOver.MoveTerm.isTerm_move H g t hg ht
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTermLocalTermMoveOfIsometryStatement
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTerm_localTermMove_of_isometry : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ} (g : V ≃ₗ[E] V) (t : Term V M r), IsUnitary H g → H.IsTerm t → H.IsTerm (GlobalTheory.LocOver.move g t) := by
  first | exact @GlobalTheory.LocOver.isTerm_move_of_unitary | exact GlobalTheory.LocOver.isTerm_move_of_unitary | (intros; apply GlobalTheory.LocOver.isTerm_move_of_unitary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalIndicesColumnRowLevelsExact
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalIndicesColumnRowLevelsExact
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory

theorem prod_pow_sub_pow_eq_mul_prod_Icc (g : ℝ) (k : ℕ) :
    ∏ j ∈ Finset.range k, (g ^ k - g ^ j) =
      g ^ (k * (k - 1) / 2) * ∏ j ∈ Finset.Icc 1 k, (g ^ j - 1) := by

  have hshift : ∀ n : ℕ, ∏ j ∈ Finset.range n, (g ^ (j + 1) - 1) = ∏ j ∈ Finset.Icc 1 n, (g ^ j - 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.prod_range_succ, ih, Finset.prod_Icc_succ_top (by omega)]
  have hterm : ∀ j ∈ Finset.range k, g ^ k - g ^ j = g ^ j * (g ^ (k - 1 - j + 1) - 1) := by
    intro j hj
    have hjk : j + (k - 1 - j + 1) = k := by
      have := Finset.mem_range.mp hj
      omega
    rw [mul_sub, mul_one, ← pow_add, hjk]
  have hrev := Finset.prod_range_reflect (fun j => g ^ (j + 1) - 1) k
  rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.sum_range_id, hrev, hshift]

theorem natCard_GL_zmod_real (g n : ℕ) (hg : g.Prime) :
    (Nat.card (GL (Fin n) (ZMod g)) : ℝ) = ∏ j ∈ Finset.range n, ((g : ℝ) ^ n - (g : ℝ) ^ j) := by
  haveI : Fact g.Prime := ⟨hg⟩
  rw [Matrix.card_GL_field, ZMod.card, Nat.cast_prod, Finset.prod_range]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Nat.cast_sub (Nat.pow_le_pow_right hg.pos j.isLt.le), Nat.cast_pow, Nat.cast_pow]

private theorem card_pattern_GL_eq_card_pow {F : Type} [Field F] [Fintype F] {n : ℕ}
    (fr : Fin n → Fin n → Prop) [DecidableRel fr] (hfr : ∀ i j, fr i j → i < j)
    (P : Matrix (Fin n) (Fin n) F → Prop)
    (hP : ∀ M, P M ↔ (∀ i, M i i = 1) ∧ ∀ i j, i ≠ j → ¬ fr i j → M i j = 0) :
    Nat.card {A : GL (Fin n) F // P (A : Matrix (Fin n) (Fin n) F)} =
      Nat.card F ^ Nat.card {p : Fin n × Fin n // fr p.1 p.2} := by
  classical

  have hunit : ∀ M : Matrix (Fin n) (Fin n) F, P M → IsUnit M := by
    intro M hM
    have hup : M.IsUpperTriangular := by
      intro i j hji
      exact ((hP M).1 hM).2 i j (ne_of_gt hji) (fun h => lt_asymm hji (hfr i j h))
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isUpperTriangular hup,
      Finset.prod_eq_one (fun i _ => ((hP M).1 hM).1 i)]
    exact isUnit_one

  have e1 : {A : GL (Fin n) F // P (A : Matrix (Fin n) (Fin n) F)} ≃
      {M : Matrix (Fin n) (Fin n) F // P M} :=
    { toFun := fun A => ⟨A.1, A.2⟩
      invFun := fun M => ⟨(hunit M.1 M.2).unit, by rw [IsUnit.unit_spec]; exact M.2⟩
      left_inv := fun A => Subtype.ext (Units.ext rfl)
      right_inv := fun M => Subtype.ext (IsUnit.unit_spec (hunit M.1 M.2)) }
  have e2 : {M : Matrix (Fin n) (Fin n) F // P M} ≃ ({p : Fin n × Fin n // fr p.1 p.2} → F) :=
    { toFun := fun M p => M.1 p.1.1 p.1.2
      invFun := fun f => ⟨Matrix.of fun i j => if i = j then 1 else if h : fr i j then f ⟨(i, j), h⟩ else 0, by
        rw [hP]
        refine ⟨fun i => by simp, fun i j hij hf => by simp [hij, hf]⟩⟩
      left_inv := fun M => by
        apply Subtype.ext
        funext i j
        by_cases hij : i = j
        · subst hij
          simp [((hP _).1 M.2).1 i]
        · by_cases hf : fr i j
          · simp [hij, hf]
          · simp [hij, hf, ((hP _).1 M.2).2 i j hij hf]
      right_inv := fun f => by
        funext p
        have hne : p.1.1 ≠ p.1.2 := ne_of_lt (hfr _ _ p.2)
        simp [hne, p.2] }
  rw [Nat.card_congr (e1.trans e2)]
  exact Nat.card_fun

private theorem card_lt_pairs_eq_choose_two (k : ℕ) :
    Nat.card {p : Fin k × Fin k // p.1 < p.2} = k * (k - 1) / 2 := by
  classical
  have h : ∀ j : Fin k, (∑ i : Fin k, if i < j then 1 else 0) = (j : ℕ) := by
    intro j
    rw [← Finset.card_filter, ← Fin.card_Iio j]
    congr 1
    ext i
    simp
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  simp only
  rw [Finset.sum_comm, Finset.sum_congr rfl (fun j _ => h j), Fin.sum_univ_eq_sum_range (fun i => i) k,
    Finset.sum_range_id]

private theorem blk_mono' (s k : ℕ) {a b : ℕ} (hab : a ≤ b) : StandardLattice.blk s k a ≤ StandardLattice.blk s k b := by
  unfold StandardLattice.blk
  split_ifs <;> omega

private theorem card_excluded_pairs_eq_k (s k : ℕ) :
    Nat.card {p : Fin (k + 2 * s + 1) × Fin (k + 2 * s + 1) //
      p.1 < p.2 ∧ (p.2.val = s + k ∧ StandardLattice.blk s k p.1.val = s)} = k := by
  have hb : ∀ a : ℕ, StandardLattice.blk s k a = s → s ≤ a ∧ a < s + k + 1 := by
    intro a ha
    unfold StandardLattice.blk at ha
    split_ifs at ha <;> omega
  have hb' : ∀ a : ℕ, s ≤ a → a < s + k + 1 → StandardLattice.blk s k a = s := by
    intro a h1 h2
    unfold StandardLattice.blk
    split_ifs <;> omega
  have e : {p : Fin (k + 2 * s + 1) × Fin (k + 2 * s + 1) //
      p.1 < p.2 ∧ (p.2.val = s + k ∧ StandardLattice.blk s k p.1.val = s)} ≃ Fin k :=
    { toFun := fun p => ⟨p.1.1.val - s, by
        have h1 := hb _ p.2.2.2
        have h2 : p.1.1.val < p.1.2.val := p.2.1
        have h3 := p.2.2.1
        omega⟩
      invFun := fun t => ⟨(⟨s + t.val, by omega⟩, ⟨s + k, by omega⟩), by
        refine ⟨?_, rfl, hb' (s + t.val) (Nat.le_add_right _ _) (by omega)⟩
        show s + t.val < s + k
        omega⟩
      left_inv := fun p => by
        have h1 := hb _ p.2.2.2
        have h3 := p.2.2.1
        apply Subtype.ext
        apply Prod.ext
        · apply Fin.ext
          simp only
          omega
        · apply Fin.ext
          simp only
          omega
      right_inv := fun t => by
        apply Fin.ext
        simp }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem card_not_excluded_pairs_eq (s k : ℕ) :
    Nat.card {p : Fin (k + 2 * s + 1) × Fin (k + 2 * s + 1) //
      p.1 < p.2 ∧ ¬ (p.2.val = s + k ∧ StandardLattice.blk s k p.1.val = s)} =
      s * (2 * k + 2 * s + 1) + k * (k - 1) / 2 := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun p : Fin (k + 2 * s + 1) × Fin (k + 2 * s + 1) => p.1 < p.2))
    (fun p => p.2.val = s + k ∧ StandardLattice.blk s k p.1.val = s)
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  have hall := card_lt_pairs_eq_choose_two (k + 2 * s + 1)
  have hex := card_excluded_pairs_eq_k s k
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hall hex ⊢
  rw [hex, hall] at hsplit
  have e : (k + 2 * s + 1) * (k + 2 * s + 1 - 1) = k * (k - 1) + (k + s * (2 * k + 2 * s + 1)) * 2 := by
    rw [Nat.add_sub_cancel]
    rcases k with _ | k
    · simp
      ring
    · rw [Nat.add_sub_cancel]
      ring
  rw [e, Nat.add_mul_div_right _ _ two_pos] at hsplit
  omega

theorem idxColLoc_idxRowLoc_exact : ∀ (D : D7) (i : Fin 2), StandardLattice.idxColLoc (D.host.g i) D.R.k = ∏ j ∈ Finset.Icc 1 D.R.k, ((D.host.g i : ℝ) ^ j - 1) ∧ StandardLattice.idxRowLoc (D.host.g i) D.R.k D.R.m = (∏ j ∈ Finset.range D.R.r, ((D.host.g i : ℝ) ^ D.R.r - (D.host.g i : ℝ) ^ j)) / ((D.host.g i : ℝ) ^ (D.R.rS * (2 * D.R.k + 2 * D.R.rS + 1)) * (D.host.g i : ℝ) ^ (D.R.k * (D.R.k - 1) / 2)) := by
  intro D i
  have hg : (D.host.g i).Prime := D.host.g_prime i
  haveI : Fact (D.host.g i).Prime := ⟨hg⟩
  have hpos : (0 : ℝ) < (D.host.g i : ℝ) := by exact_mod_cast hg.pos
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hs : D.R.rS = D.R.m / 2 - 1 := rfl
  have hm : D.R.k + D.R.m - 1 = D.R.k + 2 * D.R.rS + 1 := by
    have h1 := D.R.m_even
    have h2 := D.R.two_le_m
    obtain ⟨t, ht⟩ := h1
    rw [hs]
    omega
  constructor
  ·
    have hcard := card_pattern_GL_eq_card_pow (F := ZMod (D.host.g i)) (n := D.R.k) (fun a b => a < b)
      (fun _ _ h => h) StandardLattice.IsUnitri (by
        intro M
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h2, fun a b hab hlt => h1 a b (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hab))⟩
        · rintro ⟨h1, h2⟩
          exact ⟨fun a b hba => h2 a b (ne_of_gt hba) (not_lt.mpr hba.le), h1⟩)
    rw [card_lt_pairs_eq_choose_two, Nat.card_zmod] at hcard
    unfold StandardLattice.idxColLoc StandardLattice.idxLoc
    rw [hcard, natCard_GL_zmod_real _ _ hg, prod_pow_sub_pow_eq_mul_prod_Icc, Nat.cast_pow,
      mul_div_cancel_left₀ _ (pow_ne_zero _ hpos.ne')]
  ·

    unfold StandardLattice.idxRowLoc StandardLattice.idxLoc
    rw [hr, natCard_GL_zmod_real _ _ hg, ← pow_add]
    congr 2
    have hcard := card_pattern_GL_eq_card_pow (F := ZMod (D.host.g i)) (n := D.R.k + D.R.m - 1)
      (fun a b => a < b ∧ ¬ (b.val = (D.R.m / 2 - 1) + D.R.k ∧ StandardLattice.blk (D.R.m / 2 - 1) D.R.k a.val = D.R.m / 2 - 1))
      (fun _ _ h => h.1) (StandardLattice.IsRowLev D.R.k (D.R.m / 2 - 1)) (by
        intro M
        constructor
        · rintro ⟨h1, h2, h3, h4⟩
          refine ⟨h2, fun a b hab hf => ?_⟩
          by_cases hlt : a < b
          · have hE : b.val = (D.R.m / 2 - 1) + D.R.k ∧ StandardLattice.blk (D.R.m / 2 - 1) D.R.k a.val = D.R.m / 2 - 1 := by
              by_contra hc
              exact hf ⟨hlt, hc⟩
            exact h4 a b hE.1 hab hE.2
          · have hba : b < a := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hab)
            have hmono := blk_mono' (D.R.m / 2 - 1) D.R.k (Fin.lt_def.mp hba).le
            rcases lt_or_eq_of_le hmono with hl | he
            · exact h1 a b hl
            · exact h3 a b he.symm hba
        · rintro ⟨h1, h2⟩
          refine ⟨fun a b hb => ?_, h1, fun a b he hba => ?_, fun a b hj hab hblk => ?_⟩
          · have hba : b < a := by
              by_contra hc
              have := blk_mono' (D.R.m / 2 - 1) D.R.k (Fin.le_def.mp (not_lt.mp hc))
              omega
            exact h2 a b (ne_of_gt hba) (fun h => lt_asymm hba h.1)
          · exact h2 a b (ne_of_gt hba) (fun h => lt_asymm hba h.1)
          · exact h2 a b hab (fun h => h.2 ⟨hj, hblk⟩))
    rw [hcard, Nat.card_zmod, Nat.cast_pow]
    congr 1
    rw [← hs]
    have hc := card_not_excluded_pairs_eq D.R.rS D.R.k
    rw [← hm] at hc
    rw [hs] at hc ⊢
    rw [hc]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalIndicesColumnRowLevelsExactStatement
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localIndices_column_row_levels_exact : ∀ (D : D7) (i : Fin 2), StandardLattice.idxColLoc (D.host.g i) D.R.k = ∏ j ∈ Finset.Icc 1 D.R.k, ((D.host.g i : ℝ) ^ j - 1) ∧ StandardLattice.idxRowLoc (D.host.g i) D.R.k D.R.m = (∏ j ∈ Finset.range D.R.r, ((D.host.g i : ℝ) ^ D.R.r - (D.host.g i : ℝ) ^ j)) / ((D.host.g i : ℝ) ^ (D.R.rS * (2 * D.R.k + 2 * D.R.rS + 1)) * (D.host.g i : ℝ) ^ (D.R.k * (D.R.k - 1) / 2)) := by
  first | exact @GlobalTheory.idxColLoc_idxRowLoc_exact | exact GlobalTheory.idxColLoc_idxRowLoc_exact | (intros; apply GlobalTheory.idxColLoc_idxRowLoc_exact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormRootMeasureHaarUnimodular
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormRootMeasureHaarUnimodular
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Amp.StabMeas
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.RootMeas

theorem normR_facts : ∀ (k r : ℕ) (γ : Mat k r) (s : ℝ) (μR : Measure (Mt k r)), 0 < s → NormR k r γ s μR → IsClosedSub k r (Rset k r γ) ∧ IsHaarOn (Rset k r γ) μR ∧ IsUnimod (Rset k r γ) μR ∧ NormR k r γ⁻¹ s (μR.map (conjM γ)) := by
  rintro k r γ s μR hs ⟨n₁, h₁, n₂, h₂, g₀, β, hg, rfl, rfl⟩
  obtain ⟨n1, -, -, n4, n5⟩ := isClosedSub_Nset (k := k) (r := r)
  obtain ⟨-, -, b1, b2, a3, c1⟩ := GlobalTheory.T.commonStabilizer_normalForm_blockUnitriangular k r g₀ β hg
  have hγ : n₁ * g₀ * n₂ ∈ GG k r :=
    isClosedSub_GG.2.2.2.1 _ (isClosedSub_GG.2.2.2.1 _ (n1 h₁) _ hg.1) _ (n1 h₂)
  have hinv : (n₁ * g₀ * n₂)⁻¹ = n₂⁻¹ * g₀⁻¹ * n₁⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]
  obtain ⟨d1, d2⟩ := haar_smul b1 b2 hs
  obtain ⟨e1, e2⟩ := haar_conj (isUnit_det_of_mem_GG (n1 (n5 _ h₂))) (conj_mem_Rset h₁ h₂ g₀) d1 d2
  refine ⟨isClosedSub_Rset hγ, e1, e2, n₂⁻¹, n5 _ h₂, n₁⁻¹, n5 _ h₁, g₀⁻¹, β, a3, hinv, ?_⟩
  rw [map_conj_conj, Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_det_of_mem_GG (n1 h₂)), ← map_conj_conj,
    Measure.map_smul, c1, Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem_GG (n1 h₁))]
  exact (meas_conj g₀).aemeasurable

end GlobalTheory.Amp.RootMeas
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormRootMeasureHaarUnimodularStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalFormRootMeasure_haar_unimodular : ∀ (k r : ℕ) (γ : Mat k r) (s : ℝ) (μR : Measure (Mt k r)), 0 < s → NormR k r γ s μR → IsClosedSub k r (Rset k r γ) ∧ IsHaarOn (Rset k r γ) μR ∧ IsUnimod (Rset k r γ) μR ∧ NormR k r γ⁻¹ s (μR.map (conjM γ)) := by
  first | exact @GlobalTheory.Amp.RootMeas.normR_facts | exact GlobalTheory.Amp.RootMeas.normR_facts | (intros; apply GlobalTheory.Amp.RootMeas.normR_facts <;> assumption)
end
end
