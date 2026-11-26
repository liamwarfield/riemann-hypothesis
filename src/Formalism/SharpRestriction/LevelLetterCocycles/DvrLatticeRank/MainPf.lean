module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UnivLinkPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.RankBounds
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U3mixlinkPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelQPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U2ringPfZetaO

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ExponentRecursionHolds
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ExponentRecursionOfDimension
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ExistsAutPrim
noncomputable section

namespace Formalism.MainNotions.N.Ln34.CrystallineExponents

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

variable {l : ℕ} [Fact l.Prime]

theorem exists_aut_prim (K : FinExt l) {z z' : Om l} (hz : IsPrimitiveRoot z l)
    (hz' : IsPrimitiveRoot z' l) : ∃ g : Om l ≃ₐ[↥(K0 K)] Om l, g z = z' := by
  have hl : l.Prime := Fact.out
  haveI : NeZero l := ⟨hl.ne_zero⟩
  haveI : Algebra.IsAlgebraic ↥(K0 K) (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) _
  haveI : IsAlgClosure ↥(K0 K) (Om l) := ⟨inferInstance, inferInstance⟩
  have hint : IsIntegral ↥(K0 K) z := Algebra.IsIntegral.isIntegral z
  have hle : K0 K ≤ Ks K 1 := le_sup_left
  have hdeg := CyclotomicLifting.cyclotomic_degree_max_unramified K
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle] at hdeg
  have hsub : IntermediateField.extendScalars hle ≤ IntermediateField.adjoin ↥(K0 K) {z} := by
    have h : Ks K 1 ≤ (IntermediateField.adjoin ↥(K0 K) {z}).restrictScalars ℚ_[l] := by
      refine sup_le (fun x hx => ?_) (IntermediateField.adjoin_le_iff.2 fun x hx => ?_)
      · exact (IntermediateField.adjoin ↥(K0 K) {z}).algebraMap_mem ⟨x, hx⟩
      · have hx1 : x ^ l = 1 := by simpa using hx
        obtain ⟨b, -, rfl⟩ := hz.eq_pow_of_pow_eq_one hx1
        exact pow_mem (IntermediateField.mem_adjoin_simple_self ↥(K0 K) z) b
    intro x hx
    exact h hx
  haveI := IntermediateField.adjoin.finiteDimensional hint
  have hd : l - 1 ≤ (minpoly ↥(K0 K) z).natDegree := by
    rw [← IntermediateField.adjoin.finrank hint, ← hdeg]
    exact IntermediateField.finrank_le_of_le_right hsub
  have hroot : ∀ {w : Om l}, IsPrimitiveRoot w l →
      Polynomial.aeval w (Polynomial.cyclotomic l ↥(K0 K)) = 0 := fun {w} hw => by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
    exact hw.isRoot_cyclotomic hl.pos
  have hdvd : minpoly ↥(K0 K) z ∣ Polynomial.cyclotomic l ↥(K0 K) := minpoly.dvd _ _ (hroot hz)
  have heq : Polynomial.cyclotomic l ↥(K0 K) = minpoly ↥(K0 K) z :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
      (Polynomial.cyclotomic.monic _ _) hdvd
      (by rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hl]; exact hd)
  have h0 : Polynomial.aeval z' (minpoly ↥(K0 K) z) = 0 := heq ▸ hroot hz'
  exact minpoly.exists_algEquiv_of_root' hint.isAlgebraic h0

theorem exists_pt (D : D7) (HW : HWOf D.loc) {K LL : FinExt l} (hG : Good K 1 LL)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (hζ : IsPrimitiveRoot ζ l) :
    ∃ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ := by
  have : Algebra.IsAlgebraic ↥(K0 K) (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) _
  obtain ⟨σ, hσ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ_[l]) (L := ↥(K0 K))
    (M := Om l) (E := Om l) ((LL.1.val).comp (((HW l).W K 1 LL hG).emb c))
  have hσx : ∀ x : ↥(K0 K),
      σ (x : Om l) = ((((HW l).W K 1 LL hG).emb c x : ↥LL.1) : Om l) := fun x => by
    have := congrArg (fun f => f x) hσ
    simpa [AlgHom.domRestrict] using this
  have hζ₁ := Formalism.MainNotions.UnusedSlot80.LevR.root_of_unity_primitive D l
  have hσinj : Function.Injective σ := σ.toRingHom.injective
  have hζO : IsPrimitiveRoot ((ζ : ↥LL.1) : Om l) l :=
    hζ.map_of_injective (f := LL.1.val) Subtype.val_injective
  have hσζ₁ : IsPrimitiveRoot (σ ((D.loc l).ζQ 1)) l := hζ₁.map_of_injective hσinj
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨b, -, hb⟩ := hσζ₁.eq_pow_of_pow_eq_one hζO.pow_eq_one
  have hβ : IsPrimitiveRoot ((D.loc l).ζQ 1 ^ b) l := by
    apply IsPrimitiveRoot.of_map_of_injective (f := σ) _ hσinj
    rw [map_pow, hb]
    exact hζO
  obtain ⟨g, hg⟩ := exists_aut_prim K hζ₁ hβ
  let g' : Om l →ₐ[ℚ_[l]] Om l := (g.toAlgHom).restrictScalars ℚ_[l]
  have hmem : ∀ y, ((σ.comp g').comp (Ks K 1).val) y ∈ LL.1 := hG.2.2.2 _
  let τs : ↥(Ks K 1) →ₐ[ℚ_[l]] ↥LL.1 :=
    ((σ.comp g').comp (Ks K 1).val).codRestrict LL.1.toSubalgebra hmem
  refine ⟨τs.comp (IntermediateField.inclusion hG.2.2.1), τs,
    ⟨fun x y hxy => ?_, fun y hy => ?_⟩, fun x y hxy => ?_⟩
  · apply Subtype.ext
    show σ (g (y : Om l)) = _
    have hgx : g (x : Om l) = x := g.commutes x
    rw [hxy, hgx, hσx]
  · apply Subtype.ext
    show σ (g (y : Om l)) = _
    rw [hy, hg, map_pow, hb]
  · show τs _ = τs y
    congr 1
    exact Subtype.ext hxy.symm

end Formalism.MainNotions.N.Ln34.CrystallineExponents

end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln34.CrystallineExponents

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem exponent_recursion_of_dimension (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : Formalism.MainNotions.ElementDenominator.adm1 D HW F Cm) (h8 : Formalism.MainNotions.ElementDenominator.adm8 D)
    (hdim : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL)
      (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ →
      ∀ (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1),
        finrank ↥LL.1 ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi ((HW l).W K 1 LL hG) T c) ≤
          finrank ↥LL.1 ↥(DdRE ((D.loc l).PD K) T.ρ τ)) :
    ExpansionFormAll D HW := by
  intro l _ hl K LL hG T h' hh' hT hJ c y _ hyc hk hexp
  obtain ⟨p1, -, p3, p4, p5, -⟩ := h1 l K 1 LL hG
  obtain ⟨⟨hfc, -⟩, hfd⟩ := h8 l K LL T
  have hFr : IsFractionRing ↥(OL LL) ↥LL.1 := by
    haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
    exact integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
  haveI : FiniteDimensional ↥LL.1
      ↥(DcrisL ((D.loc l).PD K) T.ρ (((HW l).W K 1 LL hG).emb c)) :=
    Submodule.finiteDimensional_of_le (inf_le_left : _ ≤ Dcris ((D.loc l).PD K) T.ρ)
  haveI : FiniteDimensional ↥LL.1 ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi ((HW l).W K 1 LL hG) T c) := by
    unfold Formalism.MainNotions.DeltaInvariantLattices.ιDi
    infer_instance
  have hyc' : (letE c : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) • y = y := by
    have h := LinearMap.mem_ker.1 hyc
    simpa only [LinearMap.restrictScalars_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero] using h
  refine mem_N_of_exp ((HW l).W K 1 LL hG) hFr ((HW l).W_s K 1 LL hG) T
    (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) (M := fun _ => h') (h := fun _ => h') (p1 T hT) (p3 T hT)
    (p4 T hT) (p5 T _ _ hT fun τ _ _ => hJ τ) c (fun ζ hζ => ?_) (fun τ => (hfd τ).1)
    (hdim l K LL hG T hT c) y hyc' hk hexp
  rw [(D.loc l).PD_p] at hζ
  exact exists_pt D HW hG c ζ hζ

end Formalism.MainNotions.N.Ln34.CrystallineExponents

end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln34

theorem exponent_recursion_holds : ExpansionFormHypothesis := fun D HW F Cm _ _ _ hA hd hr =>
  CrystallineExponents.exponent_recursion_of_dimension D HW F Cm hA.1 hA.2.2.2.2.2.2.2.2.2.2.1 fun l _ K LL hG T hT c τ =>
    ((hr l K LL hG T hT c).trans (hd l K LL ⟨1, hG⟩ T hT τ).symm).le

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.InvLiftPf
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules


set_option maxHeartbeats 1000000 in
theorem invLiftCondition : InvLiftStep := by
  set_option synthInstance.maxHeartbeats 400000 in
  intro D HW F Cm CA CB CK hA l _ hl K LL hG π' E hπ T h' hh' hT hJ c
  haveI := ((HW l).W K 1 LL hG).ddTowO T
  have hNL : NinLam ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' :=
    ninlam_pf D HW F Cm CA CB CK hA l hl K LL hG π' E hπ T h' hT hJ
  rcases le_or_gt (MK l K h') 1 with hM | hM
  · refine ⟨fun w hw => ⟨((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ^ sigA l (sK l K) h' • w, ?_, ?_⟩,
      fun wb _ hwb => gradNPf_PiNS_anti _ T π' hM hwb⟩
    · obtain ⟨hwL, hwγ⟩ := (mem_InvS _ T π' _ h' 1 c w).1 hw
      refine (mem_InvS _ T π' _ h' _ c _).2 ⟨Submodule.smul_mem _ _ hwL, ?_⟩
      rw [map_smul, ← smul_sub]
      exact Submodule.smul_mem _ _ (gradNPf_PiNS_anti _ T π' hM hwγ)
    · rw [sub_self]
      exact Submodule.zero_mem _
  have hs : 1 ≤ sK l K := by
    by_contra h0
    have h0' : sK l K = 0 := by omega
    have : MK l K h' = 0 := by simp [MK, h0']
    omega
  obtain ⟨f, t, x, u, hu, hxu, hf, ht, hEE, hπΔ, hγN, hK, hprod⟩ :=
    gradNPf_hyps D HW F Cm hA.1 l hl K LL hG π' E hπ T hT hs
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  obtain ⟨a, ha⟩ := hprod (MK l K h' - 1)
  have hM1 : MK l K h' - 1 + 1 = MK l K h' := by omega
  rw [hM1] at ha
  have hσ : sigA l (sK l K) h' = MK l K h' - 1 + padicValNat l (MK l K h' - 1).factorial := rfl

  have hl0 : ((l : ℕ) : ↥LL.1) ≠ 0 := by
    intro h0
    have hv := (D.loc l).v_l LL
    rw [h0, AddValuation.map_zero] at hv
    exact absurd hv (by simp)
  have hℓ : ∀ c : ↥(OL LL), (l : ↥(OL LL)) * c = 0 → c = 0 := by
    intro c hc
    have h1 := congrArg (algebraMap ↥(OL LL) ↥LL.1) hc
    rw [map_mul, map_natCast, map_zero] at h1
    have h2 := (mul_eq_zero.1 h1).resolve_left hl0
    exact (injective_iff_map_eq_zero (algebraMap ↥(OL LL) ↥LL.1)).1 Subtype.val_injective c h2

  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  obtain ⟨-, -, -, -, -, -, -, -, h9W, -⟩ := hA.1 l K 1 LL hG
  obtain ⟨-, ⟨π'₀, E₀, -, hm₀⟩, -⟩ := h9W T hT hs1 hp
  obtain ⟨⟨r, b, hbΔ, huniq, -⟩, -⟩ := hm₀
  obtain ⟨w, hw⟩ := hπ.2.2.1
  have hnz : ∀ y : ℕ, 1 ≤ y → y < MK l K h' → ∀ r₀ ∈ ((HW l).W K 1 LL hG).N T,
      ∀ d ∈ ((HW l).W K 1 LL hG).N T, ((x ^ sK l K) ^ y - 1) • r₀ = π' • d →
      ∃ e ∈ ((HW l).W K 1 LL hG).N T, r₀ = π' • e := by
    intro y hy1 hyM r₀ hr₀ d hd hrd
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun y => (x ^ sK l K) ^ y - 1)
      (Finset.mem_Ico.2 ⟨hy1, hyM⟩)
    rw [hq] at ha
    refine invLiftPf_nzd _ T π' w (sK l K) w.isUnit hw (l : ↥(OL LL)) hℓ r b
      (fun j => (hbΔ j).1) huniq (MK l K h' - 1 + padicValNat l (MK l K h' - 1).factorial) r₀
      ((a * q) • d) hr₀ ?_ ?_
    · rw [← algebraMap_smul (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))]
      exact Submodule.smul_mem _ _ hd
    · rw [ha, mul_comm ((x ^ sK l K) ^ y - 1) q, ← mul_assoc, mul_smul, hrd,
        ← algebraMap_smul (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (a * q) (π' • d),
        ← algebraMap_smul (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (a * q) d, smul_smul, smul_smul,
        mul_comm]
  have hpσ : (((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ^ sigA l (sK l K) h') =
      a * ∏ y ∈ Finset.Ico 1 (MK l K h'), ((x ^ sK l K) ^ y - 1) := by
    rw [hpl, hσ]
    exact ha
  have hGr : GradN ((HW l).W K 1 LL hG) T π' (sigA l (sK l K) h') (MK l K h') :=
    gradNPf_local _ T π' f t (x ^ sK l K) hf ht hEE hπΔ hγN hK _ _ (by omega) a hpσ
  refine ⟨invLiftPf_lift _ T π' _ h' _ _ c hGr hNL, fun wb hwb hwb1 => ?_⟩
  exact invLiftPf_inj _ T π' f t (x ^ sK l K) hf ht hEE hπΔ hγN hK _ hnz wb hwb1
    ((mem_InvS _ T π' _ h' _ c wb).1 hwb).2

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPf
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem gradNCondition : Formalism.MainNotions.N.Ln34.GradNStep := by
  intro D HW F Cm CA CB CK hA l hlp hl K LL hG π' E hR T h' hh' hT
  have h1 : adm1 D HW F Cm := hA.1
  rcases Nat.eq_zero_or_pos (sK l K) with hs0 | hs
  ·
    apply gradNPf_small
    simp [MK, hs0]
  · obtain ⟨f, t, x, u, -, -, hf, ht, hE, hΔ, hγ, hK, hN⟩ :=
      gradNPf_hyps D HW F Cm h1 l hl K LL hG π' E hR T hT hs
    rcases le_or_gt (MK l K h') 1 with hM | hM
    · apply gradNPf_small
      exact hM
    · obtain ⟨a, ha⟩ := hN (MK l K h' - 1)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ MK l K h')] at ha
      refine gradNPf_local (hf := hf) (ht := ht) (hu := hE) (hπΔ := hΔ) (hγN := hγ) (hK := hK)
        (hM := by omega) (a := a) (ha := ?_)
      convert ha using 2
      · rw [(D.loc l).PD_p K]
      · rfl

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U3uplinkPfOf
noncomputable section

namespace Formalism.MainNotions.N.Ln34

theorem u3uplink_pf_of (hW : WStep) : UpSlotOfModels := by
  intro D HW F Cm CA CB CK hA hMF
  exact u3upPf_ofR D HW hMF (hW D HW F Cm CA CB CK hA) (ninlam_pf D HW F Cm CA CB CK hA)
    (gamPiCondition D HW F Cm CA CB CK hA)

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FrobeniusSpanDecomposition
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section KerLam2Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

private theorem kl2_dec_lemma (W : LocWach PD LL O v n) [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    (T : LocLat G Qp LL O) (S : Submodule (LetA O n) (W.DD T)) (a : LetA O n) (s : W.DD T) (hs : s ∈ S) :
    ∃ t : Fin PD.p → W.DD T, (∀ k, t k ∈ S) ∧
      a • W.φD T s = ∑ k : Fin PD.p, (letπ : LetA O n) ^ (k : ℕ) • W.φD T (t k) := by
  obtain ⟨e, he⟩ := Formalism.MainNotions.LiftingTheory.PhiBasis_of W a
  refine ⟨fun k => e k • s, fun k => S.smul_mem _ hs, ?_⟩
  rw [he, Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Formalism.MainNotions.LiftingTheory.wmap_φD_smul, mul_smul]

theorem frobenius_span_decomposition (W : LocWach PD LL O v n) [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    (T : LocLat G Qp LL O) (S : Submodule (LetA O n) (W.DD T)) (z : W.DD T)
    (hz : z ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T S) :
    ∃ s : Fin PD.p → W.DD T, (∀ k, s k ∈ S) ∧
      z = ∑ k : Fin PD.p, (letπ : LetA O n) ^ (k : ℕ) • W.φD T (s k) := by
  unfold Formalism.MainNotions.DeltaInvariantLattices.φspan at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, he⟩ := kl2_dec_lemma W T S 1 s hs
    exact ⟨t, ht, by rw [← he, one_smul]⟩
  | zero => exact ⟨fun _ => 0, fun _ => S.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨s', hs', rfl⟩ := hy
    exact ⟨fun k => s k + s' k, fun k => S.add_mem (hs k) (hs' k),
      by simp only [map_add (f := _), smul_add, Finset.sum_add_distrib]⟩
  | smul a x _ hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    choose t ht he using fun k : Fin PD.p =>
      kl2_dec_lemma W T S (a * (letπ : LetA O n) ^ (k : ℕ)) (s k) (hs k)
    refine ⟨fun j => ∑ k, t k j, fun j => S.sum_mem fun k _ => ht k j, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.smul_sum, ← mul_smul, he, map_sum]
    rw [Finset.sum_comm]

theorem frobenius_span_exact_lift (W : LocWach PD LL O v n) [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    {T Tp T'' : LocLat G Qp LL O} (ι : LatHom T.L Tp.L) (π : LatHom Tp.L T''.L)
    (c'' : IsCrys PD T''.ρ) (hinj : Function.Injective (W.map ι))
    (hex : ∀ x, W.map π x = 0 → ∃ y, W.map ι y = x)
    (h4 : ∀ x : W.DD T, W.map ι x ∈ W.N Tp → x ∈ W.N T) (i : ZMod n)
    (z : W.DD Tp) (hz : z ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W Tp (W.Nl Tp i)) (h0 : W.map π z = 0) :
    ∃ z' ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T i), W.map ι z' = z := by
  obtain ⟨s, hs, rfl⟩ := frobenius_span_decomposition W Tp (W.Nl Tp i) z hz
  have hπs : ∀ k, W.map π (s k) = 0 := by
    refine Formalism.MainNotions.LiftingTheory.phii_DD W T'' c'' (fun k => W.map π (s k)) ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h0, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul, W.map_φ]
  choose y hy using fun k => hex (s k) (hπs k)
  have hyNl : ∀ k, y k ∈ W.Nl T i := by
    intro k
    obtain ⟨w, hw, hwe⟩ := (Formalism.MainNotions.LiftingTheory.wmap_mem_Nl W Tp i (s k)).1 (hs k)
    have hyN : y k ∈ W.N T := by
      apply h4
      rw [hy k, ← hwe]
      exact (W.N Tp).smul_mem _ hw
    rw [Formalism.MainNotions.LiftingTheory.wmap_mem_Nl]
    refine ⟨y k, hyN, ?_⟩
    apply hinj
    rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul, hy k, Formalism.MainNotions.LiftingTheory.wmap_Nl_fix W Tp i (s k) (hs k)]
  refine ⟨∑ k : Fin PD.p, (letπ : LetA O n) ^ (k : ℕ) • W.φD T (y k), ?_, ?_⟩
  · refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    unfold Formalism.MainNotions.DeltaInvariantLattices.φspan
    exact Submodule.subset_span ⟨y k, hyNl k, rfl⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul, W.map_φ, hy k]

theorem frobenius_span_exact_local (W : LocWach PD LL O v n) [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    {T Tp T'' : LocLat G Qp LL O} (ι : LatHom T.L Tp.L) (π : LatHom Tp.L T''.L)
    (π' Eπ : LetA O n) (h' : ℕ) (c'' : IsCrys PD T''.ρ)
    (hinj : Function.Injective (W.map ι))
    (hex : ∀ x, W.map π x = 0 ↔ ∃ y, W.map ι y = x)
    (h4 : ∀ x : W.DD T, W.map ι x ∈ W.N Tp → x ∈ W.N T)
    (hπ' : IsUnit (algebraMap (LetA O n) W.EE π')) :
    KerLam W ι π π' Eπ h' := by
  have hex' : ∀ x, W.map π x = 0 → ∃ y, W.map ι y = x := fun x hx => (hex x).1 hx
  have hΔ : ∀ x : W.DD T, (∀ δ ∈ W.DelF, W.γD Tp δ (W.map ι x) = W.map ι x) →
      ∀ δ ∈ W.DelF, W.γD T δ x = x := by
    intro x hx δ hδ
    apply hinj
    rw [W.map_γ, hx δ hδ]
  have hL : ∀ (x : W.DD T) (a : LetA O n), a • W.map ι x = W.map ι x → a • x = x := by
    intro x a hx
    apply hinj
    rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul, hx]
  refine ⟨hinj, ?_, fun c => ⟨?_, ?_⟩⟩
  · intro k y hy hyπ
    rw [mem_PiNS] at hy
    obtain ⟨⟨y0, hy0N, rfl⟩, hyΔ⟩ := hy
    have hz : W.map π y0 = 0 := by
      have hu : IsUnit (algebraMap (LetA O n) W.EE (π' ^ k)) := by
        rw [map_pow]
        exact hπ'.pow k
      rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul, ← algebraMap_smul W.EE] at hyπ
      exact (hu.smul_eq_zero).1 hyπ
    obtain ⟨x0, rfl⟩ := hex' y0 hz
    refine ⟨π' ^ k • x0, ?_, Formalism.MainNotions.LiftingTheory.wmap_map_smul W ι _ _⟩
    rw [mem_PiNS]
    refine ⟨⟨x0, h4 x0 hy0N, rfl⟩, hΔ _ ?_⟩
    rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul]
    exact hyΔ
  · intro y hy hyπ
    rw [mem_LamPS] at hy
    obtain ⟨hyE, hyΔ, hyL⟩ := hy
    obtain ⟨x, rfl⟩ := hex' y hyπ
    obtain ⟨z', hz', hz'e⟩ := frobenius_span_exact_lift W ι π c'' hinj hex' h4 (c - 1) (Eπ ^ h' • W.map ι x) hyE
      (by rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul, hyπ, smul_zero])
    refine ⟨x, ?_, rfl⟩
    rw [mem_LamPS]
    refine ⟨?_, hΔ x hyΔ, hL x _ hyL⟩
    have e : z' = Eπ ^ h' • x := hinj (by rw [hz'e, Formalism.MainNotions.LiftingTheory.wmap_map_smul])
    rw [← e]
    exact hz'
  · intro y hy hyπ
    rw [mem_NcS] at hy
    obtain ⟨hyN, hyΔ, hyL⟩ := hy
    obtain ⟨x, rfl⟩ := hex' y hyπ
    refine ⟨x, ?_, rfl⟩
    rw [mem_NcS]
    exact ⟨h4 x hyN, hΔ x hyΔ, hL x _ hyL⟩

end KerLam2Local

theorem kerlam2_pf : KerLamStep := by
  unfold KerLamStep kerLamR
  intro D HW F Cm CA CB CK hA hF l _ hl K LL hG π' E hp9 T Tp T'' ι π h' hses hT hTp hT'' hJ
  obtain ⟨hW, -⟩ := hA
  obtain ⟨-, -, -, -, -, h6W, -⟩ := hW l K 1 LL hG
  obtain ⟨-, -, h6ses⟩ := h6W
  obtain ⟨-, -, -, hsat, -⟩ := h6ses T Tp T'' ι π hT hTp hT'' hses
  have hEx := hF l K 1 LL hG T Tp T'' ι π hses
  obtain ⟨-, -, ⟨w, hw⟩, -⟩ := hp9
  have e : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  letI : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
    rw [e]
    exact Formalism.MainNotions.LiftingTheory.phib_OL_complete LL
  refine frobenius_span_exact_local _ ι π π' _ h' hT'' hEx.1 hEx.2.2 hsat ?_
  rw [hw, map_mul, map_pow]
  exact (w.isUnit.map _).mul (by simpa using (Formalism.MainNotions.LiftingTheory.wmap_unit _ 0).pow _)

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.OneGenPf
noncomputable section

namespace Formalism.MainNotions.N.Ln34.OneGenPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem onegen_pf : Formalism.MainNotions.N.Ln34.OneGenStep := by
  intro D HW F Cm CA CB CK _ l _ _ K LL hG
  obtain ⟨-, -, e, -, hspan, hφ, hγ⟩ := Formalism.MainNotions.LiftingTheory.liftb_HOne_holds D HW F l K 1 LL hG
  exact ⟨e, hspan, hφ, hγ⟩

end Formalism.MainNotions.N.Ln34.OneGenPf
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LiftPf
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LiftPfB
noncomputable section

namespace Formalism.MainNotions.N.Ln34.CyclotomicLifting

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

variable {l : ℕ} [Fact l.Prime]

theorem fix_of_mem_GK {K : FinExt l} {σ : GQ l} (hσ : σ ∈ GK K) {x : Om l} (hx : x ∈ K.1) :
    σ x = x :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x hx

theorem Ks_stable (K : FinExt l) {σ : GQ l} (hσ : σ ∈ GK K) {x : Om l} (hx : x ∈ Ks K 1) :
    σ x ∈ Ks K 1 := by
  have hle : Ks K 1 ≤ (Ks K 1).map (σ.symm : Om l ≃ₐ[ℚ_[l]] Om l).toAlgHom := by
    unfold Ks
    refine sup_le ?_ ?_
    · intro y hy
      refine (IntermediateField.mem_map _).2 ⟨y, (le_sup_left : K0 K ≤ _) hy, ?_⟩
      have h1 : σ y = y := fix_of_mem_GK hσ (inf_le_left (a := K.1) (b := MaximalUnramifiedExtension l) hy)
      show σ.symm y = y
      rw [AlgEquiv.symm_apply_eq]
      exact h1.symm
    · rw [IntermediateField.adjoin_le_iff]
      intro y hy
      refine (IntermediateField.mem_map _).2 ⟨σ y, ?_, by simp⟩
      apply (le_sup_right : _ ≤ K0 K ⊔ _)
      apply IntermediateField.subset_adjoin
      show (σ y) ^ (l ^ 1) = 1
      rw [← map_pow, show y ^ (l ^ 1) = 1 from hy, map_one]
  obtain ⟨y, hy, hyx⟩ := (IntermediateField.mem_map _).1 (hle hx)
  have hyx' : σ.symm y = x := hyx
  rw [← hyx', AlgEquiv.apply_symm_apply]
  exact hy

theorem GKin_normal (K : FinExt l) (hKK : K.1 ≤ (cycL K).1) : (GKin hKK).Normal := by
  constructor
  intro n hn g
  rw [GKin, Subgroup.mem_subgroupOf] at hn ⊢
  rw [GK, IntermediateField.mem_fixingSubgroup_iff] at hn ⊢
  intro x hx
  have h1 : ((g : GQ l)⁻¹) x ∈ Ks K 1 := Ks_stable K (inv_mem g.2) hx
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply]
  rw [hn _ h1, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

theorem range_inclusion_eq (K : FinExt l) (hKK : K.1 ≤ (cycL K).1) (hle : GK (cycL K) ≤ GK K) :
    (Subgroup.inclusion hle).range = GKin hKK := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact Subgroup.mem_subgroupOf.2 y.2
  · intro hx
    exact ⟨⟨x.1, Subgroup.mem_subgroupOf.1 hx⟩, rfl⟩

theorem chi_cong (P : LocPrime l) (K : FinExt l) (g : GQ l) (hg : g ∈ GK (cycL K)) :
    ‖(P.χQ g : ℚ_[l]) - 1‖ ≤ (l : ℝ)⁻¹ := by
  have hp : l.Prime := Fact.out
  have hζl : P.ζQ 1 ^ (l ^ 1) = 1 := by
    have := P.ζQ_succ 0
    rw [P.ζQ_zero] at this
    simpa using this
  obtain ⟨a, ha, hga⟩ := P.χQ_cyc g 1 (P.ζQ 1) hζl
  have hζK : P.ζQ 1 ∈ (cycL K).1 :=
    (le_sup_right : _ ≤ K0 K ⊔ _) (IntermediateField.subset_adjoin _ _ hζl)
  have hfix : g (P.ζQ 1) = P.ζQ 1 := fix_of_mem_GK hg hζK
  have hord : orderOf (P.ζQ 1) = l := orderOf_eq_prime (by simpa using hζl) P.ζQ_one
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · exfalso
      apply P.ζQ_one
      have h2 : P.ζQ 1 ^ 0 = P.ζQ 1 ^ 1 := by rw [pow_one, ← hga, hfix]
      rw [pow_zero, pow_one] at h2
      exact h2.symm
    · exact h
  have hζ0 : P.ζQ 1 ≠ 0 := by
    intro h0
    rw [h0, zero_pow (pow_pos hp.pos 1).ne'] at hζl
    exact zero_ne_one hζl
  have h3 : P.ζQ 1 ^ (a - 1) = 1 := by
    have h4 : P.ζQ 1 ^ (a - 1) * P.ζQ 1 = 1 * P.ζQ 1 := by
      rw [← pow_succ, Nat.sub_add_cancel ha1, one_mul, ← hga, hfix]
    exact mul_right_cancel₀ hζ0 h4
  have hdvdN : l ∣ a - 1 := hord ▸ orderOf_dvd_of_pow_eq_one h3
  have hdvdN1 : l ^ 1 ∣ a - 1 := by rw [pow_one]; exact hdvdN
  have hcast : (a : ℤ) - 1 = ((a - 1 : ℕ) : ℤ) := by omega
  have h1 := (Padic.norm_int_le_pow_iff_dvd (p := l) ((a : ℤ) - 1) 1).2
    (by rw [hcast]; exact_mod_cast hdvdN1)
  have e : (P.χQ g : ℚ_[l]) - 1 = ((P.χQ g : ℚ_[l]) - (a : ℚ_[l])) + (((a : ℤ) - 1 : ℤ) : ℚ_[l]) := by
    push_cast; ring
  rw [e]
  refine ((Padic.nonarchimedean _ _).trans (max_le ha h1)).trans (le_of_eq ?_)
  simp

theorem v_ge_one (P : LocPrime l) (LL : FinExt l) (x : ℚ_[l]) (hx : ‖x‖ ≤ (l : ℝ)⁻¹) :
    (1 : WithTop ℚ) ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 x) := by
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hy : ‖x / l‖ ≤ 1 := by
    rw [norm_div, Padic.norm_p, div_le_one (inv_pos.2 (by exact_mod_cast (Fact.out : l.Prime).pos))]
    exact hx
  have hxy : x = (l : ℚ_[l]) * (x / l) := by field_simp
  have hyO : algebraMap ℚ_[l] ↥LL.1 (x / l) ∈ OL LL := by
    obtain ⟨y, hy'⟩ : ∃ y : ℤ_[l], (y : ℚ_[l]) = x / l := ⟨⟨x / l, hy⟩, rfl⟩
    rw [← hy', show (y : ℚ_[l]) = algebraMap ℤ_[l] ℚ_[l] y from rfl,
      ← IsScalarTower.algebraMap_apply]
    exact isIntegral_algebraMap
  rw [hxy, map_mul, map_natCast, AddValuation.map_mul, P.v_l LL]
  exact le_add_of_nonneg_right ((P.v_O LL _).2 hyO)

theorem FildR_succ_le (P : LocPrime l) (K LL : FinExt l)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ) :
    FildR (P.PD K) T.ρ τ (a + 1) ≤ FildR (P.PD K) T.ρ τ a := by
  unfold FildR FilV
  refine inf_le_inf_left _ ?_
  have hle : ((P.PD K).Fil (a + 1)).restrictScalars ℚ_[l] ≤ ((P.PD K).Fil a).restrictScalars ℚ_[l] :=
    fun x hx => (P.PD K).Fil_anti a hx
  rintro x ⟨y, rfl⟩
  exact ⟨TensorProduct.AlgebraTensorModule.map LinearMap.id (Submodule.inclusion hle) y, by
    rw [← LinearMap.comp_apply, ← TensorProduct.AlgebraTensorModule.map_comp]
    rfl⟩

theorem multV_ne_zero (P : LocPrime l) (K LL : FinExt l)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ)
    (hfd : FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) T.ρ τ)) (hj : IsJumpV (P.PD K) T.ρ τ a) :
    multV (P.PD K) T.ρ τ a ≠ 0 := by
  unfold multV
  have hle := FildR_succ_le P K LL T τ a
  have hlt : FildR (P.PD K) T.ρ τ (a + 1) < FildR (P.PD K) T.ρ τ a := lt_of_le_of_ne hle hj
  haveI := hfd
  haveI : FiniteDimensional ↥LL.1 ↥(FildR (P.PD K) T.ρ τ a) := Submodule.finiteDimensional_of_le inf_le_left
  have := Submodule.finrank_lt_finrank_of_lt hlt
  omega

theorem isJump_of_multV (P : LocPrime l) (K LL : FinExt l)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ)
    (h : multV (P.PD K) T.ρ τ a ≠ 0) : IsJumpV (P.PD K) T.ρ τ a := by
  intro he
  apply h
  unfold multV
  rw [he]
  simp

end Formalism.MainNotions.N.Ln34.CyclotomicLifting

end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules Formalism.MainNotions.N.Ln34.CyclotomicLifting

theorem padicValNat_le_of_dvd' (p : ℕ) {a b : ℕ} (hab : a ∣ b) (hb : b ≠ 0) :
    padicValNat p a ≤ padicValNat p b := by
  by_cases hp1 : p = 1
  · subst hp1
    first
      | simp
      | simp [padicValNat]
      | (unfold padicValNat; simp)
  · nth_rw 2 [Nat.padicValNat_def]
    have hd : p ^ padicValNat p a ∣ b := (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _)).trans hab
    have hf : FiniteMultiplicity p b := Nat.finiteMultiplicity_iff.2 ⟨hp1, Nat.pos_of_ne_zero hb⟩
    first
      | exact hf.le_multiplicity_of_pow_dvd hd
      | exact (hf.pow_dvd_iff_le_multiplicity).mp hd

theorem ePB_le_expLift_pf (l M H h : ℕ) (jumps : Finset ℤ) (hM : M ≤ h) (hH : H ≤ 2 * h) :
    Formalism.MainNotions.LiftingTheory.ePB l 1 M H jumps ≤ expLift l h (Formalism.MainNotions.LiftingTheory.JSet jumps M) := by
  unfold Formalism.MainNotions.LiftingTheory.ePB expLift LiftingTheory.eWB LIFT.eU
  have h1 : padicValNat l (2 * H).factorial ≤ padicValNat l (2 * (2 * h)).factorial :=
    padicValNat_le_of_dvd' l (Nat.factorial_dvd_factorial (by omega)) (Nat.factorial_ne_zero _)
  have h2 : padicValNat l M.factorial ≤ padicValNat l h.factorial :=
    padicValNat_le_of_dvd' l (Nat.factorial_dvd_factorial hM) (Nat.factorial_ne_zero _)
  omega

theorem JSet_sub_pf (jumps : Finset ℤ) (M h : ℕ) (hj : ∀ a ∈ jumps, -(h : ℤ) ≤ a ∧ a ≤ h)
    (hM : M ≤ h) :
    Formalism.MainNotions.LiftingTheory.JSet jumps M ⊆ Finset.Icc (-(h : ℤ)) (2 * h) ∧
      (0 : ℤ) ∉ Formalism.MainNotions.LiftingTheory.JSet jumps M := by
  unfold Formalism.MainNotions.LiftingTheory.JSet
  constructor
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨hx, -⟩ := Finset.mem_filter.mp hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
      obtain ⟨hb1, hb2⟩ := Finset.mem_Icc.mp hb
      obtain ⟨ha1, ha2⟩ := hj _ ha
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hx
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro h0
    rcases Finset.mem_union.mp h0 with h0 | h0
    · exact (Finset.mem_filter.mp h0).2 rfl
    · have h1 := (Finset.mem_Icc.mp h0).1
      omega

theorem pow_smul_mem_of_le {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M]
    (S : Submodule O M) (p : O) {e e' : ℕ} (he : e ≤ e') {c : M} (hc : p ^ e • c ∈ S) :
    p ^ e' • c ∈ S := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [pow_add, mul_comm, mul_smul]
  exact S.smul_mem _ hc

theorem jumpSet_bound {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (M h : ℕ) (hM : M ≤ h) : ∀ a ∈ Formalism.MainNotions.LiftingTheory.jumpSet W T M M, -(h : ℤ) ≤ a ∧ a ≤ h := by
  classical
  unfold Formalism.MainNotions.LiftingTheory.jumpSet
  intro a ha
  have ha' : a ∈ Finset.Icc (-(M : ℤ)) M := by
    first
      | exact Finset.mem_of_mem_filter a ha
      | (simp only [Finset.mem_filter] at ha; exact ha.1)
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha'
  constructor <;> omega

theorem lift_jumps_bounded {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l)
    {T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)} (Fm : LatHom T₁.L T₂.L) (h n : ℕ)
    (Js : Finset ℤ) (hJb : ∀ a ∈ Js, -(h : ℤ) ≤ a ∧ a ≤ h)
    (hL : Fm.LiftF (P.PD K) (Formalism.MainNotions.LiftingTheory.ePB l 1 (Formalism.MainNotions.LiftingTheory.Mmax n fun _ => h)
      (Formalism.MainNotions.LiftingTheory.Hmax n (fun _ => h) fun _ => h) Js)) :
    ∃ J : Finset ℤ, J ⊆ Finset.Icc (-(h : ℤ)) (2 * h) ∧ (0 : ℤ) ∉ J ∧
      Fm.LiftF (P.PD K) (expLift l h J) := by
  have hMm : Formalism.MainNotions.LiftingTheory.Mmax n (fun _ => h) ≤ h := by
    unfold Formalism.MainNotions.LiftingTheory.Mmax
    exact Finset.sup_le fun _ _ => le_rfl
  have hHm : Formalism.MainNotions.LiftingTheory.Hmax n (fun _ => h) (fun _ => h) ≤ 2 * h := by
    unfold Formalism.MainNotions.LiftingTheory.Hmax
    exact Finset.sup_le fun _ _ => by dsimp only; omega
  obtain ⟨hJ1, hJ2⟩ := JSet_sub_pf Js _ h hJb hMm
  refine ⟨_, hJ1, hJ2, ?_⟩
  have he := ePB_le_expLift_pf l _ _ h Js hMm hHm
  unfold Formalism.WeaklyAdmissibleFiltrations.LatHom.LiftF at hL ⊢
  intro c hc
  exact pow_smul_mem_of_le _ _ he (hL c hc)

theorem lift_bound_of_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ) (hA : Adm1 D HW F Cm CA CB CK) : liftR D := by
  obtain ⟨-, -, -, -, -, -, hA4, -, -, -, hA8, -, hA12⟩ := hA
  obtain ⟨-, -, -, -, hDesc⟩ := hA4
  intro l _ hl K LL hg T₁ T₂ Fm r S η m h up b hH
  have hKK : K.1 ≤ (cycL K).1 := hg.2.2.1
  have hle : GK (cycL K) ≤ GK K := GK_le hKK
  have hg1 : Good (cycL K) 1 LL := by
    refine ⟨le_rfl, fun h2 => absurd h2 hl, ?_, ?_⟩
    · rw [Ks_cycL K]; exact le_rfl
    · rw [Ks_cycL K]; exact hg.2.2.2
  have hD := hDesc l (cycL K) K hKK hle (GKin_normal K hKK) 1 LL hg1
  have hs : ((HW l).W (cycL K) 1 LL hg1).s = 1 := (HW l).W_s _ _ _ _
  have hCB : Formalism.MainNotions.LiftingTheory.CaseB ((HW l).W (cycL K) 1 LL hg1) := by
    refine ⟨?_, ?_⟩
    · rw [eq_top_iff]
      intro g _
      rw [((HW l).W (cycL K) 1 LL hg1).GKs_def, hs, Nat.cast_one, (D.loc l).PD_χ,
        ← map_one (algebraMap ℚ_[l] ↥LL.1), ← map_sub]
      exact v_ge_one _ LL _ (chi_cong (D.loc l) K g g.2)
    · rw [(D.loc l).PD_p, hs, finrank_cycL]
      simp
  have hv0 := hD.2 hCB rfl (by rw [max_unramified_cyclotomic_eq K]; exact inf_le_left)
  have hrange : (Subgroup.inclusion hle).range.Normal := by
    rw [range_inclusion_eq K hKK hle]
    exact GKin_normal K hKK
  have hres := hA12 l (cycL K) K hKK hle LL T₁ hH.1
  have hres2 := hA12 l (cycL K) K hKK hle LL T₂ hH.2.1
  have hL := (hD.1 hrange T₁ T₂ Fm (fun _ => h) (fun _ => h) ⟨hres.1, hres2.1, hH.2.2.1⟩
    (by
      intro i τ _ a ha
      have hm := multV_ne_zero (D.loc l) (cycL K) LL _ τ a ((hA8 l (cycL K) LL _).2 τ).1 ha
      rw [hres.2 τ a] at hm
      have := hH.2.2.2.2.2.2.2.1 (τ.comp (IntermediateField.inclusion hKK)) a
        (isJump_of_multV (D.loc l) K LL T₁ _ a hm)
      simpa using this)).2 hCB
  rw [(D.loc l).PD_p, hv0, add_zero, hs] at hL
  exact lift_jumps_bounded (D.loc l) K LL Fm h _ _
    (jumpSet_bound (D.loc l) (cycL K) LL _ _ _ h (Finset.sup_le fun _ _ => le_rfl)) hL

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UniformiserRingOfHypotheses
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem uniformiser_ring_of_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : adm1 D HW F Cm) : p9R D HW := by
  unfold adm1 Formalism.MainNotions.DeltaInvariantLattices.deltaInvariantLatticeGlobal Formalism.MainNotions.DeltaInvariantLattices.deltaInvariantLatticeLocal at h1
  intro l _ hl K LL hG T hT
  have h9 := (h1 l K 1 LL hG).2.2.2.2.2.2.2.2.1 T hT
  unfold Formalism.MainNotions.DeltaInvariantLattices.p9 at h9
  have hpe : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hs : ((HW l).W K 1 LL hG).s = 1 := by
    first
    | exact (HW l).W_s K 1 LL hG
    | exact (HW l).hs K 1 LL hG
    | exact (HW l).s_eq K 1 LL hG
    | exact (HW l).W_s
    | rfl
  obtain ⟨-, ⟨π', E, hr, -⟩, -⟩ := h9 hs (by rw [hpe]; exact hl)
  refine ⟨π', E, ?_⟩
  convert hr using 2 <;> first | rfl | (simp only [eK, sK, hpe]) | (unfold eK sK; simp [hpe])

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.QuotPf
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Gen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem qpf_filV_succ_le (a : ℤ) :
    FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  have h : (PD.Fil (a + 1)).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp := fun x hx => PD.Fil_anti a hx
  intro x hx
  rw [FilV, LinearMap.mem_range] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  refine ⟨AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion h) y, ?_⟩
  rw [← LinearMap.comp_apply, ← AlgebraTensorModule.map_comp, LinearMap.id_comp, Submodule.subtype_comp_inclusion]

theorem qpf_fildR_succ_le (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ (a + 1) ≤ FildR PD ρ τ a := by
  unfold FildR
  exact inf_le_inf_left _ (qpf_filV_succ_le PD a)

theorem qpf_isJumpV_iff_pos (τ : K →ₐ[Qp] LL) (hfin : Module.Finite LL ↥(DdRE PD ρ τ)) (a : ℤ) :
    IsJumpV PD ρ τ a ↔ 0 < multV PD ρ τ a := by
  have hle := qpf_fildR_succ_le PD ρ τ a
  haveI := hfin
  haveI : Module.Finite LL ↥(FildR PD ρ τ a) :=
    Module.Finite.of_injective (Submodule.inclusion (inf_le_left : FildR PD ρ τ a ≤ DdRE PD ρ τ))
      (Submodule.inclusion_injective _)
  unfold IsJumpV multV
  constructor
  · intro hne
    have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)
    omega
  · intro hpos heq
    rw [heq] at hpos
    simp at hpos

theorem qpf_multV_nonneg (τ : K →ₐ[Qp] LL) (hfin : Module.Finite LL ↥(DdRE PD ρ τ)) (a : ℤ) :
    0 ≤ multV PD ρ τ a := by
  by_cases h : FildR PD ρ τ (a + 1) = FildR PD ρ τ a
  · unfold multV
    rw [h]
    simp
  · exact le_of_lt ((qpf_isJumpV_iff_pos PD ρ τ hfin a).1 h)

end Gen

theorem quotient_jumps_subset (D : D7) (h8 : adm8 D) (h11 : adm11 D) : quotR D := by
  unfold quotR
  intro l _ hl2 K LL hG
  unfold quotA
  intro T₁ T₂ F hc1 hc2 hon τ X hJ a ha
  haveI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  have hden : Formalism.MainNotions.LiftingTheory.lker_Den ↥LL.1 ↥(OL LL) := by
    intro c
    have hint : IsIntegral ℚ_[l] c := Algebra.IsIntegral.isIntegral c
    have halg : IsAlgebraic ℤ_[l] c := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 hint.isAlgebraic
    have hinj : Function.Injective (algebraMap ℤ_[l] ↥LL.1) := by
      rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1]
      exact (algebraMap ℚ_[l] ↥LL.1).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
    obtain ⟨y, hy, hyc⟩ : ∃ y ≠ (0 : ℤ_[l]), IsIntegral ℤ_[l] (y • c) := by
      exact IsAlgebraic.exists_integral_multiple halg
    refine ⟨algebraMap ℤ_[l] ↥(OL LL) y, ?_, ⟨y • c, hyc⟩, ?_⟩
    · rw [← IsScalarTower.algebraMap_apply]
      exact fun h => hy (hinj (h.trans (map_zero _).symm))
    · rw [← IsScalarTower.algebraMap_apply]
      change _ = y • c
      rw [Algebra.smul_def]
  have hses : IsSESLat (Qp := ℚ_[l]) (Formalism.MainNotions.LiftingTheory.lker_ι F hon hden) F := by
    refine ⟨(LinearMap.ker F.f).injective_subtype, Formalism.MainNotions.LiftingTheory.lker_surj F hon, hon,
      fun x => ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, ?_⟩, fun y hy => hy⟩
    rintro ⟨y, rfl⟩
    exact LinearMap.mem_ker.1 y.2
  obtain ⟨-, -, hmult⟩ := h11 l K LL _ T₁ T₂ (Formalism.MainNotions.LiftingTheory.lker_ι F hon hden) F hses hc1
  apply hJ
  rw [qpf_isJumpV_iff_pos _ _ τ ((h8 l K LL T₂).2 τ).1] at ha
  rw [qpf_isJumpV_iff_pos _ _ τ ((h8 l K LL T₁).2 τ).1, hmult τ a]
  have h0 := qpf_multV_nonneg _ _ τ ((h8 l K LL (Formalism.MainNotions.LiftingTheory.lker_T₀ F hon hden)).2 τ).1 a
  omega

end Formalism.MainNotions.N.Ln34

end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem lifting_theorem_of_uniform_link (hU1L : FirstFrameOfModels) :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
      (CA CB CK C : ℝ), 160 ≤ C → FontExAll D HW F → DdRFull D → DiRank D HW F Cm →
        IntegralityFromMetric D HW F Cm CA CB CK C :=
  local_theorem_of_leaf_lemmas generator_bound_of_hypotheses lift_bound_of_hypotheses DvdPf.dvdCondition quotient_jumps_subset normR_holds
    uniformiser_ring_of_hypotheses ExtPf.ext_pf w_pf kerlam2_pf ninlam_pf gradNCondition frobPiNCondition gamPiCondition
    OneGenPf.onegen_pf univlink_pf invLiftCondition ClassMapPf.classmap_pf frame_pf modelflink_pf
    exponent_recursion_holds modell_pf modelqlink_pf hU1L kappi_pf RankLink.rank_link_holds
    (RankBounds.u2rank_of_ring u2ring_pf) DescentValuation.down_of_models (u3uplink_pf_of w_pf) u3mixlink_pf

end Formalism.MainNotions.N.Ln34

end
