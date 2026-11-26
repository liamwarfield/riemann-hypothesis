module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasCompactSupportTj
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CoheightEqOneOfDimClosure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSupportDcos

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingUnitOf
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingUnitOf
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open PositivityTheory.Rg.BcB.F.Tail hiding idem
open PositivityTheory.Rg.BcB.F.U (lpow lone)
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.MatchUnit

theorem hint_ind_conv {H : Type} [Group H] (K : Subgroup H) (y : H) :
    hint K (fun z => (K : Set H).indicator (1 : H → ℂ) z * (K : Set H).indicator (1 : H → ℂ) (z⁻¹ * y)) =
      (K : Set H).indicator (1 : H → ℂ) y := by
  by_cases hy : y ∈ K
  · have e : (fun z => (K : Set H).indicator (1 : H → ℂ) z * (K : Set H).indicator (1 : H → ℂ) (z⁻¹ * y)) =
        (K : Set H).indicator (1 : H → ℂ) := by
      funext z
      by_cases hz : z ∈ K
      · have hzy : z⁻¹ * y ∈ K := mul_mem (inv_mem hz) hy
        simp [Set.indicator_of_mem (show z ∈ (K : Set H) from hz),
          Set.indicator_of_mem (show z⁻¹ * y ∈ (K : Set H) from hzy)]
      · simp [Set.indicator_of_notMem (show z ∉ (K : Set H) from hz)]
    rw [e, GlobalTheory.CompanionTheory.FamClP.hint_ind, Set.indicator_of_mem (show y ∈ (K : Set H) from hy)]
    rfl
  · have e : (fun z => (K : Set H).indicator (1 : H → ℂ) z * (K : Set H).indicator (1 : H → ℂ) (z⁻¹ * y)) =
        fun _ => (0 : ℂ) := by
      funext z
      by_cases hz : z ∈ K
      · have hzy : z⁻¹ * y ∉ K := fun h => hy (by simpa using mul_mem hz h)
        simp [Set.indicator_of_notMem (show z⁻¹ * y ∉ (K : Set H) from hzy)]
      · simp [Set.indicator_of_notMem (show z ∉ (K : Set H) from hz)]
    rw [e, GlobalTheory.CompanionTheory.FamClP.hint_zero, Set.indicator_of_notMem (show y ∉ (K : Set H) from hy)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem blk_mem_KGL_iff {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    blk h w m (Multiplicative.toAdd X) ∈ GlobalTheory.LFun.KGL w (n := n) ↔ m ∈ K2 a b w ∧ X ∈ intMat a b w := by
  obtain ⟨hN, hM⟩ := GlobalTheory.CompanionTheory.LeviInt.comap_uN_and_map_sM E a b n h w
  have hdiag : ∀ c ∈ K2 a b w, blk h w c 0 ∈ GlobalTheory.LFun.KGL w (n := n) := fun c hc => hM ⟨c, hc, rfl⟩
  have hNK : ∀ Z, Z ∈ intMat a b w ↔ blk h w 1 (Multiplicative.toAdd Z) ∈ GlobalTheory.LFun.KGL w (n := n) := by
    intro Z
    rw [← hN, Subgroup.mem_comap, Subgroup.mem_subgroupOf, GlobalTheory.LeviFubini.uN_val]
  have hsplit : blk h w m (Multiplicative.toAdd X) = blk h w m 0 * blk h w 1 (Multiplicative.toAdd X) := by
    have := GlobalTheory.CompanionTheory.IntDec.blk_add h w m 0 (Multiplicative.toAdd X)
    simpa using this
  constructor
  · intro hb
    have hm : m ∈ K2 a b w := by
      have h2 := GlobalTheory.LeviFubini.levH_mem_KGL_of_mem E a b n h w
        ⟨blk h w m (Multiplicative.toAdd X), GlobalTheory.LeviFubini.blk_mem h w m _⟩ hb
      rw [GlobalTheory.LeviFubini.levH_blk] at h2
      exact Subgroup.mem_prod.2 h2
    refine ⟨hm, (hNK X).2 ?_⟩
    have e : blk h w 1 (Multiplicative.toAdd X) = (blk h w m 0)⁻¹ * blk h w m (Multiplicative.toAdd X) := by
      rw [hsplit]
      group
    rw [e]
    exact mul_mem (inv_mem (hdiag m hm)) hb
  · rintro ⟨hm, hX⟩
    rw [hsplit]
    exact mul_mem (hdiag m hm) ((hNK X).1 hX)

variable {n : ℕ}

theorem val_toSub {w : Pl E} (hU : UL n w = ⊤) (y : GLw n w) : ((toSub (UL n w) y : UL n w) : GLw n w) = y := by
  have hy : y ∈ UL n w := hU ▸ Subgroup.mem_top y
  simp [toSub, hy]

theorem lone_toSub {w : Pl E} (hU : UL n w = ⊤) (y : GLw n w) :
    lone (KL n w) (toSub (UL n w) y) = if y ∈ GlobalTheory.LFun.KGL w (n := n) then 1 else 0 := by
  rw [GlobalTheory.CompanionTheory.UnitaryWord.lone_KL]
  unfold GlobalTheory.CompanionTheory.UnitaryWord.unitFn
  by_cases hy : y ∈ GlobalTheory.LFun.KGL w (n := n)
  · have : toSub (UL n w) y ∈ (KL n w : Set (UL n w)) := by
      show toSub (UL n w) y ∈ KL n w
      rw [KL, Subgroup.mem_subgroupOf, val_toSub hU]
      exact hy
    rw [if_pos hy, Set.indicator_of_mem this]
    rfl
  · have : toSub (UL n w) y ∉ (KL n w : Set (UL n w)) := by
      intro h'
      have h'' : toSub (UL n w) y ∈ KL n w := h'
      rw [KL, Subgroup.mem_subgroupOf, val_toSub hU] at h''
      exact hy h''
    rw [if_neg hy, Set.indicator_of_notMem this]

theorem ct_lone {a b : ℕ} (h : a + b = n) {w : Pl E} (hU : UL n w = ⊤) (m : GLw a w × GLw b w) :
    ct h w (fun y => lone (KL n w) (toSub (UL n w) y)) m = if m ∈ K2 a b w then 1 else 0 := by
  have hk : ∀ X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)),
      GlobalTheory.BCT.avg (fun k : GlobalTheory.LFun.KGL w (n := n) => lone (KL n w) (toSub (UL n w)
        ((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k))) =
      if m ∈ K2 a b w ∧ X ∈ intMat a b w then 1 else 0 := by
    intro X
    have e : (fun k : GlobalTheory.LFun.KGL w (n := n) => lone (KL n w) (toSub (UL n w)
        ((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k))) =
        fun _ => if m ∈ K2 a b w ∧ X ∈ intMat a b w then (1 : ℂ) else 0 := by
      funext k
      rw [lone_toSub hU]
      have hiff : (k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k ∈ GlobalTheory.LFun.KGL w (n := n) ↔
          m ∈ K2 a b w ∧ X ∈ intMat a b w := by
        rw [← blk_mem_KGL_iff h w m X, Subgroup.mul_mem_cancel_right _ k.2,
          Subgroup.mul_mem_cancel_left _ (inv_mem k.2)]
      simp only [hiff]
    rw [e]
    exact GlobalTheory.CompanionTheory.CtS.avg_const _
  unfold ct
  simp only [hk]
  by_cases hm : m ∈ K2 a b w
  · obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hm
    have hv : Valued.v (m.1.val.det ^ b / m.2.val.det ^ a) = 1 := by
      rw [map_div₀, map_pow, map_pow, GlobalTheory.CompanionTheory.CtHecke.v_det h1, GlobalTheory.CompanionTheory.CtHecke.v_det h2]
      simp
    have habs : absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) = 1 := by
      unfold absHalf
      rw [GlobalTheory.CompanionTheory.CtHecke.ordL_eq_zero hv]
      simp
    have e : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        if m ∈ K2 a b w ∧ X ∈ intMat a b w then (1 : ℂ) else 0) =
        (intMat a b w : Set _).indicator 1 := by
      funext X
      by_cases hX : X ∈ intMat a b w
      · simp [hm, hX, Set.indicator_of_mem (show X ∈ (intMat a b w : Set _) from hX)]
      · simp [hX, Set.indicator_of_notMem (show X ∉ (intMat a b w : Set _) from hX)]
    rw [e, GlobalTheory.CompanionTheory.FamClP.hint_ind, habs, if_pos hm, mul_one]
  · have e : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        if m ∈ K2 a b w ∧ X ∈ intMat a b w then (1 : ℂ) else 0) = fun _ => 0 := by
      funext X
      simp [hm]
    rw [e, GlobalTheory.CompanionTheory.FamClP.hint_zero, if_neg hm, mul_zero]

theorem ctMu_lone {a b : ℕ} (h : a + b = n) {w : Pl E} (hU : UL n w = ⊤) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hμ : ∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1) :
    ctMu h w μ (lone (KL n w)) = idem (K2 a b w) := by
  funext m
  unfold ctMu
  rw [ct_lone h hU]
  by_cases hm : m ∈ K2 a b w
  · have h1 : μ (-1) = 1 := by
      refine hμ _ (GlobalTheory.CompanionTheory.CtHecke.ordL_eq_zero ?_)
      simp
    have hu := GlobalTheory.CompanionTheory.CtHecke.mu_unit hμ hm
    have e : μ ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) = 1 := by
      rw [mul_assoc, map_mul, hu, map_pow, h1]
      simp
    rw [e, if_pos hm]
    unfold idem
    rw [Set.indicator_of_mem (show m ∈ (K2 a b w : Set _) from hm), Subgroup.relIndex_self]
    simp
  · rw [if_neg hm, mul_zero]
    unfold idem
    rw [Set.indicator_of_notMem (show m ∉ (K2 a b w : Set _) from hm)]

theorem lpow_lone_one {w : Pl E} : lpow (KL n w) (lone (KL n w)) 1 = (KL n w : Set (UL n w)).indicator 1 := by
  funext y
  show lconv (lone (KL n w)) (lone (KL n w)) y = _
  rw [GlobalTheory.CompanionTheory.UnitaryWord.lone_KL]
  exact hint_ind_conv (KL n w) y

theorem isHecke_lone_KL (hE : Unr E) {w : Pl E} : IsHecke (KL n w) (lone (KL n w)) := by
  rw [GlobalTheory.CompanionTheory.UnitaryWord.lone_KL]
  refine ⟨HasCompactSupport.intro (GlobalTheory.CompanionTheory.SphLine.isCompact_KL hE n w) fun x hx =>
    Set.indicator_of_notMem hx _, fun k hk x => ?_⟩
  have h1 : k * x ∈ KL n w ↔ x ∈ KL n w := Subgroup.mul_mem_cancel_left _ hk
  have h2 : x * k ∈ KL n w ↔ x ∈ KL n w := Subgroup.mul_mem_cancel_right _ hk
  unfold GlobalTheory.CompanionTheory.UnitaryWord.unitFn
  by_cases hx : x ∈ KL n w
  · exact ⟨by rw [Set.indicator_of_mem (show k * x ∈ (KL n w : Set _) from h1.2 hx),
      Set.indicator_of_mem (show x ∈ (KL n w : Set _) from hx)]; rfl,
      by rw [Set.indicator_of_mem (show x * k ∈ (KL n w : Set _) from h2.2 hx),
      Set.indicator_of_mem (show x ∈ (KL n w : Set _) from hx)]; rfl⟩
  · exact ⟨by rw [Set.indicator_of_notMem (show k * x ∉ (KL n w : Set _) from fun h => hx (h1.1 h)),
      Set.indicator_of_notMem (show x ∉ (KL n w : Set _) from hx)],
      by rw [Set.indicator_of_notMem (show x * k ∉ (KL n w : Set _) from fun h => hx (h2.1 h)),
      Set.indicator_of_notMem (show x ∉ (KL n w : Set _) from hx)]⟩

theorem isOpen_levelSubgroup' (a b : ℕ) (w : Pl E) : IsOpen (K2 a b w : Set (GLw a w × GLw b w)) := by
  have e : (K2 a b w : Set (GLw a w × GLw b w)) =
      (GlobalTheory.LFun.KGL w (n := a) : Set (GLw a w)) ×ˢ (GlobalTheory.LFun.KGL w (n := b) : Set (GLw b w)) := rfl
  rw [e]
  exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1

theorem matchLMUnitOf : PositivityTheory.Rg.BcB.F.MLM.MatchLMUnitOf := by
  intro hI hS hId E _ _ _ hE n d _ a ha w hwB hgood
  have hT : w ∉ d.T := fun h => hwB (by simp [LocData.B, h])
  have hS₀ : w ∉ d.S₀ := fun h => hwB (by simp [LocData.B, h])
  have hBad : w ∉ d.Bad := fun h => hwB (by simp [LocData.B, h])
  have hP : w ∉ d.P := by simp [LocData.P, hT, hS₀]
  have hlev : d.lev a w = K2 a (n - a) w := by
    unfold LocData.lev
    rw [if_neg hT, if_neg (by simp [hS₀, hBad])]
  have htr : (d.eL a).tr d.P d.one w = idem (K2 a (n - a) w) := by
    unfold LM.tr
    rw [if_neg hP]
    show idem (d.lev a w) = _
    rw [hlev]
  rw [htr]
  by_cases hw : IsSplitAt w
  · rw [if_pos hw]
    obtain ⟨-, -, -, -, hμ⟩ := hgood hw
    have hU : UL n w = ⊤ := if_pos hw
    have hc := ctMu_lone (Nat.add_sub_cancel' ha) hU (d.μ w) hμ
    have h : Match n a (n - a) w (d.μ w) (lpow (KL n w) (lone (KL n w)) 1)
        (mconv (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (lone (KL n w)))
          (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (lone (KL n w)))) :=
      hS E n a ha w hw (d.μ w) hμ (lone (KL n w)) (isHecke_lone_KL hE) 1 le_rfl
    obtain ⟨hH, -, hU'⟩ := hId E a (n - a) w (K2 a (n - a) w) (isOpen_levelSubgroup' a (n - a) w) le_rfl
    rw [hc, (hU' _ hH).1, lpow_lone_one] at h
    exact h
  · rw [if_neg hw]
    exact hI E hE w hw n a ha

end GlobalTheory.CompanionTheory.MatchUnit

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingUnitOfStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matching_unit_of : PositivityTheory.Rg.BcB.F.MLM.MatchLMUnitOf := by
  first | exact @GlobalTheory.CompanionTheory.MatchUnit.matchLMUnitOf | exact GlobalTheory.CompanionTheory.MatchUnit.matchLMUnitOf | (intros; apply GlobalTheory.CompanionTheory.MatchUnit.matchLMUnitOf <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.O1ClassPullbackNaturality
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.O1ClassPullbackNaturality
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup

namespace GlobalTheory.CompanionTheory.MixZ

def chartPullPullO {R : Type} [CommRing R] {N : ℕ} {S T : Scheme.{0}} (r : T ⟶ S) (φ : S ⟶ PSpace R N) :
    ChartPull (pullO (r ≫ φ) 1) (pullO φ 1) r where
  idx i := i
  le _ _ h := h
  g y i j hi hj := by
    have hle : (pullO (r ≫ φ) 1).U i ⊓ (pullO (r ≫ φ) 1).U j ≤
        r ⁻¹ᵁ ((pullO φ 1).U i ⊓ (pullO φ 1).U j) := fun _ h => h
    have hm : r y ∈ (pullO φ 1).U i ⊓ (pullO φ 1).U j := ⟨hi, hj⟩
    have ev : (((pullO φ 1).g i j : Γ(S, (pullO φ 1).U i ⊓ (pullO φ 1).U j)ˣ) :
        Γ(S, (pullO φ 1).U i ⊓ (pullO φ 1).U j)) = pullRatio φ _ i inf_le_left j :=
      (Units.val_pow_eq_pow_val _ _).trans (pow_one _)
    have ev' : (((pullO (r ≫ φ) 1).g i j : Γ(T, (pullO (r ≫ φ) 1).U i ⊓ (pullO (r ≫ φ) 1).U j)ˣ) :
        Γ(T, (pullO (r ≫ φ) 1).U i ⊓ (pullO (r ≫ φ) 1).U j)) = pullRatio (r ≫ φ) _ i inf_le_left j :=
      (Units.val_pow_eq_pow_val _ _).trans (pow_one _)
    have e : (pullO (r ≫ φ) 1).g i j = res hle (pullU r _ ((pullO φ 1).g i j)) := by
      apply Units.ext
      refine ev'.trans (Eq.trans ?_ (congrArg (r.appLE _ _ hle).hom ev).symm)
      exact (appLE_pullRatio (hi := inf_le_left) r hle).symm
    rw [e, gm_res (𝟙 T) y hle ⟨hi, hj⟩, gm_pull (𝟙 T) r y _ hm, Category.id_comp]

theorem cls_pullO_comp {R : Type} [CommRing R] {N : ℕ} {S T : Scheme.{0}} (r : T ⟶ S) (φ : S ⟶ PSpace R N) :
    cls (pullO (r ≫ φ) 1) (isLB_pullO _ 1) = CechPic.pull r (cls (pullO φ 1) (isLB_pullO _ 1)) := by
  rw [← cls_pull (isLB_pullO φ 1) r (pull_isLB (isLB_pullO φ 1) r)]
  exact (cls_eq_iff _ _).2 (LBIso.chartPull (chartPullPullO r φ)
    (chartPullPull (pullO φ 1) r) (PolBaseChange.lbIso_refl (isLB_pullO φ 1)))

end GlobalTheory.CompanionTheory.MixZ
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.O1ClassPullbackNaturalityStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cls_pullO_one_comp_eq_pull : ∀ {R : Type} [CommRing R] {N : ℕ} {S T : Scheme.{0}} (r : T ⟶ S) (φ : S ⟶ PSpace R N), cls (pullO (r ≫ φ) 1) (isLB_pullO _ 1) = CechPic.pull r (cls (pullO φ 1) (isLB_pullO _ 1)) := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.cls_pullO_comp | exact GlobalTheory.CompanionTheory.MixZ.cls_pullO_comp | (intros; apply GlobalTheory.CompanionTheory.MixZ.cls_pullO_comp <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LawOfOrbitMeasure
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LawOfOrbitMeasure
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting.LawPf

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem C1_mul (hn : W.rank + t = n) {a b : ℕ} (A : Mx D a b) (U : Mx D b n) :
    c1 (W := W) hn (mm A U) = mm A (c1 (W := W) hn U) := by
  ext i j; rfl

theorem mul_sub_one_mulVec_mem_spL (hn : W.rank + t = n) {a b : ℕ} (A : Mx D a b) (U : Mx D b n) :
    c2 (W := W) hn (mm A U) = mm A (c2 (W := W) hn U) := by
  ext i j; rfl

theorem isOneCochain_add (hn : W.rank + t = n) {a : ℕ} (U V : Mx D a n) :
    c1 (W := W) hn (U + V) = c1 (W := W) hn U + c1 (W := W) hn V := by
  ext i j; rfl

theorem isTwoCochain_add (hn : W.rank + t = n) {a : ℕ} (U V : Mx D a n) :
    c2 (W := W) hn (U + V) = c2 (W := W) hn U + c2 (W := W) hn V := by
  ext i j; rfl

theorem first_columns_join_eq (hn : W.rank + t = n) {a : ℕ} (x : Mx D a W.rank) (v : Mx D a t) :
    c1 (W := W) hn (jn hn x v) = x := by
  ext i j
  simp [c1, jn]

theorem second_columns_join_eq (hn : W.rank + t = n) {a : ℕ} (x : Mx D a W.rank) (v : Mx D a t) :
    c2 (W := W) hn (jn hn x v) = v := by
  ext i j
  simp [c2, jn]

theorem ww_mul_inv (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h b : GA D W) :
    ww W x₀ (h * b⁻¹) = mm (mt W b) (ww W x₀ h) := by
  simp only [ww, mm, mul_inv_rev, inv_inv, mt_mul, Matrix.mul_assoc]

theorem ac_zp (d : HypDec B W t) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    {g : GA D B} {α : Mx D t t} {c : Mx D t W.rank} {b : GA D W}
    (h1 : mm (mt B g) d.jX = mm d.jX α) (h2 : mm (mt B g) d.j0 = mm d.jX c + mm d.j0 (mt W b)) (p : Par D n t W) :
    ac B g (zp d hn x₀ p) =
      zp d hn x₀ (p.1 * b⁻¹, mm α p.2.1 + jn hn (mm c (ww W x₀ p.1)) 0, p.2.2) := by
  have key : mm (mt B g) (mm d.jX (c1 (W := W) hn p.2.1) + mm d.j0 (ww W x₀ p.1)) =
      mm d.jX (c1 (W := W) hn (mm α p.2.1 + jn hn (mm c (ww W x₀ p.1)) 0)) + mm d.j0 (ww W x₀ (p.1 * b⁻¹)) := by
    rw [isOneCochain_add, C1_mul, first_columns_join_eq, ww_mul_inv]
    simp only [mm] at h1 h2 ⊢
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, h2, Matrix.add_mul, Matrix.mul_add]
    simp only [Matrix.mul_assoc]
    abel
  have key2 : mm (mt B g) (mm d.jX (c2 (W := W) hn p.2.1)) =
      mm d.jX (c2 (W := W) hn (mm α p.2.1 + jn hn (mm c (ww W x₀ p.1)) 0)) := by
    rw [isTwoCochain_add, mul_sub_one_mulVec_mem_spL, second_columns_join_eq]
    simp only [mm] at h1 ⊢
    rw [← Matrix.mul_assoc, h1, add_zero, Matrix.mul_assoc]
  unfold ac zp
  refine Prod.ext key ?_
  change mm (mt B g) (mm (mm d.jX (c1 (W := W) hn p.2.1) + mm d.j0 (ww W x₀ p.1)) p.2.2 + mm d.jX (c2 (W := W) hn p.2.1)) =
    mm (mm d.jX (c1 (W := W) hn (mm α p.2.1 + jn hn (mm c (ww W x₀ p.1)) 0)) + mm d.j0 (ww W x₀ (p.1 * b⁻¹))) p.2.2 +
      mm d.jX (c2 (W := W) hn (mm α p.2.1 + jn hn (mm c (ww W x₀ p.1)) 0))
  rw [← key, ← key2]
  simp only [mm]
  rw [Matrix.mul_add, Matrix.mul_assoc]

theorem map_aff {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsAddHaarMeasure]
    (φ : G ≃ₜ+ G) (s : G) : ν.map (fun U => φ U + s) = (addEquivAddHaarChar φ)⁻¹ • ν := by
  have h := addEquivAddHaarChar_smul_map ν φ
  have hne : addEquivAddHaarChar φ ≠ 0 := (addEquivAddHaarChar_pos φ).ne'
  have hm : ν.map φ = (addEquivAddHaarChar φ)⁻¹ • ν := by
    conv_rhs => rw [← h]
    rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
  have e : (fun U : G => φ U + s) = (fun U => U + s) ∘ φ := rfl
  have hφ : Measurable (φ : G → G) := φ.continuous.measurable
  rw [e, ← Measure.map_map (measurable_add_const s) hφ, hm, Measure.map_smul, map_add_right_eq_self]
  exact (measurable_add_const s).aemeasurable

theorem map_skew {H A Y : Type} [MeasurableSpace H] [MeasurableSpace A] [MeasurableSpace Y] {m : Measure H} {ν : Measure A}
    {μ : Measure Y} [SFinite m] [SFinite ν] [SFinite μ] {g : H → H} (hg : MeasurePreserving g m m) {f : H → A → A}
    (hf : Measurable (Function.uncurry f)) {c : ℝ≥0} (hc : ∀ h, ν.map (f h) = c • ν) :
    (m.prod (ν.prod μ)).map (fun p : H × A × Y => (g p.1, f p.1 p.2.1, p.2.2)) = c • m.prod (ν.prod μ) := by
  have hfm : ∀ h, Measurable (f h) := fun h => hf.of_uncurry_left
  have hs : Measurable (Function.uncurry fun (h : H) (z : A × Y) => ((f h z.1, z.2) : A × Y)) :=
    (hf.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk (measurable_snd.comp measurable_snd)
  have h1 : ∀ h, (ν.prod μ).map (fun z : A × Y => ((f h z.1, z.2) : A × Y)) = c • (ν.prod μ) := fun h => by
    have e := Measure.map_prod_map ν μ (hfm h) measurable_id
    rw [Measure.map_id, hc h] at e
    have e2 : (c • ν).prod μ = c • ν.prod μ := by
      have := Measure.prod_smul_left (μ := ν) (ν := μ) (c : ℝ≥0∞)
      exact this
    rw [e2] at e
    exact e.symm
  have h2 := (hg.skew_product hs (.of_forall h1)).map_eq
  rw [h2]
  exact Measure.prod_smul_right (μ := m) (ν := ν.prod μ) (c : ℝ≥0∞)

theorem map_left_add (a : GL (Fin t) (AE D)) (ν : Measure (Mx D t n)) (hν : ν.IsAddHaarMeasure) (s : Mx D t n) :
    ν.map (fun U => mm a.1 U + s) = ((absA D (Matrix.GeneralLinearGroup.det a))⁻¹ ^ n : ℝ≥0) • ν := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := top_mx (D := D) t n
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hc : addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE a (1 : GL (Fin n) (AE D))) = absA D (Matrix.GeneralLinearGroup.det a) ^ n := by
    have := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE D.host.F D.host.E D.sp.cm.sig (isCMExt_host D) t n
      a (1 : GL (Fin n) (AE D))
    simpa using this
  have h := map_aff ν (GlobalTheory.ModuLR.lrCE a (1 : GL (Fin n) (AE D))) s
  rw [hc, ← inv_pow] at h
  rw [← h]
  congr 1
  funext U
  simp [GlobalTheory.ModuLR.lrCE_apply, mm]

theorem map_tau {d : HypDec B W t} (I : IkD d n) (μ : Measure (Mx D W.rank t)) (hμ : μ.IsAddHaarMeasure)
    (a : GL (Fin t) (AE D)) (b : GA D W) {S : GA D W → Mx D t n} (hS : Continuous S) :
    (Q0 I μ).map (fun p : Par D n t W => (p.1 * b, mm a.1 p.2.1 + S p.1, p.2.2)) =
      ((absA D (Matrix.GeneralLinearGroup.det a))⁻¹ ^ n : ℝ≥0) • Q0 I μ := by
  obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t n
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
  obtain ⟨g1, g2, g3, -, g5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hB : BorelSpace (GA D W) := ⟨rfl⟩
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨𝓕, hf⟩ := I.cov₁
  have hH := hf.1
  have hhaar := I.haar
  haveI := GlobalTheory.RegSch.Ibp.isMulRightInvariant I.m
  have hr : MeasurePreserving (fun h : GA D W => h * b) I.m I.m := measurePreserving_mul_right I.m b
  have hsm : Measurable (Function.uncurry fun (h : GA D W) (U : Mx D t n) => mm a.1 U + S h) := by
    have : Continuous (Function.uncurry fun (h : GA D W) (U : Mx D t n) => mm a.1 U + S h) :=
      (continuous_const.matrix_mul continuous_snd).add (hS.comp continuous_fst)
    exact this.measurable
  exact map_skew hr hsm fun h => map_left_add a I.μ₁ hH (S h)

theorem continuous_S (hn : W.rank + t = n) (c : Mx D t W.rank) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Continuous fun h : GA D W => jn hn (mm c (ww W x₀ h)) (0 : Mx D t t) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hc : Continuous fun h : GA D W => mm c (ww W x₀ h) := continuous_const.matrix_mul (continuous_ww x₀)
  refine continuous_matrix fun i j => ?_
  unfold jn
  simp only [Matrix.submatrix_apply, id]
  generalize (finSumFinEquiv.trans (finCongr hn)).symm j = s
  cases s with
  | inl k => exact hc.matrix_elem i k
  | inr k => exact continuous_const

theorem law : Law := by
  intro D n t B W d hn I μ hμ x₀ q
  subst hn
  obtain ⟨c, g, hcg⟩ := GlobalTheory.RegSch.IkStab.exists_valuation_adapted_index d q.2
  have h1 := GlobalTheory.RegSW.mul_jX d q
  obtain ⟨g1, g2⟩ := top_pair (D := D) B.rank W.rank t
  obtain ⟨p1, p2⟩ := top_par (D := D) (W.rank + t) t W
  obtain ⟨-, -, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t (W.rank + t)
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have o0 : OpensMeasurableSpace (Par D (W.rank + t) t W) := p1.opensMeasurable
  have o1 : OpensMeasurableSpace (Mx D B.rank W.rank × Mx D B.rank t) := g1.opensMeasurable
  have hS := continuous_S (W := W) (t := t) rfl c x₀
  have hac : Measurable (ac B (q : GA D B) (a := W.rank) (b := t)) :=
    ((continuous_ac B).comp (continuous_const.prodMk continuous_id)).measurable
  have hτ : Measurable fun p : Par D (W.rank + t) t W =>
      ((p.1 * g⁻¹, mm (GlobalTheory.RegSW.onX d q).1 p.2.1 + jn rfl (mm c (ww W x₀ p.1)) (0 : Mx D t t), p.2.2) : Par D (W.rank + t) t W) :=
    Continuous.measurable ((continuous_fst.mul continuous_const).prodMk
      (((continuous_const.matrix_mul (continuous_fst.comp continuous_snd)).add (hS.comp continuous_fst)).prodMk
        (continuous_snd.comp continuous_snd)))
  have e : (ac B (q : GA D B)) ∘ zp d rfl x₀ = zp d rfl x₀ ∘ fun p : Par D (W.rank + t) t W =>
      ((p.1 * g⁻¹, mm (GlobalTheory.RegSW.onX d q).1 p.2.1 + jn rfl (mm c (ww W x₀ p.1)) (0 : Mx D t t), p.2.2) : Par D (W.rank + t) t W) :=
    funext fun p => ac_zp d rfl x₀ h1 hcg p
  unfold rho
  rw [Measure.map_map hac (measurable_zp d rfl x₀), e, ← Measure.map_map (measurable_zp d rfl x₀) hτ,
    map_tau I μ hμ (GlobalTheory.RegSW.onX d q) g⁻¹ hS, Measure.map_smul]
  · rfl
  · exact (measurable_zp d rfl x₀).aemeasurable

end GlobalTheory.CompanionTheory.ColumnSplitting.LawPf

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LawOfOrbitMeasureStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.law_of_orbit_measure : Law := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.LawPf.law | exact GlobalTheory.CompanionTheory.ColumnSplitting.LawPf.law | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.LawPf.law <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepClassDecomposition
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepClassDecomposition
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup

namespace GlobalTheory.CompanionTheory.MPDict.ClsRep

open GlobalTheory.CompanionTheory.MPDict.IsomT GlobalTheory.CompanionTheory.MPDict.TensRep

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

def HasFrame (L : LB (MP ℤ m n)) (a : Fin (m + 1) → ℤ) : Prop :=
  ∃ u : ∀ (i : L.ι) (c : ∀ k, Bk n k), Γ(MP ℤ m n, L.U i ⊓ mchart c)ˣ,
    (∀ i j c,
      Semi.res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          L.U i ⊓ L.U j ⊓ mchart c ≤ L.U j ⊓ mchart c) (u j c) =
        Semi.res (inf_le_left : L.U i ⊓ L.U j ⊓ mchart c ≤ L.U i ⊓ L.U j) (L.g i j) *
          Semi.res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            L.U i ⊓ L.U j ⊓ mchart c ≤ L.U i ⊓ mchart c) (u i c)) ∧
    (∀ i c c',
      Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          L.U i ⊓ (mchart c ⊓ mchart c') ≤ L.U i ⊓ mchart c) (u i c) =
        Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          L.U i ⊓ (mchart c ⊓ mchart c') ≤ L.U i ⊓ mchart c') (u i c') *
        ∏ k, blockUnit (c k) (c' k) (fun _ hx =>
          ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
            L.U i ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) ^ a k)

theorem hasFrame_of_isHermRep {M : HermLB (mpStr ℤ m n)} {A : Geo.HermLine (Bk n)} (h : IsHermRep M A) :
    HasFrame M.B A.a := by
  obtain ⟨u, h₁, h₂, -⟩ := h
  exact ⟨u, h₁, h₂⟩

theorem iSup_mchart : ⨆ c : (∀ k, Bk n k), mchart c = (⊤ : (MP ℤ m n).Opens) := by
  refine top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨fun k => ptChart x k, ?_⟩
  exact Set.mem_iInter.2 fun k => mem_ptChart x k

theorem cg₃ {G : Type*} [CommGroup G] {x x' y y' P : G} (h : x = x' * P) (h' : y = y' * P) :
    x * y⁻¹ = x' * y'⁻¹ := by
  subst h h'
  rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]

theorem cg₄ {G : Type*} [CommGroup G] {x x' y y' g g' : G} (h : x' = g' * x) (h' : y' = g * y) :
    x * y⁻¹ = g * g'⁻¹ * (x' * y'⁻¹) := by
  subst h h'
  simp only [mul_inv]
  rw [show g * g'⁻¹ * (g' * x * (g⁻¹ * y⁻¹)) = (g * g⁻¹) * (g'⁻¹ * g') * (x * y⁻¹) by ac_rfl]
  simp

theorem lbIso_of_hasFrame {L N : LB (MP ℤ m n)} {a : Fin (m + 1) → ℤ} (hL : HasFrame L a) (hN : HasFrame N a) :
    LBIso L N := by
  obtain ⟨u, u₁, u₂⟩ := hL
  obtain ⟨v, v₁, v₂⟩ := hN
  have hglue (p : N.ι × L.ι) : ∃ t : Γ(MP ℤ m n, N.U p.1 ⊓ L.U p.2)ˣ, ∀ c,
      Semi.res inf_le_left t =
        Semi.res (ofMem fun _ hx => ⟨hx.1.2, hx.2⟩ : (N.U p.1 ⊓ L.U p.2) ⊓ mchart c ≤ L.U p.2 ⊓ mchart c) (u p.2 c) *
        (Semi.res (ofMem fun _ hx => ⟨hx.1.1, hx.2⟩ : (N.U p.1 ⊓ L.U p.2) ⊓ mchart c ≤ N.U p.1 ⊓ mchart c) (v p.1 c))⁻¹ := by
    refine exists_glue mchart iSup_mchart _ _ fun c c' => ?_
    have e₁ := (congrArg (Semi.res (ofMem fun _ hx => ⟨hx.1.1.2, hx.1.2, hx.2.2⟩ :
      ((N.U p.1 ⊓ L.U p.2) ⊓ mchart c) ⊓ ((N.U p.1 ⊓ L.U p.2) ⊓ mchart c') ≤ L.U p.2 ⊓ (mchart c ⊓ mchart c'))) (u₂ p.2 c c')).trans
      (res_mul_prod c c' a _ _ _)
    have e₂ := (congrArg (Semi.res (ofMem fun _ hx => ⟨hx.1.1.1, hx.1.2, hx.2.2⟩ :
      ((N.U p.1 ⊓ L.U p.2) ⊓ mchart c) ⊓ ((N.U p.1 ⊓ L.U p.2) ⊓ mchart c') ≤ N.U p.1 ⊓ (mchart c ⊓ mchart c'))) (v₂ p.1 c c')).trans
      (res_mul_prod c c' a _ _ _)
    simp only [map_mul, map_inv, res_twice] at e₁ e₂ ⊢
    exact cg₃ e₁ e₂
  choose t ht using hglue
  have htT (p : N.ι × L.ι) (c : ∀ k, Bk n k) {T : (MP ℤ m n).Opens} (hT : T ≤ (N.U p.1 ⊓ L.U p.2) ⊓ mchart c) :
      Semi.res (hT.trans inf_le_left) (t p) =
        Semi.res (ofMem fun _ hx => ⟨(hT hx).1.2, (hT hx).2⟩ : T ≤ L.U p.2 ⊓ mchart c) (u p.2 c) *
        (Semi.res (ofMem fun _ hx => ⟨(hT hx).1.1, (hT hx).2⟩ : T ≤ N.U p.1 ⊓ mchart c) (v p.1 c))⁻¹ := by
    have e := congrArg (Semi.res hT) (ht p c)
    simpa only [map_mul, map_inv, res_twice] using e
  refine ⟨⟨t⟩, fun (p q : N.ι × L.ι) => units_ext_cover mchart iSup_mchart fun c => ?_⟩
  change Semi.res (inf_le_left : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c ≤ (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2))
      (Semi.res (inf_le_left : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ≤ N.U p.1 ⊓ L.U p.2) (t p)) =
    Semi.res (inf_le_left : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c ≤ (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2))
      ((Semi.res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ≤ N.U p.1 ⊓ N.U q.1) (N.g p.1 q.1) *
        (Semi.res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ≤ L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹) *
        Semi.res (inf_le_right : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ≤ N.U q.1 ⊓ L.U q.2) (t q))
  simp only [map_mul, map_inv, res_twice]
  rw [htT p c (T := (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c) (ofMem fun _ hx => ⟨hx.1.1, hx.2⟩),
    htT q c (T := (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c) (ofMem fun _ hx => ⟨hx.1.2, hx.2⟩)]
  have hU : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c ≤ L.U p.2 ⊓ L.U q.2 ⊓ mchart c :=
    ofMem fun _ hx => ⟨⟨hx.1.1.2, hx.1.2.2⟩, hx.2⟩
  have hV : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c ≤ N.U p.1 ⊓ N.U q.1 ⊓ mchart c :=
    ofMem fun _ hx => ⟨⟨hx.1.1.1, hx.1.2.1⟩, hx.2⟩
  have e₁ := congrArg (Semi.res hU) (u₁ p.2 q.2 c)
  have e₂ := congrArg (Semi.res hV) (v₁ p.1 q.1 c)
  simp only [map_mul, res_twice] at e₁ e₂
  exact cg₄ e₁ e₂

theorem hasFrame_tens {L N : LB (MP ℤ m n)} {a b : Fin (m + 1) → ℤ} (hL : HasFrame L a) (hN : HasFrame N b) :
    HasFrame (GlobalTheory.CechPic.tens L N) (a + b) := by
  obtain ⟨u, hu₁, hu₂⟩ := hL
  obtain ⟨v, hv₁, hv₂⟩ := hN
  refine ⟨fun p c => mulUnit (u p.1 c) (v p.2 c), ?_, ?_⟩
  · rintro ⟨i, i'⟩ ⟨j, j'⟩ c
    exact frame_mulUnit _ _ _ _ _ _ _ _ _ _ _ _ (hu₁ i j c) (hv₁ i' j' c) _ _ _ _ _
  · rintro ⟨i, i'⟩ c c'
    exact mono_mulUnit a b _ _ _ _ _ _ _ _ _ _ (hu₂ i c c') (hv₂ i' c c') _ _ _

theorem hasFrame_dual {L : LB (MP ℤ m n)} {a : Fin (m + 1) → ℤ} (hL : HasFrame L a) :
    HasFrame (GlobalTheory.CechPic.dual L) (-a) := by
  obtain ⟨u, h1, h2⟩ := hL
  refine ⟨fun i c => (u i c)⁻¹, ?_, ?_⟩
  · intro i j c
    have e := h1 i j c
    change Semi.res _ (u j c)⁻¹ = Semi.res _ (L.g i j)⁻¹ * Semi.res _ (u i c)⁻¹
    rw [map_inv, map_inv, map_inv]
    exact (congrArg (·⁻¹) e).trans (mul_inv _ _)
  · intro i c c'
    have e := h2 i c c'
    change Semi.res _ (u i c)⁻¹ = Semi.res _ (u i c')⁻¹ * ∏ k, blockUnit (c k) (c' k) _ ^ (-a k)
    simp only [zpow_neg, Finset.prod_inv_distrib, map_inv]
    exact (congrArg (·⁻¹) e).trans (mul_inv _ _)

theorem hasFrame_triv : HasFrame (LB.triv (MP ℤ m n)) 0 := by
  refine ⟨fun _ _ => 1, ?_, ?_⟩
  · intro i j c
    simp only [map_one, mul_one]
  · intro i c c'
    simp

theorem res_pullO_g (k : Fin (m + 1)) (i j : Bk n k) {V : (MP ℤ m n).Opens}
    (h : V ≤ (pullO (prB n k) 1).U i ⊓ (pullO (prB n k) 1).U j) :
    Semi.res h ((pullO (prB n k) 1).g i j) = blockUnit i j h := by
  refine Units.ext ((val_res_pullO_g (prB n k) 1 i j h).trans ?_)
  rw [pow_one]
  exact (GlobalTheory.CompanionTheory.MPDict.Inhab.val_blockUnit i j h).symm

theorem hasFrame_pullO (k : Fin (m + 1)) : HasFrame (pullO (prB n k) 1) (Pi.single k 1) := by
  refine ⟨fun i c => blockUnit (c k) i (le_inf (inf_le_right.trans (mchart_le c k)) inf_le_left), ?_, ?_⟩
  · intro i j c
    refine (GlobalTheory.CompanionTheory.MPDict.res_blockUnit _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (res_pullO_g k i j _) (GlobalTheory.CompanionTheory.MPDict.res_blockUnit _ _ _ _)).symm)
    rw [mul_comm]
    exact (GlobalTheory.CompanionTheory.MPDict.Inhab.blockUnit_mul _ _ _ _ _ _).symm
  · intro i c c'
    refine (GlobalTheory.CompanionTheory.MPDict.res_blockUnit _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (GlobalTheory.CompanionTheory.MPDict.res_blockUnit _ _ _ _)
        (GlobalTheory.CompanionTheory.MPDict.Inhab.prod_blockUnit_single k c c' _)).symm)
    rw [mul_comm]
    exact (GlobalTheory.CompanionTheory.MPDict.Inhab.blockUnit_mul _ _ _ _ _ _).symm

theorem exists_hasFrame_cls (a : Fin (m + 1) → ℤ) : ∃ (L : LB (MP ℤ m n)) (hL : L.IsLB), HasFrame L a ∧
    cls L hL = ∑ k, a k • cls (pullO (prB n k) 1) (isLB_pullO _ 1) := by
  classical
  let H : AddSubgroup (Fin (m + 1) → ℤ) :=
    { carrier := {a | ∃ (L : LB (MP ℤ m n)) (hL : L.IsLB), HasFrame L a ∧
        cls L hL = ∑ k, a k • cls (pullO (prB n k) 1) (isLB_pullO _ 1)}
      add_mem' := by
        rintro a b ⟨L, hL, fL, eL⟩ ⟨N, hN, fN, eN⟩
        refine ⟨_, isLB_tens hL hN, hasFrame_tens fL fN, ?_⟩
        rw [cls_tens hL hN, eL, eN, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => (add_smul _ _ _).symm
      zero_mem' := ⟨_, LB.isLB_triv _, hasFrame_triv, by simp; rfl⟩
      neg_mem' := by
        rintro a ⟨L, hL, fL, eL⟩
        refine ⟨_, isLB_dual hL, hasFrame_dual fL, ?_⟩
        rw [cls_dual hL, eL, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun k _ => (neg_smul _ _).symm }
  have hs (k : Fin (m + 1)) : (Pi.single k 1 : Fin (m + 1) → ℤ) ∈ H := by
    refine ⟨_, isLB_pullO _ 1, hasFrame_pullO k, ?_⟩
    rw [Finset.sum_eq_single k (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul]) (by simp),
      Pi.single_eq_same, one_smul]
  have e : a = ∑ k, a k • (Pi.single k 1 : Fin (m + 1) → ℤ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have : a ∈ H := e ▸ H.sum_mem fun k _ => H.zsmul_mem (hs k) _
  exact this

end GlobalTheory.CompanionTheory.MPDict.ClsRep

theorem GlobalTheory.CompanionTheory.MPDict.ClsRep.cls_eq_of_isHermRep : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)), IsHermRep M A → cls M.B M.isLB = ∑ k, A.a k • cls (pullO (prB n k) 1) (isLB_pullO _ 1) := by
  intro m n M A h
  obtain ⟨L, hL, fL, eL⟩ := GlobalTheory.CompanionTheory.MPDict.ClsRep.exists_hasFrame_cls (m := m) (n := n) A.a
  exact ((cls_eq_iff M.isLB hL).2 (GlobalTheory.CompanionTheory.MPDict.ClsRep.lbIso_of_hasFrame
    (GlobalTheory.CompanionTheory.MPDict.ClsRep.hasFrame_of_isHermRep h) fL)).trans eL
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepClassDecompositionStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermRep_class_decomposition : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)), IsHermRep M A → cls M.B M.isLB = ∑ k, A.a k • cls (pullO (prB n k) 1) (isLB_pullO _ 1) := by
  first | exact @GlobalTheory.CompanionTheory.MPDict.ClsRep.cls_eq_of_isHermRep | exact GlobalTheory.CompanionTheory.MPDict.ClsRep.cls_eq_of_isHermRep | (intros; apply GlobalTheory.CompanionTheory.MPDict.ClsRep.cls_eq_of_isHermRep <;> assumption)
end
end
end
