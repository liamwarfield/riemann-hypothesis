module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.IsDiscreteOfNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.FiniteTypes.FintypeHolds
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TraceUnique

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.WtExPf
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.wtEx_pf :
    WtEx := by
  intro E _ _ _ n π hreg
  have h : ∀ φ : E →+* ℂ, ∃ lam : DomWeight n, π.HasInfChar φ (infOfWeight lam) := fun φ => by
    have hm : π.HasInfChar φ ((CG.mk π).infChar φ) :=
      GlobalTheory.CuspRep.hasInfChar_infChar_of_commute E n (fun τ u o => GlobalTheory.SpehInfChar.cap_commute_act τ u o) (CG.mk π) φ
    obtain ⟨lam, hl⟩ := DiscreteGroups.T1.G.reg_of hreg hm
    exact ⟨lam, hl ▸ hm⟩
  choose lamE hlam using h
  exact ⟨lamE, hlam⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PPiAdm
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open NumberField GlobalTheory.CuspRep PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.Desc
open PositivityTheory.Rg.BcB.E.E3.fintype in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.piAdm_pf :
    PiAdm := by
  intro E _ _ _ n _ π _ K W hK hW
  have hs : ∀ (τ : E →+* ℂ) (z : ℂ), ∃ c : ℂ, ∀ φ ∈ π.V, cap τ z φ = c • φ := fun τ z =>
    π.exists_scalar (Algebra.subset_adjoin ⟨τ, z, rfl⟩) (by
      rintro (k | k | X)
      exacts [commute_cap_finRep τ z k, GlobalTheory.CapAdInv.cap_commute_rt_infGL E n τ z _, commute_cap_lie τ z X])
  choose c hc using hs
  haveI := wl_fin W
  haveI hF := PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E n K hK _ (sig W) (sig_cont W) c
  refine ⟨π.V ⊓ Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms K (sig W) c), inf_le_left,
    Submodule.finiteDimensional_inf_right _ _, fun ψ hψ ht => ⟨hψ, Submodule.subset_span
      ⟨(π.cusp ψ hψ).1, fun k hk => Subtype.ext (funext fun g => ht.1 k hk g),
        coeff_mem W ψ ht.2, fun τ z => hc τ z ψ hψ⟩⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.YLocPf
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.yLoc_pf :
    PfHecke → ProdOp → YLoc := by
  intro hP hO E _ _ _ n S Z N hS hZ hG π y i hi f hf x hx
  classical
  obtain ⟨w, b⟩ := i
  let F : ∀ w', Bool → _ := fun w' b' =>
    if h : w' = w ∧ b' = b then h.1 ▸ f else ((N w' : Set _).indicator 1)
  have hFi : F w b = f := by simp [F]
  have hFam : Fam S N {(w, b)} F := by
    refine ⟨?_, ?_⟩
    · intro j hj
      obtain rfl := Finset.mem_singleton.mp hj
      exact ⟨hi, by simpa [hFi] using hf⟩
    · rintro ⟨w', b'⟩ _ hj
      have hne : ¬ (w' = w ∧ b' = b) := by
        rintro ⟨rfl, rfl⟩
        exact hj (Finset.mem_singleton_self _)
      simp [F, hne]
  have h1 := hO E n S Z N hS hZ hG {(w, b)} F hFam x (y.fix hx)
  have h2 := y.act _ (hP E n S Z N hS hZ hG {(w, b)} F hFam) ⟨x, hx⟩
  have h3 : Lw N w b f x = ((y.r (pf S F) ⟨x, hx⟩ : y.Y) : _) := by
    rw [h2]
    show _ = Lv _ _ _ x
    rw [h1]
    simp [hFi]
  show Lw N w b f x ∈ y.Y
  rw [h3]
  exact (y.r (pf S F) ⟨x, hx⟩).2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PTraceForm
namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem traceForm_pf : TraceForm := by
  intro J M Y _ _ _ _ _ _ α a C hs hk hc p
  have surj : Function.Surjective (FreeAlgebra.lift ℂ α) :=
    DiscreteGroups.T1.Desc.Swap3.burnside (FreeAlgebra.lift ℂ α) fun W hW => hs W fun f x hx => by
      simpa using hW (FreeAlgebra.ι ℂ f) x hx

  let lam : FreeAlgebra ℂ J →ₗ[ℂ] ℂ :=
    LinearMap.trace ℂ Y ∘ₗ LinearMap.mulRight ℂ C ∘ₗ (FreeAlgebra.lift ℂ a).toLinearMap
  have lam_apply : ∀ r, lam r = LinearMap.trace ℂ Y (FreeAlgebra.lift ℂ a r * C) := fun _ => rfl
  obtain ⟨s, hs'⟩ := LinearMap.exists_rightInverse_of_surjective
    (FreeAlgebra.lift ℂ α).toLinearMap (LinearMap.range_eq_top.2 surj)
  have sec : ∀ T, FreeAlgebra.lift ℂ α (s T) = T := fun T => LinearMap.congr_fun hs' T

  have same : ∀ r r', FreeAlgebra.lift ℂ α r = FreeAlgebra.lift ℂ α r' → lam r = lam r' := by
    intro r r' h
    have h0 : FreeAlgebra.lift ℂ a (r - r') = 0 := hk _ (by rw [map_sub, h, sub_self])
    have h1 : lam (r - r') = 0 := by rw [lam_apply, h0, zero_mul, map_zero]
    rw [map_sub] at h1
    exact sub_eq_zero.1 h1
  let g : Module.End ℂ M →ₗ[ℂ] ℂ := lam ∘ₗ s
  have g_apply : ∀ r, g (FreeAlgebra.lift ℂ α r) = lam r := fun r => same _ _ (sec _)
  obtain ⟨c, hc'⟩ := DiscreteGroups.T1.Desc.Swap3.trace_unique g (by
    intro x y
    obtain ⟨r, rfl⟩ := surj x
    obtain ⟨r', rfl⟩ := surj y
    rw [← map_mul, ← map_mul, g_apply, g_apply, lam_apply, lam_apply,
      map_mul (FreeAlgebra.lift ℂ a), map_mul (FreeAlgebra.lift ℂ a)]
    exact hc r r')
  have hp : lam p = c * LinearMap.trace ℂ M (FreeAlgebra.lift ℂ α p) := by
    rw [← g_apply, hc']
  have h1 : LinearMap.trace ℂ Y C = c * (Module.finrank ℂ M : ℂ) := by
    have := g_apply 1
    rw [hc', map_one (FreeAlgebra.lift ℂ α), LinearMap.trace_one, lam_apply, map_one (FreeAlgebra.lift ℂ a), one_mul] at this
    exact this.symm
  rw [← lam_apply, hp, h1]
  ring

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PLocComm
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open GlobalTheory.BCT GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host Formalism.UG Formalism.BasicNotions

private theorem lv_commute {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (H : Subgroup G) (hH : IsOpen (H : Set G)) (f : G → ℂ)
    (hf : HasCompactSupport f) (T : Module.End ℂ V) (hT : ∀ a, Commute T (ρ a)) : Commute T (Lv ρ H f) := by
  have hs := GlobalTheory.TwTrLevel.finite_supp H hH f hf
  have hsupp : (Function.support fun q : G ⧸ H =>
      f q.out • (ρ q.out ∘ₗ (LinearMap.id : V →ₗ[ℂ] V))).Finite :=
    hs.subset fun q hq h0 => hq (by simp [h0])
  unfold UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.Lv levOp
  rw [finsum_eq_sum_of_support_subset _ (s := hsupp.toFinset) (by simp)]
  refine Commute.smul_right (Commute.sum_right _ _ _ fun q _ => Commute.smul_right ?_ _) _
  rw [LinearMap.comp_id]
  exact hT _

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.locComm_pf :
    SlotBasic → LevTop → LocComm := by
  intro hSF _ E _ _ _ n S Z N hSec _ hG i hi f hf
  obtain ⟨-, -, hloc, hind, -⟩ := hSF E n S hSec
  have hmem : ∀ c, c ∈ Lev S N ↔ ∀ k, Sl S k → qw n k.1 k.2 c ∈ N k.1 := by
    intro c
    simp only [Lev, Subgroup.mem_iInf, Subgroup.mem_comap, Subtype.forall]
  have hjw : ∀ a ∈ N i.1, jw n i.1 i.2 a ∈ Lev S N := by
    intro a ha
    refine (hmem _).2 fun k hk => ?_
    by_cases h : i = k
    · subst h
      rw [(hloc i.1 i.2).2.2.1]
      exact ha
    · rw [hind i k hi hk h a]
      exact one_mem _
  have hopen := (hG i.1).1
  refine ⟨fun y hy => ?_, fun k hk hik g hg => ?_⟩
  · have hy' := (GlobalTheory.TwTrLevel.mem_fixed_iff _ _ y).1 hy
    have h1 : y ∈ fixed (rw' n i.1 i.2) (N i.1) :=
      (GlobalTheory.TwTrLevel.mem_fixed_iff _ _ y).2 fun a ha => hy' _ (hjw a ha)
    refine ⟨h1, (GlobalTheory.TwTrLevel.mem_fixed_iff _ _ _).2 fun c hc => ?_⟩
    have ha : qw n i.1 i.2 c ∈ N i.1 := (hmem c).1 hc i hi
    obtain ⟨c', hcc⟩ : ∃ c', c' = (jw n i.1 i.2 (qw n i.1 i.2 c))⁻¹ * c := ⟨_, rfl⟩
    have hc' : c' ∈ Lev S N := hcc ▸ mul_mem (inv_mem (hjw _ ha)) hc
    have hq : qw n i.1 i.2 c' = 1 := by
      rw [hcc, map_mul, map_inv, (hloc i.1 i.2).2.2.1, inv_mul_cancel]
    have hc2 : c = jw n i.1 i.2 (qw n i.1 i.2 c) * c' := by
      rw [hcc, mul_inv_cancel_left]
    have hL : Commute (finRep E n c') (Lw N i.1 i.2 f) :=
      lv_commute (rw' n i.1 i.2) (N i.1) hopen f hf.1 _ fun a =>
        (((hloc i.1 i.2).2.2.2 a c' hq).map (finRep E n)).symm
    have hfix : Lw N i.1 i.2 f y ∈ fixed (rw' n i.1 i.2) (N i.1) :=
      GlobalTheory.TwTrLevel.levOp_mem_fixed (rw' n i.1 i.2) (MonoidHom.id _) (fun _ => rfl) LinearMap.id
        (fun _ => rfl) (N i.1) (N i.1) hopen (fun _ h => h) f hf y h1
    have e : finRep E n c' (Lw N i.1 i.2 f y) = Lw N i.1 i.2 f y := by
      have h2 := LinearMap.congr_fun hL.eq y
      rw [Module.End.mul_apply, Module.End.mul_apply, hy' c' hc'] at h2
      exact h2
    have h3 := (GlobalTheory.TwTrLevel.mem_fixed_iff _ _ _).1 hfix _ ha
    rw [hc2, map_mul, Module.End.mul_apply, e]
    exact h3
  · have hrr : ∀ a b, Commute (rw' n i.1 i.2 a) (rw' n k.1 k.2 b) := fun a b =>
      (((hloc k.1 k.2).2.2.2 b (jw n i.1 i.2 a) (hind i k hi hk hik a)).map (finRep E n)).symm
    exact lv_commute (rw' n k.1 k.2) (N k.1) (hG k.1).1 g hg.1 _ fun b =>
      (lv_commute (rw' n i.1 i.2) (N i.1) hopen f hf.1 _ fun a => (hrr a b).symm).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PLevTop
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.levTop_pf :
    SlotBasic → LevTop := by
  intro hS E _ _ _ n S Z N hSec hZ hG
  obtain ⟨hinv, -, hloc, -, -, hinert, hK⟩ := hS E n S hSec
  have mem : ∀ (M : ∀ w : GlobalTheory.BCT.Pl E, Subgroup (GlobalTheory.BCT.GLw n w)) (x : GF E n),
      x ∈ Lev S M ↔ ∀ i : GlobalTheory.BCT.Pl E × Bool, Sl S i → qw n i.1 i.2 x ∈ M i.1 := by
    intro M x
    simp only [Lev, Subgroup.mem_iInf, Subgroup.mem_comap, Subtype.forall]
  have hKq : ∀ k ∈ PositivityTheory.Rg.BcB.G8.Kf E n, ∀ i : GlobalTheory.BCT.Pl E × Bool, Sl S i →
      qw n i.1 i.2 k ∈ GlobalTheory.LFun.KGL i.1 (n := n) := fun k hk => (mem _ k).1 ((hK k).2 hk)
  have hsub : (Lev S N : Set (GF E n)) ⊆ (PositivityTheory.Rg.BcB.G8.Kf E n : Set (GF E n)) := by
    intro x hx
    exact (hK x).1 ((mem _ x).2 fun i hi => (hG i.1).2.1 ((mem N x).1 hx i hi))
  have hset : (Lev S N : Set (GF E n)) = (PositivityTheory.Rg.BcB.G8.Kf E n : Set (GF E n)) ∩
      ⋂ i ∈ {i : GlobalTheory.BCT.Pl E × Bool | i.1 ∈ Z ∧ Sl S i},
        (qw n i.1 i.2) ⁻¹' (N i.1 : Set (GlobalTheory.BCT.GLw n i.1)) := by
    ext x
    constructor
    · intro hx
      refine ⟨hsub hx, ?_⟩
      simp only [Set.mem_iInter]
      exact fun i hi => (mem N x).1 hx i hi.2
    · rintro ⟨hx, hx'⟩
      simp only [Set.mem_iInter] at hx'
      refine (mem N x).2 fun i hi => ?_
      by_cases hz : i.1 ∈ Z
      · exact hx' i ⟨hz, hi⟩
      · rw [(hG i.1).2.2.2 hz]
        exact hKq x hx i hi
  have hfinZ : {i : GlobalTheory.BCT.Pl E × Bool | i.1 ∈ Z ∧ Sl S i}.Finite :=
    ((Z.finite_toSet).prod (Set.finite_univ (α := Bool))).subset fun i hi => ⟨hi.1, trivial⟩
  have hopen : IsOpen (Lev S N : Set (GF E n)) := by
    rw [hset]
    refine GlobalTheory.CompanionTheory.EulerV.isOpen_Kf.inter (hfinZ.isOpen_biInter fun i _ => ?_)
    exact ((hG i.1).1).preimage (hloc i.1 i.2).2.1
  refine ⟨hopen, ?_, ?_, ?_⟩
  · exact GlobalTheory.CompanionTheory.EulerV.isCompact_Kf.of_isClosed_subset
      (Subgroup.isClosed_of_isOpen (Lev S N) hopen) hsub
  · intro k hk
    have hq0 : ∀ w, qw n w false (GlobalTheory.BCT.thF E n k) = qw n w true k := fun w => rfl
    have hq1 : ∀ w, qw n w true (GlobalTheory.BCT.thF E n k) = qw n w false k := by
      intro w
      change qw n w false (GlobalTheory.BCT.thF E n (GlobalTheory.BCT.thF E n k)) = _
      rw [hinv]
    refine (mem N _).2 ?_
    rintro ⟨w, b⟩ ⟨hw, hb⟩
    cases b with
    | true =>
      exact (hq1 w).symm ▸ (mem N k).1 hk (w, false) ⟨hw, by simp⟩
    | false =>
      change qw n w false (GlobalTheory.BCT.thF E n k) ∈ N w
      rw [hq0]
      by_cases hs : GlobalTheory.UnitaryBC.IsSplitAt w
      · exact (mem N k).1 hk (w, true) ⟨hw, fun _ => hs⟩
      · have hz : w ∉ Z := fun h => hs (hZ w h).2
        have h0 : qw n w false k ∈ N w := (mem N k).1 hk (w, false) ⟨hw, by simp⟩
        rw [(hG w).2.2.2 hz] at h0 ⊢
        exact (hinert w hs k).2 h0
  · intro k hk x hx
    refine (mem N _).2 fun i hi => ?_
    rw [map_mul, map_mul, map_inv]
    exact (hG i.1).2.2.1 _ (hKq k hk i hi) _ ((mem N x).1 hx i hi)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.POrthZero
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.OZ

private def bump (s : ℝ) : ℂ := ((max 0 (min 1 (2 - |s|)) : ℝ) : ℂ)

private theorem bump_cont : Continuous bump := by
  unfold bump
  fun_prop

private theorem bump_supp : HasCompactSupport bump := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (-2 : ℝ)) (b := 2)) fun s hs => ?_
  have h : 2 < |s| := by
    by_contra hc
    exact hs (abs_le.1 (not_lt.1 hc))
  have h1 : min 1 (2 - |s|) ≤ 0 := (min_le_right _ _).trans (by linarith)
  simp [bump, max_eq_left h1]

private theorem bump_one {s : ℝ} (h : s ∈ Set.Ioo (-1 : ℝ) 1) : bump s = 1 := by
  have h1 : |s| < 1 := abs_lt.2 h
  have h2 : min 1 (2 - |s|) = 1 := min_eq_left (by linarith)
  simp [bump, h2]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.OZ

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.OZ in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.orthZero_pf :
    Basic → AeEq → WtInd → OrthZero := by
  intro hB hA _ E _ _ _ n hn D π _ f hf hS ho
  obtain ⟨hl, hmul, -⟩ := hB E n hn
  obtain ⟨hfc, hfr, hfs, -⟩ := hf
  obtain ⟨v, hv, hve⟩ := hS bump bump_cont bump_supp
  have horth : v ∈ (piSp D π Unit)ᗮ := by
    rw [piSp, Submodule.orthogonal_closure, Submodule.mem_orthogonal]
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨ψ, hψ, u, hu, hus, he⟩ := hg ()
      have hz := ho ψ hψ (fun s => starRingEnd ℂ (u s) * bump s)
        ((Complex.continuous_conj.comp hu).mul bump_cont)
        ((hus.comp_left (g := starRingEnd ℂ) (map_zero _)).mul_right)
      rw [PiLp.inner_apply]
      simp only [Finset.univ_unique, Finset.sum_singleton]
      rw [L2.inner_def]
      rw [← hz, prW]
      refine integral_congr_ae ?_
      filter_upwards [he, hve] with x h1 h2
      simp only [PUnit.default_eq_unit]
      rw [h1, h2]
      simp only [RCLike.inner_apply, map_mul]
      ring
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul r x _ hx => rw [inner_smul_left, hx, mul_zero]
  have hv0 : v = 0 := inner_self_eq_zero.1
    ((Submodule.mem_orthogonal _ _).1 horth v hv)
  have hlat : ∀ x : H E n 0, ldet x ∈ Set.Ioo (-1 : ℝ) 1 → f x.1 = 0 := by
    refine hA E n D (fun x => f x.1) (fun _ => 0) (Set.Ioo (-1 : ℝ) 1) (hfc.comp continuous_fst)
      continuous_const ?_ (fun _ _ => rfl) isOpen_Ioo ?_
    · intro γ x
      obtain ⟨⟨a, b⟩, hab⟩ := γ.2
      have h1 : (γ : H E n 0).1 = ratGL E n a := by rw [← hab]; rfl
      show f ((γ : H E n 0).1 * x.1) = f x.1
      rw [h1, hfr]
    · have hz : ((v () : Lp ℂ 2 D.ν) : H E n 0 → ℂ) =ᵐ[D.ν] 0 := by
        rw [hv0]
        exact Lp.coeFn_zero _ _ _
      filter_upwards [hve, hz] with x h1 h2 h3
      rw [h2] at h1
      simpa [bump_one h3] using h1.symm
  funext g
  have hx := hlat (ac E n (-ldet ((g, 1) : H E n 0)) * (g, 1)) (by
    rw [hmul, hl]; simp)
  have : (ac E n (-ldet ((g, 1) : H E n 0)) * (g, 1) : H E n 0).1 =
      splitCentre E n (-ldet ((g, 1) : H E n 0) / (n * Module.finrank ℚ E)) * g := rfl
  rw [this, hfs] at hx
  exact hx
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PLcLevel
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

private theorem exists_core {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K M : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hMo : IsOpen (M : Set G)) (hMK : M ≤ K) :
    ∃ C : Subgroup G, IsOpen (C : Set G) ∧ C ≤ M ∧ ∀ k ∈ K, ∀ x ∈ C, k * x * k⁻¹ ∈ C := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  set M' : Subgroup K := M.subgroupOf K with hM'
  have hM'o : IsOpen (M' : Set K) := hMo.preimage continuous_subtype_val
  haveI : Finite (K ⧸ M') := Subgroup.quotient_finite_of_isOpen M' hM'o
  haveI : M'.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hcl : IsClosed (M'.normalCore : Set K) := by
    have hc : IsClosed (M' : Set K) := Subgroup.isClosed_of_isOpen M' hM'o
    have : (M'.normalCore : Set K) = ⋂ b : K, (fun a : K => b * a * b⁻¹) ⁻¹' (M' : Set K) := by
      ext a
      simp [Subgroup.normalCore, Set.mem_iInter]
    rw [this]
    exact isClosed_iInter fun b => hc.preimage (by fun_prop)
  have hop : IsOpen (M'.normalCore : Set K) := Subgroup.isOpen_of_isClosed_of_finiteIndex _ hcl
  refine ⟨M'.normalCore.map K.subtype, ?_, ?_, ?_⟩
  · have : ((M'.normalCore.map K.subtype : Subgroup G) : Set G) = Subtype.val '' (M'.normalCore : Set K) := by
      ext x; simp
    rw [this]
    exact hKo.isOpenMap_subtype_val _ hop
  · rintro _ ⟨a, ha, rfl⟩
    have h1 : a ∈ M' := Subgroup.normalCore_le M' ha
    exact h1
  · rintro k hk _ ⟨a, ha, rfl⟩
    refine ⟨⟨k, hk⟩ * a * (⟨k, hk⟩ : K)⁻¹, ?_, by simp⟩
    exact (Subgroup.normalCore_normal M').conj_mem a ha _

private theorem hecke_slice {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Pl E)
    (K' : Subgroup (GLw n w × GLw 0 w)) (f : GLw n w × GLw 0 w → ℂ) (hf : IsHecke K' f)
    (N : Subgroup (GLw n w)) (hN : ∀ k ∈ N, ((k, 1) : GLw n w × GLw 0 w) ∈ K') :
    IsHecke N (fun g => f (g, 1)) := by
  refine ⟨?_, fun k hk x => ?_⟩
  · haveI : Unique (GLw 0 w) := Unique.mk' _
    have e : (fun g : GLw n w => ((g, 1) : GLw n w × GLw 0 w)) =
        ⇑(Homeomorph.prodUnique (GLw n w) (GLw 0 w)).symm := by
      funext g
      exact Prod.ext rfl (Subsingleton.elim _ _)
    have h : Topology.IsClosedEmbedding (fun g : GLw n w => ((g, 1) : GLw n w × GLw 0 w)) := by
      rw [e]
      exact (Homeomorph.prodUnique (GLw n w) (GLw 0 w)).symm.isClosedEmbedding
    exact hf.1.comp_isClosedEmbedding h
  · have h := hf.2 _ (hN k hk) (x, 1)
    simpa using h

theorem lcLevel_pf : LcLevel := by
  classical
  intro E _ _ _ n Z N₀ hN₀ φ₁ φ₂ hφ
  have hK := fun w : Pl E => GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have key : ∀ w ∈ Z, ∃ C : Subgroup (GLw n w), IsOpen (C : Set (GLw n w)) ∧ C ≤ N₀ w ∧
      (∀ k ∈ KGL w (n := n), ∀ x ∈ C, k * x * k⁻¹ ∈ C) ∧ ∀ b, IsHecke C (two φ₁ φ₂ w b) := by
    intro w hw
    obtain ⟨⟨A, hAo, -, hA⟩, ⟨B, hBo, -, hB⟩⟩ := hφ w hw
    let ι : GLw n w →* GLw n w × GLw 0 w := MonoidHom.inl _ _
    have hι : Continuous ι := continuous_id.prodMk continuous_const
    have hMo : IsOpen ((N₀ w ⊓ A.comap ι ⊓ B.comap ι : Subgroup (GLw n w)) : Set (GLw n w)) :=
      ((hN₀ w).1.inter (hAo.preimage hι)).inter (hBo.preimage hι)
    obtain ⟨C, hCo, hCM, hCn⟩ := exists_core (KGL w (n := n)) (N₀ w ⊓ A.comap ι ⊓ B.comap ι) (hK w).1 (hK w).2
      hMo (fun x hx => (hN₀ w).2.1 hx.1.1)
    refine ⟨C, hCo, fun x hx => (hCM hx).1.1, hCn, ?_⟩
    rintro (_ | _)
    · exact hecke_slice w A (φ₁ w) hA C fun k hk => (hCM hk).1.2
    · exact hecke_slice w B (φ₂ w) hB C fun k hk => (hCM hk).2
  choose! C hC using key
  refine ⟨fun w => if w ∈ Z then C w else N₀ w, ?_, ?_, ?_⟩
  · intro w
    by_cases hw : w ∈ Z
    · simp only [if_pos hw]
      obtain ⟨a, b, c, -⟩ := hC w hw
      exact ⟨a, b.trans (hN₀ w).2.1, c, fun h => absurd hw h⟩
    · simp only [if_neg hw]
      exact hN₀ w
  · intro w
    by_cases hw : w ∈ Z
    · simp only [if_pos hw]
      exact (hC w hw).2.1
    · simp only [if_neg hw]
      exact le_rfl
  · intro w hw b
    simp only [if_pos hw]
    exact (hC w hw).2.2.2 b

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PHeckeSum
noncomputable section

open MeasureTheory Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.BCT PositivityTheory.Rg.BcB
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section Abs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

private theorem coset_integral (μ : Measure G) [μ.IsMulLeftInvariant] {K : Subgroup G} (hK : IsOpen (K : Set G))
    (hfin : μ (K : Set G) ≠ ⊤) {h : G → ℂ} (hc : HasCompactSupport h) (hinv : ∀ g, ∀ k ∈ K, h (g * k) = h g) :
    ∃ T : Finset (G ⧸ K), (∀ q : G ⧸ K, h q.out ≠ 0 → q ∈ T) ∧ ∀ f : G → ℂ, (∀ g, ∀ k ∈ K, f (g * k) = f g) →
      ∫ y, h y * f y ∂μ = ∑ q ∈ T, (μ.real (K : Set G) : ℂ) * (h q.out * f q.out) := by
  let c : G ⧸ K → Set G := fun q => {y | q.out⁻¹ * y ∈ K}
  have hcm : ∀ q y, y ∈ c q ↔ (QuotientGroup.mk y : G ⧸ K) = q := by
    intro q y
    change q.out⁻¹ * y ∈ K ↔ _
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    exact eq_comm
  have hco : ∀ q, IsOpen (c q) := fun q => hK.preimage (continuous_const.mul continuous_id)
  have hmeas : ∀ q, μ (c q) = μ (K : Set G) := fun q => measure_preimage_mul μ q.out⁻¹ (K : Set G)
  obtain ⟨t, -, ht⟩ := hc.isCompact.elim_nhds_subcover (fun g => c (QuotientGroup.mk g))
    (fun g _ => (hco _).mem_nhds ((hcm _ g).2 rfl))
  let T : Finset (G ⧸ K) := t.image fun g => (QuotientGroup.mk g : G ⧸ K)
  have hT : ∀ y, h y ≠ 0 → (QuotientGroup.mk y : G ⧸ K) ∈ T := by
    intro y hy
    obtain ⟨g, hg, hyg⟩ := Set.mem_iUnion₂.1 (ht (subset_tsupport h hy))
    rw [(hcm _ y).1 hyg]
    exact Finset.mem_image_of_mem _ hg
  refine ⟨T, fun q hq => ?_, fun f hf => ?_⟩
  · simpa [QuotientGroup.out_eq'] using hT _ hq
  have hval : ∀ q y, y ∈ c q → h y * f y = h q.out * f q.out := by
    intro q y hy
    have e : y = q.out * (q.out⁻¹ * y) := by group
    rw [e, hinv _ _ hy, hf _ _ hy]
  have hsum : (fun y => h y * f y) = fun y => ∑ q ∈ T, (c q).indicator (fun _ => h q.out * f q.out) y := by
    funext y
    by_cases hy : (QuotientGroup.mk y : G ⧸ K) ∈ T
    · have hyc : y ∈ c (QuotientGroup.mk y) := (hcm _ y).2 rfl
      rw [Finset.sum_eq_single (QuotientGroup.mk y : G ⧸ K), Set.indicator_of_mem hyc, hval _ y hyc]
      · intro q _ hq
        exact Set.indicator_of_notMem (fun hyq => hq ((hcm q y).1 hyq).symm) _
      · exact fun h' => (h' hy).elim
    · have hy0 : h y = 0 := by
        by_contra h'
        exact hy (hT y h')
      rw [hy0, zero_mul]
      refine (Finset.sum_eq_zero fun q hq => Set.indicator_of_notMem (fun hyq => hy ?_) _).symm
      rwa [(hcm q y).1 hyq]
  rw [hsum, integral_finsetSum]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_indicator_const _ (hco q).measurableSet]
    simp only [Measure.real, hmeas q, Complex.real_smul]
  · intro q _
    refine (integrable_indicator_iff (hco q).measurableSet).2 ?_
    exact integrableOn_const (by rw [hmeas q]; exact hfin)

end Abs

theorem heckeSum_pf : HeckeSum := by
  intro E _ _ _ n K hKo hKc μf _ h hh y hy
  have hfix : ∀ k ∈ K, finRep E n k y = y := fun k hk => by
    simpa using hy ⟨k, hk⟩
  obtain ⟨T, hT, hI⟩ := coset_integral μf hKo hKc.measure_lt_top.ne hh.1 (fun g k hk => (hh.2 k hk g).2)
  funext x
  have hf := hI (fun g => y.1 (x * finGL E n g)) (fun g k hk => by
    have e := congrArg (fun φ : Sm E n => φ.1 (x * finGL E n g)) (hfix k hk)
    have e' : y.1 (x * finGL E n g * finGL E n k) = y.1 (x * finGL E n g) := e
    simpa [mul_assoc] using e')
  have hL : Lv (finRep E n) K h = ∑ q ∈ T, h q.out • finRep E n q.out := by
    have hs : (Function.support fun q : GF E n ⧸ K => h q.out • (finRep E n q.out ∘ₗ LinearMap.id)) ⊆ T := by
      intro q hq
      refine hT q fun h0 => hq ?_
      simp [h0]
    simp only [Lv, levOp, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul]
    rw [finsum_eq_sum_of_support_subset _ hs]
    rfl
  have hv : (∑ q ∈ T, (h q.out • finRep E n q.out) y : Sm E n).1 x =
      ∑ q ∈ T, h q.out * y.1 (x * finGL E n q.out) := by
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  rw [hL, heckeOp, hf, LinearMap.sum_apply, hv, Finset.mul_sum]
  rfl

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PYSwap
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.G8

open scoped Classical

noncomputable section

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private def sing (N : ∀ w : Pl E, Subgroup (GLw n w)) (w : Pl E) (f : GLw n w → ℂ) (b₀ : Bool) :
    ∀ v : Pl E, Bool → GLw n v → ℂ :=
  Function.update (fun v _ => (N v : Set (GLw n v)).indicator 1) w
    (fun b => if b = b₀ then f else (N w : Set (GLw n w)).indicator 1)

private theorem sing_self (N : ∀ w : Pl E, Subgroup (GLw n w)) (w : Pl E) (f : GLw n w → ℂ) (b₀ : Bool) :
    sing N w f b₀ w b₀ = f := by
  simp [sing]

private theorem sing_ne (N : ∀ w : Pl E, Subgroup (GLw n w)) (w : Pl E) (f : GLw n w → ℂ) (b₀ : Bool)
    (v : Pl E) (b : Bool) (h : (v, b) ≠ (w, b₀)) :
    sing N w f b₀ v b = (N v : Set (GLw n v)).indicator 1 := by
  by_cases hv : v = w
  · subst hv
    have hb : b ≠ b₀ := fun e => h (by rw [e])
    simp [sing, hb]
  · simp [sing, Function.update_of_ne hv]

private theorem sing_fam (S : Set (Pl E)) (N : ∀ w : Pl E, Subgroup (GLw n w)) (w : Pl E) (f : GLw n w → ℂ)
    (b₀ : Bool) (hs : Sl S (w, b₀)) (hf : IsHecke (N w) f) :
    Fam S N {(w, b₀)} (sing N w f b₀) := by
  refine ⟨fun i hi => ?_, fun i _ hi => ?_⟩
  · rw [Finset.mem_singleton] at hi
    subst hi
    exact ⟨hs, by rw [sing_self]; exact hf⟩
  · exact sing_ne N w f b₀ i.1 i.2 (by simpa using hi)

private theorem sing_cross (N : ∀ w : Pl E, Subgroup (GLw n w)) (w : Pl E) (f : GLw n w → ℂ) (v : Pl E) :
    sing N w f false v true = sing N w f true v false := by
  rw [sing_ne N w f false v true (by simp), sing_ne N w f true v false (by simp)]

private theorem sing_diag (N : ∀ w : Pl E, Subgroup (GLw n w)) (w : Pl E) (f : GLw n w → ℂ) (v : Pl E) :
    sing N w f false v false = sing N w f true v true := by
  by_cases hv : v = w
  · subst hv
    rw [sing_self, sing_self]
  · rw [sing_ne N w f false v false (by simp [hv]), sing_ne N w f true v true (by simp [hv])]

private theorem pf_sing_twist (S : Set (Pl E)) (N : ∀ w : Pl E, Subgroup (GLw n w)) (w : Pl E)
    (f : GLw n w → ℂ) (hw : IsSplitAt w) (hth : ∀ g, thF E n (thF E n g) = g)
    (hin : ∀ v : Pl E, ¬ IsSplitAt v → ∀ g, qw n v true g ∈ KGL v (n := n) ↔ qw n v false g ∈ KGL v (n := n))
    (hN : ∀ v : Pl E, ¬ IsSplitAt v → N v = KGL v (n := n)) (g : GF E n) :
    pf S (sing N w f false) (thF E n g) = pf S (sing N w f true) g := by
  unfold pf
  refine finprod_congr fun v => finprod_congr fun _ => ?_
  have q0 : qw n v false (thF E n g) = qw n v true g := rfl
  have q1 : qw n v true (thF E n g) = qw n v false g := by
    show GeneralLinearGroup.map (pLoc E v) (thF E n (thF E n g)) = _
    rw [hth]
    rfl
  rw [q0, q1]
  by_cases hs : IsSplitAt v
  · rw [if_pos hs, if_pos hs, sing_cross, sing_diag, mul_comm]
  · have hv : v ≠ w := fun e => hs (e ▸ hw)
    rw [if_neg hs, if_neg hs, mul_one, mul_one, sing_ne N w f false v false (by simp [hv]),
      sing_ne N w f true v false (by simp [hv]), hN v hs]
    have h := hin v hs g
    by_cases hm : qw n v false g ∈ KGL v (n := n)
    · rw [Set.indicator_of_mem (show qw n v true g ∈ (KGL v (n := n) : Set (GLw n v)) from h.2 hm),
        Set.indicator_of_mem (show qw n v false g ∈ (KGL v (n := n) : Set (GLw n v)) from hm)]
      rfl
    · rw [Set.indicator_of_notMem (show qw n v true g ∉ (KGL v (n := n) : Set (GLw n v)) from fun e => hm (h.1 e)),
        Set.indicator_of_notMem (show qw n v false g ∉ (KGL v (n := n) : Set (GLw n v)) from hm)]

end SlopeTestRemainingChoices

theorem ySwap_pf : SlotBasic → PfHecke → ProdOp → YSwap := by
  intro hSF hPH hPO E _ _ _ n S Z N hS hZ hG π y w hw f hf x x' hx
  obtain ⟨hth, -, -, -, -, hin, -⟩ := hSF E n S hS
  have hwS := hZ w hw
  have hN : ∀ v : Pl E, ¬ IsSplitAt v → N v = KGL v (n := n) :=
    fun v hv => (hG v).2.2.2 fun hvZ => hv (hZ v hvZ).2
  have F0 := sing_fam S N w f false ⟨hwS.1, by simp⟩ hf
  have F1 := sing_fam S N w f true ⟨hwS.1, fun _ => hwS.2⟩ hf
  have h0 := hPH E n S Z N hS hZ hG _ _ F0
  have h1 := hPH E n S Z N hS hZ hG _ _ F1
  have e : (fun g => pf S (sing N w f false) (thF E n g)) = pf S (sing N w f true) :=
    funext (pf_sing_twist S N w f hwS.2 hth hin hN)
  have t := y.tw _ h0
  rw [e] at t
  have a0 : y.r (pf S (sing N w f false)) x = x' := by
    apply Subtype.ext
    rw [y.act _ h0, hPO E n S Z N hS hZ hG _ _ F0 _ (y.fix x.2), hx]
    simp [sing_self]
  have t' := congrArg (fun T : Module.End ℂ y.Y => T x) t
  simp only [Module.End.mul_apply, a0] at t'
  rw [t', y.act _ h1, hPO E n S Z N hS hZ hG _ _ F1 _ (y.fix (y.A x).2)]
  simp [sing_self]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PAbsStep
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

private lemma lv_eq_sum {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K : Subgroup G) (u : G → ℂ) (S : Finset (G ⧸ K)) (hS : ∀ c : G ⧸ K, u c.out ≠ 0 → c ∈ S) :
    Lv ρ K u = ∑ c ∈ S, u c.out • ρ c.out := by
  have hs : Function.support (fun c : G ⧸ K => u c.out • (ρ c.out ∘ₗ LinearMap.id)) ⊆ (S : Set (G ⧸ K)) := by
    intro c hc
    refine Finset.mem_coe.2 (hS c fun h0 => hc ?_)
    simp [h0]
  simp only [Lv, GlobalTheory.BCT.levOp, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul]
  rw [finsum_eq_sum_of_support_subset _ hs]
  rfl

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.absStep_pf :
    AbsStep := by
  intro G A V _ _ _ _ ρ K N j q f h h₁ hqj hcomm hjN hqK hh hh₁N hK hfN hfs hh₁s y hy
  classical
  have hyk : ∀ k ∈ K, ρ k y = y := fun k hk => by
    have := hy ⟨k, hk⟩
    simpa using this

  have hx0 : ∀ g, q ((j (q g))⁻¹ * g) = 1 := fun g => by simp [hqj]
  have hright : ∀ g k, k ∈ K → h (g * k) = h g := by
    intro g k hk
    rw [hh (g * k), hh g]
    have e1 : f (q (g * k)) = f (q g) := by
      rw [map_mul]
      exact hfN _ (hqK k hk) _
    have c : Commute (j (q k)) ((j (q g))⁻¹ * g) := hcomm (q k) _ (hx0 g)
    have e2 : (j (q (g * k)))⁻¹ * (g * k) = ((j (q g))⁻¹ * g) * ((j (q k))⁻¹ * k) := by
      have c' : (j (q k))⁻¹ * ((j (q g))⁻¹ * g) = ((j (q g))⁻¹ * g) * (j (q k))⁻¹ := c.inv_left.eq
      rw [map_mul, map_mul, mul_inv_rev, ← mul_assoc ((j (q g))⁻¹ * g), ← c']
      simp only [mul_assoc]
    rw [e1, e2, (hK _ (K.mul_mem (K.inv_mem (hjN _ (hqK k hk))) hk) _).2]
  set S₁ : Finset (A ⧸ N) := hfs.toFinset with hS₁
  set S₂ : Finset (G ⧸ K) := hh₁s.toFinset with hS₂
  have m₁ : ∀ s, s ∈ S₁ ↔ f s.out ≠ 0 := fun s => by simp [hS₁]
  have m₂ : ∀ t, t ∈ S₂ ↔ h₁ t.out ≠ 0 := fun t => by simp [hS₂]
  let φ : (A ⧸ N) × (G ⧸ K) → G ⧸ K := fun p => ((j p.1.out * p.2.out : G) : G ⧸ K)
  have hterm : ∀ (s : A ⧸ N) (t : G ⧸ K), t ∈ S₂ → h (j s.out * t.out) = f s.out * h₁ t.out := by
    intro s t ht
    have hn : q t.out ∈ N := hh₁N _ ((m₂ t).1 ht)
    have e0 : q (j s.out * t.out) = s.out * q t.out := by rw [map_mul, hqj]
    have e1 : (j (q (j s.out * t.out)))⁻¹ * (j s.out * t.out) = (j (q t.out))⁻¹ * t.out := by
      rw [e0, map_mul, mul_inv_rev]
      group
    rw [hh, e1, e0, hfN _ hn, (hK _ (K.inv_mem (hjN _ hn)) _).1]
  have hinj : Set.InjOn φ (S₁ ×ˢ S₂ : Finset _) := by
    rintro ⟨s, t⟩ hp ⟨s', t'⟩ hp' e
    have ht : t ∈ S₂ := (Finset.mem_product.1 (Finset.mem_coe.1 hp)).2
    have ht' : t' ∈ S₂ := (Finset.mem_product.1 (Finset.mem_coe.1 hp')).2
    have hn : q t.out ∈ N := hh₁N _ ((m₂ t).1 ht)
    have hn' : q t'.out ∈ N := hh₁N _ ((m₂ t').1 ht')
    have hk : (j s.out * t.out)⁻¹ * (j s'.out * t'.out) ∈ K := QuotientGroup.eq.1 e
    have hq : (q t.out)⁻¹ * (s.out⁻¹ * s'.out) * q t'.out ∈ N := by
      have := hqK _ hk
      simpa [hqj, mul_assoc] using this
    have hs : s.out⁻¹ * s'.out ∈ N := by
      have := N.mul_mem (N.mul_mem hn hq) (N.inv_mem hn')
      simpa [mul_assoc] using this
    have es : s = s' := by
      rw [← QuotientGroup.out_eq' s, ← QuotientGroup.out_eq' s']
      exact QuotientGroup.eq.2 hs
    subst es
    have ht2 : t.out⁻¹ * t'.out ∈ K := by
      simpa [mul_assoc] using hk
    have et : t = t' := by
      rw [← QuotientGroup.out_eq' t, ← QuotientGroup.out_eq' t']
      exact QuotientGroup.eq.2 ht2
    rw [et]
  have hsupp : ∀ c : G ⧸ K, h c.out ≠ 0 → c ∈ (S₁ ×ˢ S₂).image φ := by
    intro c hc
    set g := c.out with hg
    set a := q g with ha
    set x := (j a)⁻¹ * g with hx
    rw [hh g] at hc
    have hfa : f a ≠ 0 := left_ne_zero_of_mul hc
    have hhx : h₁ x ≠ 0 := right_ne_zero_of_mul hc
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N a
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K x
    refine Finset.mem_image.2 ⟨((a : A ⧸ N), (x : G ⧸ K)), Finset.mem_product.2 ⟨?_, ?_⟩, ?_⟩
    · show ((a : A ⧸ N)) ∈ S₁
      rw [m₁, hn, hfN _ n.2]
      exact hfa
    · show ((x : G ⧸ K)) ∈ S₂
      rw [m₂, hk, (hK _ k.2 _).2]
      exact hhx
    · show ((j (a : A ⧸ N).out * (x : G ⧸ K).out : G) : G ⧸ K) = c
      have c1 : Commute (j (n : A)) x := hcomm _ _ (hx0 g)
      have e : j (a : A ⧸ N).out * (x : G ⧸ K).out = g * (j (n : A) * (k : G)) := by
        have hgx : j a * x = g := by rw [hx]; group
        rw [hn, hk, map_mul, mul_assoc (j a), ← mul_assoc (j (n : A)), c1.eq, mul_assoc x, ← mul_assoc (j a), hgx]
      rw [e, QuotientGroup.mk_mul_of_mem _ (K.mul_mem (hjN _ n.2) k.2), hg, QuotientGroup.out_eq']
  have hout : ∀ p ∈ S₁ ×ˢ S₂, h (φ p).out • ρ (φ p).out y = (f p.1.out * h₁ p.2.out) • ρ (j p.1.out * p.2.out) y := by
    rintro ⟨s, t⟩ hp
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (j s.out * t.out)
    have ht : t ∈ S₂ := (Finset.mem_product.1 hp).2
    show h (((j s.out * t.out : G) : G ⧸ K)).out • ρ (((j s.out * t.out : G) : G ⧸ K)).out y = _
    rw [hk, hright _ _ k.2, hterm s t ht, map_mul ρ (j s.out * t.out), Module.End.mul_apply, hyk _ k.2]
  rw [lv_eq_sum ρ K h _ hsupp, lv_eq_sum (ρ.comp j) N f S₁ (fun s hs => (m₁ s).2 hs),
    lv_eq_sum ρ K h₁ S₂ (fun t ht => (m₂ t).2 ht)]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_image hinj, Finset.sum_congr rfl hout, Finset.sum_product]
  refine Finset.sum_congr rfl fun s _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [MonoidHom.comp_apply, map_sum, map_smul, Finset.smul_sum, smul_smul, map_mul, Module.End.mul_apply]
end
