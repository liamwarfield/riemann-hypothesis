module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDict
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLatOfLattice
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsVanishingOffFramesLeSpanShortTheta

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSectionPolynomialGrowth
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory.SectionGrowth

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {B : LB Y}

theorem local_factor (hB : B.IsLB) {s : B.ι → CxPts p σ → ℂ} (hs : s ∈ fibSec p σ B)
    (hc : ∀ j, ContinuousOn (s j) (ptsIn p σ (B.U j))) {i : B.ι} {V Q : Y.Opens} (hV : V ≤ B.U i)
    (u : Γ(Y, V)) (η : Γ(Y, Q)) (hη : Y.basicOpen η = Q ⊓ V)
    (hu : resG Y (inf_le_right : Q ⊓ V ≤ V) u * resG Y (inf_le_left : Q ⊓ V ≤ Q) η = 1)
    {y₀ : CxPts p σ} (hy₀ : y₀ ∈ ptsIn p σ Q) :
    ∃ (F : CxPts p σ → ℂ) (N : ℕ), ContinuousAt F y₀ ∧
      ∀ᶠ y in 𝓝 y₀, y ∈ ptsIn p σ V → s i y = F y * ev p σ V u y ^ N := by

  obtain ⟨j, hy₀j⟩ : ∃ j, y₀ ∈ ptsIn p σ (B.U j) := ⟨_, mem_pick hB y₀⟩
  obtain ⟨W, hWa, hzW, hWle⟩ := (Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
    (Opens.mem_inf.2 ⟨mem_ptsIn.1 hy₀, mem_ptsIn.1 hy₀j⟩ :
      y₀.1 (IsLocalRing.closedPoint ℂ) ∈ Q ⊓ B.U j)
  have hWQ : W ≤ Q := hWle.trans inf_le_left
  have hWj : W ≤ B.U j := hWle.trans inf_le_right
  have hy₀W : y₀ ∈ ptsIn p σ W := mem_ptsIn.2 hzW

  set η' : Γ(Y, W) := resG Y hWQ η with hη'
  have hD : Y.basicOpen η' = W ⊓ (Q ⊓ V) := by
    rw [← hη]
    exact Y.basicOpen_res η (homOfLE hWQ).op
  have hDij : Y.basicOpen η' ≤ B.U i ⊓ B.U j := by
    rw [hD]
    exact le_inf (inf_le_right.trans (inf_le_right.trans hV)) (inf_le_left.trans hWj)

  have := hWa.isLocalization_basicOpen η'
  obtain ⟨⟨a, _, n, rfl⟩, han⟩ :=
    IsLocalization.surj (Submonoid.powers η') (resG Y hDij (B.g i j).val)
  rw [map_pow] at han
  refine ⟨fun y => ev p σ W a y * s j y, n, ?_, ?_⟩
  · exact ((continuousOn_ev a).continuousAt ((isOpen_ptsIn W).mem_nhds hy₀W)).mul
      ((hc j).continuousAt ((isOpen_ptsIn _).mem_nhds hy₀j))
  · filter_upwards [(isOpen_ptsIn W).mem_nhds hy₀W] with y hyW hyV
    have hyQ : y ∈ ptsIn p σ Q := ptsIn_mono hWQ hyW
    have hyj : y ∈ ptsIn p σ (B.U j) := ptsIn_mono hWj hyW
    have hyi : y ∈ ptsIn p σ (B.U i) := ptsIn_mono hV hyV
    have hyQV : y ∈ ptsIn p σ (Q ⊓ V) := mem_ptsIn_inf.2 ⟨hyQ, hyV⟩
    have huv : ev p σ V u y * ev p σ Q η y = 1 := by
      have h1 := congrArg (fun f => ev p σ (Q ⊓ V) f y) hu
      rwa [ev_mul, ev_res _ hyQV, ev_res _ hyQV, ev_one hyQV] at h1
    have hηne : ev p σ Q η y ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at huv
      exact zero_ne_one huv
    have hηW : ev p σ W η' y = ev p σ Q η y := ev_res hWQ hyW η
    have hyD : y ∈ ptsIn p σ (Y.basicOpen η') :=
      (mem_ptsIn_basicOpen hyW η').2 (hηW ▸ hηne)
    have hal : ∀ b : Γ(Y, W),
        ev p σ (Y.basicOpen η') (algebraMap Γ(Y, W) Γ(Y, Y.basicOpen η') b) y = ev p σ W b y :=
      fun b => ev_res (Y.basicOpen_le η') hyD b
    have e1 := congrArg (evHom hyD) han
    rw [map_mul, map_pow, ← ev_eq hyD, ← ev_eq hyD, ← ev_eq hyD, hal, hal, ev_res hDij hyD,
      hηW] at e1
    have hg : gv p σ B i j y = ev p σ (B.U i ⊓ B.U j) (B.g i j).val y := rfl
    have hun : (ev p σ V u y * ev p σ Q η y) ^ n = 1 := by rw [huv, one_pow]
    show s i y = ev p σ W a y * s j y * ev p σ V u y ^ n
    rw [hs.1 i j y hyi hyj, hg]
    linear_combination (s j y * ev p σ V u y ^ n) * e1 -
      (ev p σ (B.U i ⊓ B.U j) (B.g i j).val y * s j y) * hun

theorem global_bound {X : Type*} [TopologicalSpace X] [CompactSpace X] (S : Set X) (f T : X → ℝ)
    (hT : ∀ x, 1 ≤ T x)
    (h : ∀ x₀, ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ᶠ x in 𝓝 x₀, x ∈ S → f x ≤ C * T x ^ m) :
    ∃ (C : ℝ) (m : ℕ), ∀ x ∈ S, f x ≤ C * T x ^ m := by
  choose C m hC hev using h
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover
    (fun x₀ => {x | x ∈ S → f x ≤ C x₀ * T x ^ m x₀}) (fun x₀ _ => hev x₀)
  refine ⟨∑ x₀ ∈ t, C x₀, t.sup m, fun x hx => ?_⟩
  obtain ⟨x₀, hx₀t, hx₀⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  have h1 : f x ≤ C x₀ * T x ^ m x₀ := hx₀ hx
  have h2 : T x ^ m x₀ ≤ T x ^ t.sup m := pow_le_pow_right₀ (hT x) (Finset.le_sup hx₀t)
  have h3 : C x₀ ≤ ∑ x₀ ∈ t, C x₀ := Finset.single_le_sum (fun i _ => hC i) hx₀t
  have h4 : 0 ≤ T x ^ t.sup m := pow_nonneg (zero_le_one.trans (hT x)) _
  calc f x ≤ C x₀ * T x ^ m x₀ := h1
    _ ≤ C x₀ * T x ^ t.sup m := mul_le_mul_of_nonneg_left h2 (hC x₀)
    _ ≤ (∑ x₀ ∈ t, C x₀) * T x ^ t.sup m := mul_le_mul_of_nonneg_right h3 h4

end GlobalTheory.SectionGrowth

namespace GlobalTheory

theorem continuous_section_polynomial_growth : ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ), IsProjOver p → ∀ (B : LB Y), B.IsLB → ∀ s ∈ fibSec p (RingHom.id ℂ) B, (∀ j, ContinuousOn (s j) (ptsIn p (RingHom.id ℂ) (B.U j))) → ∀ (i : B.ι) (V : Y.Opens) (n : ℕ) (u : Fin n → Γ(Y, V)), V ≤ B.U i → (∀ z : Y, ∃ (Q : Y.Opens) (η : Γ(Y, Q)) (l : Fin n), z ∈ Q ∧ Y.basicOpen η = Q ⊓ V ∧ resG Y (inf_le_right : Q ⊓ V ≤ V) (u l) * resG Y (inf_le_left : Q ⊓ V ≤ Q) η = 1) → ∃ (C : ℝ) (m : ℕ), ∀ y ∈ ptsIn p (RingHom.id ℂ) V, ‖s i y‖ ≤ C * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m := by
  intro Y p hp B hB s hs hc i V n u hV hloc
  have := CxPts.compactSpace (RingHom.id ℂ) hp
  obtain ⟨C, m, hCm⟩ := SectionGrowth.global_bound (ptsIn p (RingHom.id ℂ) V) (fun y => ‖s i y‖)
    (fun y => 1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖)
    (fun y => le_add_of_nonneg_right (Finset.sum_nonneg fun l _ => norm_nonneg _)) (by
      intro y₀
      obtain ⟨Q, η, l, hzQ, hη, hu⟩ := hloc (y₀.1 (IsLocalRing.closedPoint ℂ))
      obtain ⟨F, N, hF, hev⟩ :=
        SectionGrowth.local_factor hB hs hc hV (u l) η hη hu (mem_ptsIn.2 hzQ)
      have hFb : ∀ᶠ y in 𝓝 y₀, ‖F y‖ < ‖F y₀‖ + 1 :=
        hF.norm.eventually (gt_mem_nhds (lt_add_one _))
      refine ⟨‖F y₀‖ + 1, N, by positivity, ?_⟩
      filter_upwards [hev, hFb] with y hy1 hy2 hyV
      have hle : ‖ev p (RingHom.id ℂ) V (u l) y‖ ≤
          1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖ := by
        have := Finset.single_le_sum (f := fun l => ‖ev p (RingHom.id ℂ) V (u l) y‖)
          (fun l _ => norm_nonneg _) (Finset.mem_univ l)
        linarith
      show ‖s i y‖ ≤ (‖F y₀‖ + 1) * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ N
      rw [hy1 hyV, norm_mul, norm_pow]
      exact mul_le_mul hy2.le (pow_le_pow_left₀ (norm_nonneg _) hle N) (by positivity)
        (by positivity))
  exact ⟨C, m, hCm⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermPairSectionsChangeOfIsometricCombinati
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermPairSectionsChangeOfIsometricCombinati
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSNef.ChangePair
open GlobalTheory.VolBr.NuEq
variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem exists_chart (M : HermLB p) (x : X) : ∃ c, x ∈ M.B.U c := by
  have h : x ∈ (⨆ c, M.B.U c) := by rw [M.isLB.cover]; trivial
  exact TopologicalSpace.Opens.mem_iSup.1 h

theorem loc_eq (P : Pair p) (a b a' b' i j : ℤ) (f : X.functionField) (ρ ρ' : X.functionFieldˣ) (e g) :
    f * (ρ : X.functionField) ^ i * (ρ' : X.functionField) ^ j =
      P.loc (i * a + j * a') (i * b + j * b') f e g *
        (((ρ : X.functionField) / P.loc a b 1 e g) ^ i * ((ρ' : X.functionField) / P.loc a' b' 1 e g) ^ j) := by
  have hs : (P.r e : X.functionField) ≠ 0 := (P.r e).ne_zero
  have ht : (P.r' g : X.functionField) ≠ 0 := (P.r' g).ne_zero
  simp only [Pair.loc, one_mul]
  rw [div_zpow, div_zpow, mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul,
    zpow_add₀ hs, zpow_add₀ ht, mul_comm a i, mul_comm b i, mul_comm a' j, mul_comm b' j]
  have h1 := zpow_ne_zero (i * a) hs
  have h2 := zpow_ne_zero (i * b) ht
  have h3 := zpow_ne_zero (j * a') hs
  have h4 := zpow_ne_zero (j * b') ht
  field_simp

end GlobalTheory.HSNef.ChangePair

namespace GlobalTheory.HSNef


open GlobalTheory.VolBr.NuEq ChangePair in
theorem change_pair : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (a b a' b' : ℤ) (M N : HermLB p), P.Rep a b M → P.Rep a' b' N → ∃ Q : Pair p, Q.L = M ∧ Q.A = N ∧ ∀ (i j : ℤ) (R : ℝ), Q.Bl i j R = P.Bl (i * a + j * a') (i * b + j * b') R := by
  intro k _ X _ p P a b a' b' M N ⟨ρ, hρ, hu, hn⟩ ⟨ρ', hρ', hu', hn'⟩
  let Q : Pair p := ⟨M, N, ρ, ρ', hρ, hρ'⟩
  have hw : ∀ (i j : ℤ) (x : X) c d e g, x ∈ M.B.U c → x ∈ N.B.U d → x ∈ P.L.B.U e → x ∈ P.A.B.U g →
      UnitAt x (((ρ c : X.functionField) / P.loc a b 1 e g) ^ i *
        ((ρ' d : X.functionField) / P.loc a' b' 1 e g) ^ j) :=
    fun i j x c d e g hc hd he hg =>
      (NuEq.unitAt_zpow (hu x c e g hc he hg) i).mul (NuEq.unitAt_zpow (hu' x d e g hd he hg) j)
  have hH : ∀ i j : ℤ, Q.H i j = P.H (i * a + j * a') (i * b + j * b') := by
    intro i j
    ext f
    constructor
    · intro hf x e g he hg
      obtain ⟨c, hc⟩ := exists_chart M x
      obtain ⟨d, hd⟩ := exists_chart N x
      have hW := hw i j x c d e g hc hd he hg
      have h := hf x c d hc hd
      change RegAt x (f * _ ^ i * _ ^ j) at h
      rw [loc_eq P a b a' b' i j f (ρ c) (ρ' d) e g] at h
      have h' := h.mul hW.inv.regAt
      rwa [mul_assoc, mul_inv_cancel₀ hW.ne_zero, mul_one] at h'
    · intro hf x c d hc hd
      obtain ⟨e, he⟩ := exists_chart P.L x
      obtain ⟨g, hg⟩ := exists_chart P.A x
      change RegAt x (f * _ ^ i * _ ^ j)
      rw [loc_eq P a b a' b' i j f (ρ c) (ρ' d) e g]
      exact (hf x e g he hg).mul (hw i j x c d e g hc hd he hg).regAt
  have hnu : ∀ (i j : ℤ) (f : X.functionField), f ∈ P.H (i * a + j * a') (i * b + j * b') →
      ∀ (σ : k →+* ℂ) (y : CxPts p σ), Q.nu i j σ y f = P.nu (i * a + j * a') (i * b + j * b') σ y f := by
    intro i j f hf σ y
    have hc := mem_pick (M.φ σ).isLB y
    have hd := mem_pick (N.φ σ).isLB y
    have he := mem_pick (P.L.φ σ).isLB y
    have hg := mem_pick (P.A.φ σ).isLB y
    set c := pick (M.φ σ).isLB y
    set d := pick (N.φ σ).isLB y
    set e := pick (P.L.φ σ).isLB y
    set g := pick (P.A.φ σ).isLB y
    have hfQ : f ∈ Q.H i j := (hH i j).symm ▸ hf
    rw [nu_eq k X p Q i j f hfQ σ y c d hc hd, nu_eq k X p P _ _ f hf σ y e g he hg]
    have hU := hu _ c e g (mem_ptsIn.1 hc) (mem_ptsIn.1 he) (mem_ptsIn.1 hg)
    have hU' := hu' _ d e g (mem_ptsIn.1 hd) (mem_ptsIn.1 he) (mem_ptsIn.1 hg)
    have hreg : RegAt (under y) (P.loc (i * a + j * a') (i * b + j * b') f e g) :=
      hf _ e g (mem_ptsIn.1 he) (mem_ptsIn.1 hg)
    have eU : ‖ratVal ((ρ c : X.functionField) / P.loc a b 1 e g) y‖ =
        Real.exp ((M.φ σ).φ c y / 2 - (a * (P.L.φ σ).φ e y + b * (P.A.φ σ).φ g y) / 2) := by
      rw [← Real.exp_log (norm_pos_iff.2 (ratVal_ne_zero hU))]
      congr 1
      linarith [hn σ y c e g hc he hg]
    have eU' : ‖ratVal ((ρ' d : X.functionField) / P.loc a' b' 1 e g) y‖ =
        Real.exp ((N.φ σ).φ d y / 2 - (a' * (P.L.φ σ).φ e y + b' * (P.A.φ σ).φ g y) / 2) := by
      rw [← Real.exp_log (norm_pos_iff.2 (ratVal_ne_zero hU'))]
      congr 1
      linarith [hn' σ y d e g hd he hg]
    change ‖ratVal (f * _ ^ i * _ ^ j) y‖ * _ = _
    rw [loc_eq P a b a' b' i j f (ρ c) (ρ' d) e g,
      ratVal_mul hreg ((NuEq.unitAt_zpow hU i).mul (NuEq.unitAt_zpow hU' j)).regAt,
      ratVal_mul (NuEq.unitAt_zpow hU i).regAt (NuEq.unitAt_zpow hU' j).regAt,
      ratVal_zpow' hU, ratVal_zpow' hU', norm_mul, norm_mul, norm_zpow, norm_zpow, eU, eU',
      ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.exp_mul, ← Real.exp_mul, mul_assoc,
      ← Real.exp_add, ← Real.exp_add]
    congr 2
    push_cast
    ring
  refine ⟨Q, rfl, rfl, fun i j R => ?_⟩
  ext f
  constructor
  · rintro ⟨hf, hR⟩
    have hf' : f ∈ P.H (i * a + j * a') (i * b + j * b') := hH i j ▸ hf
    exact ⟨hf', fun σ y => hnu i j f hf' σ y ▸ hR σ y⟩
  · rintro ⟨hf, hR⟩
    exact ⟨(hH i j).symm ▸ hf, fun σ y => (hnu i j f hf σ y).symm ▸ hR σ y⟩

end GlobalTheory.HSNef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermPairSectionsChangeOfIsometricCombinatiStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermPairSections_change_of_isometric_combinations : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (a b a' b' : ℤ) (M N : HermLB p), P.Rep a b M → P.Rep a' b' N → ∃ Q : Pair p, Q.L = M ∧ Q.A = N ∧ ∀ (i j : ℤ) (R : ℝ), Q.Bl i j R = P.Bl (i * a + j * a') (i * b + j * b') R := by
  first | exact @GlobalTheory.HSNef.change_pair | exact GlobalTheory.HSNef.change_pair | (intros; apply GlobalTheory.HSNef.change_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesOddRankGap
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section
namespace GlobalTheory.ParamMatch

theorem lamAt_anti_fin {Rk : Ranks} (h : HCParam Rk) {n : ℕ} (hn : n ≤ Rk.r) :
    StrictAnti fun a : Fin n => Formalism.L2.NTheta.lamAt h a := by
  intro a b hab
  have hab' : (a : ℕ) < b := hab
  have h1 := Formalism.L2.NTheta.lamAt_add_add_le h ((b : ℕ) - a) a (by omega)
  rw [show (a : ℕ) + ((b : ℕ) - a) = b by omega] at h1
  have h2 : (1 : ℚ) ≤ (((b : ℕ) - a : ℕ) : ℚ) := by exact_mod_cast (by omega : 1 ≤ (b : ℕ) - a)
  show Formalism.L2.NTheta.lamAt h b < Formalism.L2.NTheta.lamAt h a
  linarith

theorem enum_fst {n : ℕ} {S : SPar} {lam : Fin n → ℝ} {ε : Fin n → Bool} (he : IsEnum S lam ε)
    (f : Fin n → ℚ) (hf : StrictAnti f) (hS : S.image Prod.fst = Finset.univ.image f) (a : Fin n) :
    lam a = f a := by
  obtain ⟨h1, q, hq, rfl⟩ := he
  have h3 : StrictAnti q := fun a b hab => by
    have := h1 hab
    rw [hq, hq] at this
    exact_mod_cast this
  have h4 : Finset.univ.image q = Finset.univ.image f := by
    rw [← hS, Finset.image_image]; rfl
  have h5 : q = f := by
    refine (h3.range_inj hf).1 ?_
    have := congrArg (fun s : Finset ℚ => (s : Set ℚ)) h4
    simpa [Finset.coe_image] using this
  rw [hq, h5]

theorem lamAt_b' {Rk : Ranks} (h : HCParam Rk) (j : Fin Rk.m) :
    Formalism.L2.NTheta.lamAt h (Rk.k - 1 + j) = -h.b j := by
  have hc : ∀ (x y : ℕ) (hx : x < Rk.m) (hy : y < Rk.m), x = y → h.b ⟨x, hx⟩ = h.b ⟨y, hy⟩ := by
    rintro x _ _ _ rfl; rfl
  unfold Formalism.L2.NTheta.lamAt
  rw [dite_eq_right (by omega), dite_eq_left (by omega)]
  rw [hc _ _ _ j.2 (by omega)]

theorem lamAt_v' {Rk : Ranks} (h : HCParam Rk) (j : Fin (Rk.k - 1)) :
    Formalism.L2.NTheta.lamAt h j = h.v j := by
  unfold Formalism.L2.NTheta.lamAt
  rw [dite_eq_left j.2]

theorem parA_fst (D : D7) (ρ : D.what₂.Tau) {n : ℕ} (hn : n = D.R.r) :
    (parA (Ptw D) 0 ρ).image Prod.fst = Finset.univ.image fun a : Fin n => Formalism.L2.NTheta.lamAt (D.hc ρ) a := by
  subst hn
  have hk := D.R.m_add_three_le_k
  have hv : (Ptw D).v ρ = (D.hc ρ).v := rfl
  have hb : (Ptw D).b ρ = (D.hc ρ).b := rfl
  ext x
  simp [parA, TPar.Dpar]
  rw [hv, hb]
  constructor
  · rintro (⟨a, rfl, -⟩ | ⟨a, rfl⟩ | ⟨a, rfl, -⟩)
    · exact ⟨⟨D.R.k - 1 + a, by have := a.2; unfold Ranks.r; omega⟩, lamAt_b' _ a⟩
    · exact ⟨⟨a, by have := a.2; unfold Ranks.r; omega⟩, lamAt_v' _ a⟩
    · exact ⟨⟨D.R.k - 1 + a, by have := a.2; unfold Ranks.r; omega⟩, lamAt_b' _ a⟩
  · rintro ⟨a, rfl⟩
    have ha := a.2
    unfold Ranks.r at ha
    by_cases h1 : (a : ℕ) < D.R.k - 1
    · exact Or.inr (Or.inl ⟨⟨a, h1⟩, (lamAt_v' _ ⟨a, h1⟩).symm⟩)
    · let c : Fin D.R.m := ⟨a - (D.R.k - 1), by omega⟩
      have hc : Formalism.L2.NTheta.lamAt (D.hc ρ) a = -(D.hc ρ).b c := by
        rw [← lamAt_b' _ c]; congr 1; simp only [c]; omega
      rw [hc]
      by_cases h2 : (c : ℕ) = 0 ∨ Even (c : ℕ)
      · exact Or.inr (Or.inr ⟨c, rfl, h2⟩)
      · push_neg at h2
        exact Or.inl ⟨c, rfl, h2.1, h2.2⟩

theorem tauE_inj {D : D7} {τ ρ : D.what₂.Tau} (h : tauE D τ = tauE D ρ) : τ = ρ :=
  D.eTau.injective (Subtype.ext (Formalism.IndefR.Conj.emb_injective h))

open Formalism.FrobeniusOrbits in
theorem tauE_ne_conj' {D : D7} (τ ρ : D.what₂.Tau) : tauE D τ ≠ (starRingEnd ℂ).comp (tauE D ρ) := by
  intro h
  unfold tauE at h
  rw [Formalism.IndefR.Conj.conj_comp_emb] at h
  have e1 : (D.eTau τ).1.1.2 = ((D.eTau ρ).1 * D.R.cc).1.2 :=
    congrArg (fun g : D.R.GG => g.1.2) (Formalism.IndefR.Conj.emb_injective h)
  have hc := Formalism.IndefR.Conj.snd_side (D := D) false
  simp only [Bool.false_eq_true, if_false] at hc
  rw [show ((D.eTau ρ).1 * D.R.cc).1.2 = (D.eTau ρ).1.1.2 * (D.R.cc).1.2 from rfl] at e1
  rw [(Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau τ).2, (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau ρ).2, one_mul, hc] at e1
  exact absurd e1 (by decide)

theorem lab_base {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (ρ : D.what₂.Tau) :
    lab (sg0 D A) ρ = ρ ∧ labE (sg0 D A) ρ = tauE D ρ := by
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hb : ∀ τ, labE D.what₂.embLL τ = tauE D τ := fun τ => Formalism.IndefR.Conj.labE_base τ
  rw [hs]
  refine ⟨?_, hb ρ⟩
  have hex : ∃ τ, labE D.what₂.embLL τ = tauE D ρ ∨ labE D.what₂.embLL τ = (starRingEnd ℂ).comp (tauE D ρ) :=
    ⟨ρ, Or.inl (hb ρ)⟩
  unfold lab
  rw [dite_eq_left hex]
  rcases hex.choose_spec with h | h
  · rw [hb] at h; exact tauE_inj h
  · rw [hb] at h; exact absurd h (tauE_ne_conj' _ _)

theorem parAt_fst {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (ρ : D.what₂.Tau) {n : ℕ} (hn : n = D.R.r) :
    (parAt (Wc D i) (sg0 D A) ρ).image Prod.fst =
      Finset.univ.image fun a : Fin n => Formalism.L2.NTheta.lamAt (D.hc ρ) a := by
  subst hn
  obtain ⟨h1, h2⟩ := lab_base R ρ
  have hpq : ((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2 = D.R.r := by
    have hk := D.R.m_add_three_le_k
    have hi := i.2
    rw [D.sp.W_sigval _ (Nat.le_add_left _ _) i.2]
    simp only [Ranks.sigW, Ranks.r]; omega
  rw [parAt, if_pos (by rw [h1]; exact h2), kapAt, h1]
  generalize ((Wc D i).sig (tauE D ρ)).1 = p at hpq ⊢
  generalize ((Wc D i).sig (tauE D ρ)).2 = q at hpq ⊢
  have ho : Odd (p + q) := hpq ▸ Formalism.L2.NTheta.odd_r D.R
  ext x
  simp only [Formalism.L2.NTheta.holPar, Finset.image_image, Finset.mem_image, Finset.mem_univ, true_and,
    Function.comp_def, Formalism.L2.NTheta.holEnt_kapW _ _ _ ho]
  constructor
  · rintro ⟨(a | c), rfl⟩
    · exact ⟨⟨a, by omega⟩, rfl⟩
    · exact ⟨⟨p + c, by omega⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    have ha := a.2
    by_cases hap : (a : ℕ) < p
    · exact ⟨Sum.inl ⟨a, hap⟩, rfl⟩
    · refine ⟨Sum.inr ⟨a - p, by omega⟩, ?_⟩
      simp only [Sum.elim_inr]
      congr 1
      omega

end GlobalTheory.ParamMatch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePartZeroNeOfIsVacuumOrientedModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePartZeroNeOfIsVacuumOrientedModel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.VacNonzeroReal

variable {D : D7}

theorem continuous_finTmul (e : D.host.E) :
    Continuous fun x : Af D.host.F => (pairA D.host.F 0 x ⊗ₜ[D.host.F] e : AE D) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
  have h1 : Continuous fun x : Af D.host.F => pairA D.host.F 0 x :=
    continuous_const.prodMk continuous_id
  have h2 : Continuous fun x : Af D.host.F => pairA D.host.F 0 x • ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D) :=
    h1.smul (continuous_const : Continuous fun _ : Af D.host.F => ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D))
  refine h2.congr fun x => ?_
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem infPart_finTmul (x : Af D.host.F) (e : D.host.E) :
    infPart D (pairA D.host.F 0 x ⊗ₜ[D.host.F] e) = 0 := by
  show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)) (pairA D.host.F 0 x ⊗ₜ[D.host.F] e) = 0
  rw [Algebra.TensorProduct.map_tmul]
  show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] _ = 0
  rw [TensorProduct.zero_tmul]

theorem finPart_infTmul (x : Ainf D.host.F) (e : D.host.E) :
    finPart D (pairA D.host.F x 0 ⊗ₜ[D.host.F] e) = 0 := by
  show (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) (pairA D.host.F x 0 ⊗ₜ[D.host.F] e) = 0
  rw [Algebra.TensorProduct.map_tmul]
  show (0 : Af D.host.F) ⊗ₜ[D.host.F] _ = 0
  rw [TensorProduct.zero_tmul]


set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 1600000 in
theorem decomp_AE (V : AddSubgroup (AE D)) (hV : IsOpen (V : Set (AE D))) (z : AE D) :
    ∃ e : D.host.E, ∃ u ∈ V, infPart D u = 0 ∧ ∃ r : AE D, finPart D r = 0 ∧ z = incA D e + u + r := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, V.zero_mem, map_zero _, 0, map_zero _, by rw [map_zero, add_zero, add_zero]⟩
  | tmul a e =>
    set W : Set (Af D.host.F) := (fun x => (pairA D.host.F 0 x ⊗ₜ[D.host.F] e : AE D)) ⁻¹' V with hW
    have hWo : IsOpen W := hV.preimage (continuous_finTmul e)
    have hO : IsOpen {x : Af D.host.F | a.2 - x ∈ W} := hWo.preimage (continuous_const.sub continuous_id)
    obtain ⟨c, hc⟩ := Formalism.L2.SG.Pf.CondStd.dense_F.exists_mem_open hO
      ⟨a.2, by
        show (pairA D.host.F 0 (a.2 - a.2) ⊗ₜ[D.host.F] e : AE D) ∈ V
        rw [sub_self]
        have : pairA D.host.F 0 (0 : Af D.host.F) = 0 := rfl
        rw [this, TensorProduct.zero_tmul]
        exact V.zero_mem⟩
    refine ⟨algebraMap D.host.F D.host.E c * e, _, hc, infPart_finTmul _ _, _, finPart_infTmul (a.1 - algebraMap D.host.F (Ainf D.host.F) c) e, ?_⟩
    have hinc : incA D (algebraMap D.host.F D.host.E c * e) =
        algebraMap D.host.F (AF D.host.F) c ⊗ₜ[D.host.F] e := by
      show (1 : AF D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E c * e) = _
      have h1 : (1 : AF D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E c * e) =
          ((1 : AF D.host.F) ⊗ₜ[D.host.F] algebraMap D.host.F D.host.E c) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      have h2 : algebraMap D.host.F (AF D.host.F) c ⊗ₜ[D.host.F] e =
          (algebraMap D.host.F (AF D.host.F) c ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [h1, h2, ← Algebra.TensorProduct.algebraMap_apply, ← Algebra.TensorProduct.algebraMap_apply']
    rw [hinc, ← TensorProduct.add_tmul, ← TensorProduct.add_tmul]
    congr 1
    refine Prod.ext ?_ ?_
    · show a.1 = algebraMap D.host.F (Ainf D.host.F) c + 0 + (a.1 - algebraMap D.host.F (Ainf D.host.F) c)
      abel
    · show a.2 = algebraMap D.host.F (Af D.host.F) c + (a.2 - algebraMap D.host.F (Af D.host.F) c) + 0
      abel
  | add x y hx hy =>
    obtain ⟨e, u, hu, hu0, r, hr0, hx⟩ := hx
    obtain ⟨e', u', hu', hu0', r', hr0', hy⟩ := hy
    refine ⟨e + e', u + u', V.add_mem hu hu', by rw [map_add (f := _), hu0, hu0', add_zero], r + r',
      by rw [map_add (f := _), hr0, hr0', add_zero], ?_⟩
    rw [hx, hy, map_add (f := _), add_add_add_comm _ r, add_add_add_comm (incA D e) u]

theorem continuous_single {m n : ℕ} (i : Fin m) (j : Fin n) :
    Continuous fun v : AE D => (Matrix.single i j v : Matrix (Fin m) (Fin n) (AE D)) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    simp only [Matrix.single_apply, and_self, if_true]
    exact continuous_id
  · have : ∀ v : AE D, (Matrix.single i j v : Matrix (Fin m) (Fin n) (AE D)) a b = 0 := fun v => by
      rw [Matrix.single_apply, if_neg h]
    simpa only [this] using continuous_const

def singleHom {m n : ℕ} (i : Fin m) (j : Fin n) : AE D →+ Matrix (Fin m) (Fin n) (AE D) where
  toFun v := Matrix.single i j v
  map_zero' := Matrix.single_zero i j
  map_add' x y := Matrix.single_add i j x y

theorem decomp_WO {S T : HSp D} (U : AddSubgroup (WO S T)) (hU : IsOpen (U : Set (WO S T))) (w : WO S T) :
    ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ u ∈ U, u.map (infPart D) = 0 ∧
      ∃ r : WO S T, r.map (finPart D) = 0 ∧ w = ratW T S γ + u + r := by
  classical
  have hV : ∀ i j, IsOpen ((U.comap (singleHom i j) : AddSubgroup (AE D)) : Set (AE D)) := fun i j =>
    hU.preimage (continuous_single i j)
  choose e u hu hu0 r hr0 hw using fun i j => decomp_AE _ (hV i j) (w i j)
  refine ⟨Matrix.of e, Matrix.of u, ?_, ?_, Matrix.of r, ?_, ?_⟩
  · rw [Matrix.matrix_eq_sum_single (Matrix.of u)]
    exact U.sum_mem fun i _ => U.sum_mem fun j _ => hu i j
  · ext i j
    simp [hu0 i j]
  · ext i j
    simp [hr0 i j]
  · ext i j
    rw [hw i j]
    rfl

theorem exists_finPart_zero_ne : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (f : WO S T → ℂ), IsVacO ψ θ S T sS sT LS LT f → ∃ w : WO S T, w.map (finPart D) = 0 ∧ f w ≠ 0 := by
  intro D ψ θ S T sS sT LS LT f hv
  have hne := GlobalTheory.TwistFactorProof.vac_ne_zero hv
  have hth : IsThetaFunO ψ S T f := hv.2.theta
  obtain ⟨w0, hw0⟩ : ∃ w, f w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  obtain ⟨U, hUo, hU⟩ := hth.level
  obtain ⟨γ, u, huU, hu0, r, hr0, rfl⟩ := decomp_WO U hUo w0
  refine ⟨r, hr0, fun hfr => ?_⟩
  have hψ : ∀ a, ψ a ≠ 0 := fun a => by
    have : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    exact left_ne_zero_of_mul_eq_one this
  rw [add_assoc, hth.quasi γ (u + r)] at hw0
  have hfur : f (u + r) ≠ 0 := right_ne_zero_of_mul hw0
  have h2 := congrFun (hU u huU hu0) r
  unfold heisO at h2
  rw [hfr, add_comm r u] at h2
  exact (mul_ne_zero (hψ _) hfur) h2

end GlobalTheory.VacNonzeroReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePartZeroNeOfIsVacuumOrientedModelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finitePartZero_ne_of_isVacuum_orientedModel : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (f : WO S T → ℂ), IsVacO ψ θ S T sS sT LS LT f → ∃ w : WO S T, w.map (finPart D) = 0 ∧ f w ≠ 0 := by
  first | exact @GlobalTheory.VacNonzeroReal.exists_finPart_zero_ne | exact GlobalTheory.VacNonzeroReal.exists_finPart_zero_ne | (intros; apply GlobalTheory.VacNonzeroReal.exists_finPart_zero_ne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolSub0LeSpanShortGenUpto
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

open GlobalTheory.Dict.Extend GlobalTheory.Dict.Pull

namespace GlobalTheory.LargeCover

section Pull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def PrincUpTo (X : Data E r) (M : ℕ) (la : Wt X.Ψ r) : Prop :=
  ∀ ga : GL (Fin r) E, IsUStab X.Gm X.Λ ga →
    (∀ v ∈ X.Λ, ∃ u ∈ X.Λ, (ga : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • u) →
      ∃ gb ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, bchar la b = 1 ∧ ∀ x, lact gb x = lact ga (rmul x b)

theorem conj_stab {X X' : Data E r} (hG : X'.Gm = X.Gm) {a g : GL (Fin r) E} {M : ℕ} (ha : IsUn X a) (hg : IsUn X g)
    (hfix : mapL g (mapL a X'.Λ) = mapL a X'.Λ)
    (hM : ∀ u ∈ mapL a X'.Λ, ∃ u' ∈ mapL a X'.Λ, (g : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u') :
    IsUStab X'.Gm X'.Λ (a⁻¹ * g * a) ∧
      ∀ v ∈ X'.Λ, ∃ u ∈ X'.Λ, ((a⁻¹ * g * a : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • u := by
  have hc : mapL (a⁻¹ * g * a) X'.Λ = X'.Λ := by
    rw [mapL_mul, mapL_mul, hfix, ← mapL_mul, inv_mul_cancel, mapL_one]
  refine ⟨⟨?_, fun x => ?_⟩, fun v hv => ?_⟩
  · rw [hG]
    exact isUn_mul (isUn_mul (isUn_inv ha) hg) ha
  · rw [← mem_mapL (a := a⁻¹ * g * a), hc]
  · obtain ⟨u', ⟨w, hw, e⟩, hu⟩ := hM _ (mem_mapL.2 hv)
    have e' : (a : Matrix (Fin r) (Fin r) E) *ᵥ w = u' := e
    refine ⟨w, hw, ?_⟩
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hu, ← e',
      Matrix.mulVec_add, Matrix.mulVec_smul, inv_mulVec, inv_mulVec]

theorem exists_pow_root_eq_one (K : Type) [Field K] [NumberField K] :
    ∃ w : ℕ, 0 < w ∧ ∀ (u : K) (n : ℕ), 0 < n → u ^ n = 1 → u ^ w = 1 := by
  refine ⟨NumberField.Units.torsionOrder K, NumberField.Units.torsionOrder_pos K, fun u n hn hu => ?_⟩
  have hi : IsIntegral ℤ u := IsIntegral.of_pow hn (hu ▸ isIntegral_one)
  have h1 : (⟨u, hi⟩ : 𝓞 K) ^ n = 1 := Subtype.ext hu
  let v : (𝓞 K)ˣ := Units.ofPowEqOne _ n h1 hn.ne'
  have hv : v ∈ NumberField.Units.torsion K :=
    (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, Units.pow_ofPowEqOne h1 hn.ne'⟩)
  have h2 : (⟨v, hv⟩ : NumberField.Units.torsion K) ^ NumberField.Units.torsionOrder K = 1 := by
    unfold NumberField.Units.torsionOrder
    first | exact pow_card_eq_one | exact pow_card_eq_one'
  have h3 : v ^ NumberField.Units.torsionOrder K = 1 := congrArg Subtype.val h2
  exact congrArg (fun x : (𝓞 K)ˣ => ((x : 𝓞 K) : K)) h3

theorem princUpTo_of_root (X : Data E r) (M w : ℕ) (hw : ∀ (u : E) (n : ℕ), 0 < n → u ^ n = 1 → u ^ w = 1)
    (la : Wt X.Ψ r) (hla : ∀ τ i, (w : ℤ) ∣ la τ i)
    (h : ∀ ga : GL (Fin r) E, IsUStab X.Gm X.Λ ga →
      (∀ x ∈ X.Λ, ∃ y ∈ X.Λ, (ga : Matrix (Fin r) (Fin r) E) *ᵥ x - x = (M : E) • y) →
      ∃ gb ∈ X.Γ, ∃ (u : E) (n : ℕ), 0 < n ∧ u ^ n = 1 ∧
        (gb : Matrix (Fin r) (Fin r) E) = u • (ga : Matrix (Fin r) (Fin r) E)) : PrincUpTo X M la := by
  intro ga hga hc
  obtain ⟨gb, hgb, u, n, hn, hu, he⟩ := h ga hga fun x hx => by
    obtain ⟨y, hy, e⟩ := hc x hx
    exact ⟨y, hy, by rw [e, add_sub_cancel_left, Nat.cast_smul_eq_nsmul]⟩
  have hu0 : u ≠ 0 := by rintro rfl; rw [zero_pow hn.ne'] at hu; exact zero_ne_one hu
  let b : Frame X.Ψ r := fun τ => (Matrix.diagonal fun _ => τ.1 u : Matrix (Fin r) (Fin r) ℂ)
  have hb : ∀ τ, mat b τ = τ.1 u • (1 : Matrix (Fin r) (Fin r) ℂ) := fun τ => by
    rw [Matrix.smul_one_eq_diagonal]; rfl
  refine ⟨gb, hgb, b, fun τ => ⟨?_, fun a c hac => Matrix.diagonal_apply_ne _ hac.ne'⟩, ?_, fun x => ?_⟩
  · rw [hb, Matrix.det_smul, Matrix.det_one, _root_.mul_one]
    exact pow_ne_zero _ ((map_ne_zero τ.1).2 hu0)
  · refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun i _ => ?_
    obtain ⟨k, hk⟩ := hla τ i
    have : b τ i i = τ.1 u := Matrix.diagonal_apply_eq _ i
    rw [this, hk, _root_.zpow_mul, zpow_natCast, ← map_pow, hw u n hn hu, map_one, _root_.one_zpow]
  · funext τ
    show (gb : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
      (ga : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ)
    have : (u • (ga : Matrix (Fin r) (Fin r) E)).map τ.1 = τ.1 u • (ga : Matrix (Fin r) (Fin r) E).map τ.1 := by
      ext a c; simp
    rw [he, this, hb, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul]

end Pull

theorem isStabForm_pull_upto (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X' X : Data E r) (h : SameSp X' X) (ga : GL (Fin r) E) (la' : Wt X'.Ψ r) (la : Wt X.Ψ r) (Δ : Subgroup (GL (Fin r) E)) (M : ℕ) (P : Frame X'.Ψ r → ℂ) (hga : IsUn X ga) (hl : ∀ (τ : X.Ψ) i, la τ i = la' ⟨τ.1, by rw [h.psi]; exact τ.2⟩ i) (hΔ : ∀ g' ∈ Δ, IsUn X g' ∧ (mapL g' (mapL ga X'.Λ) = mapL ga X'.Λ → ∀ u ∈ mapL ga X'.Λ, ∃ u' ∈ mapL ga X'.Λ, (g' : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u')) (hP : PrincUpTo X' M la') (hχ : ChiOne X' la') (hb : X'.IsBddSec la' P) : IsStabForm X Δ (mapL ga X'.Λ) la (fun x => P (castFr h.psi.symm (lact ga⁻¹ x))) ∧ ∀ x ∈ X'.dom, lact ga (castFr h.psi x) ∈ X.dom ∧ castFr h.psi.symm (lact ga⁻¹ (lact ga (castFr h.psi x))) = x := by
  obtain ⟨⟨hd, hbor, hinv⟩, C, hC⟩ := hb
  have m1 : ∀ x ∈ X.dom, castFr h.psi.symm (lact ga⁻¹ x) ∈ X'.dom := fun x hx =>
    cast_GG h.psi.symm h.gm.symm h.p0.symm (lact_mem (isUn_inv hga) hx)
  have m2 : ∀ x ∈ X'.dom, lact ga (castFr h.psi x) ∈ X.dom := fun x hx =>
    lact_mem hga (cast_GG h.psi h.gm h.p0 hx)
  refine ⟨⟨?_, ?_, ?_, C, ?_⟩, fun x hx => ⟨m2 x hx, ?_⟩⟩
  · exact hd.comp ((cast_diff h.psi.symm).comp (differentiable_lact ga⁻¹)).differentiableOn m1
  · intro x hx b hb
    rw [lact_rmul, cast_rmul, hbor _ (m1 x hx) _ (cast_bor h.psi.symm hb), ← cast_bchar h.psi hl]
    rfl
  · intro g hg hfix x hx
    obtain ⟨s1, s2⟩ := conj_stab h.gm hga (hΔ g hg).1 hfix ((hΔ g hg).2 hfix)
    obtain ⟨gb, hgb, b, hb, hb1, hgbb⟩ := hP _ s1 s2
    have e : lact ga⁻¹ (lact g x) = lact (ga⁻¹ * g * ga) (lact ga⁻¹ x) := by
      rw [lact_lact, lact_lact, mul_inv_cancel_right]
    show P (castFr h.psi.symm (lact ga⁻¹ (lact g x))) = _
    have e2 := hinv _ hgb _ (m1 x hx)
    rw [hχ _ hgb, _root_.one_mul, hgbb, lact_rmul, hbor _ (lact_mem s1.1 (m1 x hx)) _ hb, hb1, _root_.one_mul] at e2
    rw [e, cast_lact, e2]
  · intro x hx
    refine le_of_eq_of_le ?_ (hC _ (m1 x hx))
    unfold Data.pnorm
    rw [cast_wt h.psi h.gm hl]
    simp only [dmin_lact (isUn_inv hga)]
  · rw [lact_lact, inv_mul_cancel, lact_one, cast_symm]


set_option maxHeartbeats 800000 in
theorem holSub0_le_span_shortGen_upto : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → l.A = 1 → (∀ k k', (U.X k).Gm = (U.X k').Gm ∧ (U.X k).ξ0 = (U.X k').ξ0) → d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → UnitC d → ¬ 3 ∣ d.pd → (Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, d.PhiPin ph ψ x₀) → ∀ (nab : NabV Xo c) (bad nV : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < bad → Dom a n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → (∀ k, PrincUpTo (U.X k) l.M (Formalism.L2.PjFree.laU U a n k)) → (∀ k, ChiOne (U.X k) (Formalism.L2.PjFree.laU U a n k)) → ShortValTot Xo c nab bad nV a n d → Dict.holSub0 U.X (Formalism.L2.PjFree.laU U a n) ≤ Submodule.span ℂ (Formalism.L2.PjFree.rdU U '' shortGen Xo c nab bad nV a n d) := by
  intro hci E _ _ _ H Dw l Xo c n d σ r U hσ hU hr1 hA hG hlev hnab huc h3 hpin nab bad nV a hbad hdom hbig
    hpr hchi htot P hP
  obtain ⟨hP1, hP0⟩ := hP
  rcases isEmpty_or_nonempty U.Comp with hemp | ⟨⟨k₀⟩⟩
  · have : P = 0 := funext fun k => (hemp.false k).elim
    rw [this]
    exact Submodule.zero_mem _
  obtain ⟨W⟩ := nonempty_uw hU
  have hrpq : r = Dw.p + Dw.q := hU.1
  have hn : r ≤ n := by
    have := Module.finrank_pos (R := ℚ) (M := E)
    nlinarith
  have hev : Even n := by
    unfold Formalism.L2.Pj.Dom at hdom
    tauto
  have huw := GlobalTheory.T.uniformisation_component_lattices_markings E H Dw l Xo c σ r U hσ hU hr1 W
  have hsame : ∀ k, SameSp (U.X k) (U.X k₀) := fun k =>
    ⟨Finset.ext fun τ => ((hU.2.1 k).2 τ).trans ((hU.2.1 k₀).2 τ).symm, (hG k k₀).1,
      (hU.2.1 k).1.trans (hU.2.1 k₀).1.symm, (hG k k₀).2, by rw [(huw k).1, (huw k₀).1, (hG k k₀).2]⟩
  obtain ⟨ph, ψ, x₀, hph⟩ := hpin (hrpq ▸ hn)
  obtain ⟨Dc, hDe, -⟩ := GlobalTheory.T.exists_letterRowWeightDictionary E H Dw l c σ r W.g n (U.X k₀) a W.e hσ hrpq (hU.2.1 k₀).1 (hU.2.1 k₀).2
    (huw k₀).2.1 hdom
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_classicalLevelData_coverSelfDual E H Dw l Xo c n d σ r (U.X k₀) hn hrpq (huw k₀).2.1 hlev h3 ph ψ x₀ hph
  obtain ⟨v₀, mu, hv₀, hmu⟩ := GlobalTheory.SW.exists_vacua_and_multipliers E r (U.X k₀) W.g Dc.bas Dc.idx n Dc.sympl hev D
  obtain ⟨x0, ga, δ, hadm, hset, hsep⟩ := GlobalTheory.T.exists_components_lattices_moved_to_level_family E H Dw l Xo c n d σ r U hσ hU hr1 hA hlev W k₀ hsame ph D hn hD
  obtain ⟨u, hu, hread⟩ := GlobalTheory.T.short_series_readings_eq_classical_thetaSeries hci E H Dw l Xo c n d σ r U hσ hU hr1 hlev hnab huc ph ψ x₀ hph W (U.X k₀) a
    hdom Dc D hn hDe hD v₀ hv₀ x0
  choose C hC hrd using fun k => hread k (hsame k) (ga k) (δ k) (hset k).1 (hset k).2.1 (hset k).2.2.1
    (hset k).2.2.2.1 (hset k).2.2.2.2
  have hmu1 := GlobalTheory.T.vacuum_multiplier_eq_one_on_stabiliser E H Dw l Xo c n d σ r W.g (U.X k₀) Dc.bas Dc.idx D hn ph Dc.sympl hev hD
    (W.F.Di (W.ik k₀)) (W.emb k₀) (huw k₀).2.2.2.1 (huw k₀).2.2.2.2.1 (huw k₀).2.2.2.2.2.1 (huw k₀).2.2.2.2.2.2
    v₀ hv₀ mu hmu
  have hgrp := (GlobalTheory.SW.level_laws E r (U.X k₀) W.g Dc.bas Dc.idx n Dc.sympl hev D hn).2.2.1
  have hpull := fun k => isStabForm_pull_upto E r (U.X k) (U.X k₀) (hsame k) (ga k) (Formalism.L2.PjFree.laU U a n k)
    (wtOf (U.X k₀) Dc.hr Dc.k Dc.k' n) D.grp l.M ((C k)⁻¹ • P k) (hset k).1
    (fun τ i => by
      rw [Dc.wt_eq]
      simp only [wtX, Formalism.L2.PjFree.laU, (hsame k).p0])
    (fun g' hg' => ⟨((hgrp g').1 hg').1, fun hfix => (hmu1 _ (hset k).2.1 g' hg' hfix).2⟩)
    (hpr k) (hchi k) (isBddSec_of_mem_holSub U.X _ P hP1 k _)
  have hM2 : 0 < d.l₂.M := lt_of_lt_of_le (by norm_num) d.l₂.three_le
  have hMm : ((2 * bad * d.l₂.M : ℕ) : 𝓞 E) ∈ D.𝔪 := by
    rw [hD.m, Nat.cast_mul]
    refine Ideal.mul_mem_left _ _ ?_
    have h1 : (d.l₂.M : 𝓞 E) ∈ d.l₂.Mb * d.l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [d.l₂.prod]
      exact Ideal.mem_span_singleton_self _
    unfold Mfr
    exact (Submodule.mem_inf.1 (Ideal.mul_le_inf h1)).2
  obtain ⟨m, Λ, Pj, hΛ, hQ⟩ := GlobalTheory.T.stableForms_eq_sum_thetaSeries_freeLowerRows E r (U.X k₀) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hev hbig D hn
    (2 * bad * d.l₂.M) (Mfr l) (Jd d) (by positivity) hMm hD.prod hD.cop v₀ hv₀ mu hmu Dc.k Dc.k' U.Comp
    (fun k => mapL (ga k) (U.X k).Λ) _ (fun k => (hset k).2.1) hsep
    (fun k g' hg' hfix => (hmu1 _ (hset k).2.1 g' hg' hfix).1) (fun k => (hpull k).1)
  have hgl := fun j => GlobalTheory.Dict.GenLatCmp.genLat_vset E n (Λ j)
  have hg1 := fun j => (hgl j).1 bad d.l₂.M hbad d.l₂.odd (hΛ j).1
  choose N hN using fun j => (hg1 j).2.2.2
  have hV : ∀ j, Λ j ∈ Vset E n d.l₂.M := fun j => (hgl j).2.2.1 _ _ (Dvd.intro_left _ rfl) (hΛ j).1
  choose mj t R hR hPj using fun j => GlobalTheory.T.harmonicRowHighest_eq_span_integral_harmonic E H Dw l c σ r W.g Dw.p n (U.X k₀) a Dc (Λ j) (N j)
    (hN j).1.pos ((hN j).2.2.trans inf_le_left) (Pj j) (hΛ j).2
  choose f hf hfr using fun j i => (htot ⟨Λ j⟩ (N j) x0 (R j i) (hg1 j).1 (hg1 j).2.1 (hg1 j).2.2.1 (hN j)
    (hadm _) (hR j i)).2
  have hPe : P = ∑ j, ∑ i, (t j i * (u (Λ j) (N j))⁻¹) • Formalism.L2.PjFree.rdU U (f j i) := by
    funext k x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hx : x ∈ (U.X k).dom
    · obtain ⟨hx1, hx2⟩ := (hpull k).2 x hx
      have e1 := hQ k _ hx1
      rw [hx2, Pi.smul_apply, smul_eq_mul, inv_mul_eq_iff_eq_mul₀ (hC k)] at e1
      rw [e1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hPj j, theta_sum_smul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hrd k (Λ j) (hV j) (N j) (hN j) (R j i) (hR j i).1 (f j i) (hf j i) (hfr j i) x hx]
      have := hu (Λ j) (hV j) (N j) (hN j)
      field_simp
    · rw [hP0 k x hx]
      refine (Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => ?_).symm
      have : Formalism.L2.PjFree.rdU U (f j i) k x = 0 := dif_neg hx
      rw [this, mul_zero]
  rw [hPe]
  refine Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨f j i, ⟨hf j i, ⟨Λ j⟩, N j, x0, R j i, (hg1 j).1, (hg1 j).2.1, (hg1 j).2.2.1, hN j,
    hadm _, hR j i, hfr j i⟩, rfl⟩

end GlobalTheory.LargeCover
end
