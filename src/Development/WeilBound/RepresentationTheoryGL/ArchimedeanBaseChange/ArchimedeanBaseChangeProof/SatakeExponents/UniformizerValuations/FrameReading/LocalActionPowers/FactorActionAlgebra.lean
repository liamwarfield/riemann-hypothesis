module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.Pfmpow
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.RStabApply
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PPositions
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.DoubleSumFinprodFactor
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PGrowth
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.IntegrableCut
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexNeZeroOfOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintConstMul
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.BlkGrowth

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairMaximalCompactOpenCompact
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA GlobalTheory.CompanionTheory.ActTr
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.FactorAction

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def fHm (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) : Hf E a b →* H E a b :=
  (finGL E a).prodMap (finGL E b)

def epsS {S : Set (Pl E)} (a b : ℕ) : ∀ i : Slot S, GLw a i.pl × GLw b i.pl →* Hf E a b
  | .inl w => (locGL E a w.1).prodMap (locGL E b w.1)
  | .inr w => ((thF E a).comp (locGL E a w.1)).prodMap ((thF E b).comp (locGL E b w.1))

def selS {S : Set (Pl E)} (φ₁ φ₂ : ∀ w : Pl E, LF a b w) : ∀ i : Slot S, LF a b i.pl
  | .inl w => φ₁ w.1
  | .inr w => φ₂ w.1

theorem continuous_thF (n : ℕ) : Continuous (thF E n) :=
  GlobalTheory.ThetaPull.continuous_thetaGL _ (continuous_conjFin _)

theorem continuous_loc (n : ℕ) (w : Pl E) : Continuous (locGL E n w) :=
  GlobalTheory.EulerTw.continuous_locGL_spl E n w

theorem continuous_epsS {S : Set (Pl E)} (i : Slot S) : Continuous (epsS a b i) := by
  rcases i with w | w
  · exact (continuous_loc a w.1).prodMap (continuous_loc b w.1)
  · exact ((continuous_thF a).comp (continuous_loc a w.1)).prodMap ((continuous_thF b).comp (continuous_loc b w.1))

theorem embT_prod (w : Pl E) : (embT a w).prodMap (embT b w) =
    (fHm E a b).comp (((thF E a).comp (locGL E a w)).prodMap ((thF E b).comp (locGL E b w))) := by
  refine MonoidHom.ext fun m => Prod.ext ?_ ?_
  · exact GlobalTheory.ThetaPull.thetaA_finGL _
  · exact GlobalTheory.ThetaPull.thetaA_finGL _

theorem actS_eq {S : Set (Pl E)} (φ₁ φ₂ : ∀ w : Pl E, LF a b w) (i : Slot S) (G : H E a b → ℂ) :
    actS φ₁ φ₂ i G = act ((fHm E a b).comp (epsS a b i)) (K2 a b i.pl) (selS φ₁ φ₂ i) G := by
  rcases i with w | w
  · rfl
  · show act ((embT a w.1).prodMap (embT b w.1)) (K2 a b w.1) (φ₂ w.1) G = _
    rw [embT_prod]
    rfl

theorem pair_maximal_compact_open_compact (w : Pl E) : IsCompact (K2 a b w : Set (GLw a w × GLw b w)) ∧ IsOpen (K2 a b w : Set (GLw a w × GLw b w)) :=
  ⟨(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2,
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1⟩

theorem hecke_of_test {φ : ∀ w : Pl E, LF a b w} (h : IsTestP φ) (w : Pl E) :
    ∃ A : Subgroup (GLw a w × GLw b w), IsOpen (A : Set (GLw a w × GLw b w)) ∧ IsHecke A (φ w) := by
  obtain ⟨K₁, K₂, h₁, h₂, h₃⟩ := h
  exact ⟨(K₁ w).prod (K₂ w), (h₁.1 w).1.prod (h₂.1 w).1, h₃.1 w⟩

theorem hecke_sel {S : Set (Pl E)} {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂) (i : Slot S) :
    ∃ A : Subgroup (GLw a i.pl × GLw b i.pl), IsOpen (A : Set (GLw a i.pl × GLw b i.pl)) ∧ IsHecke A (selS φ₁ φ₂ i) := by
  rcases i with w | w
  · exact hecke_of_test h₁ w.1
  · exact hecke_of_test h₂ w.1

theorem locGL_comm {n : ℕ} {w w' : Pl E} (h : w ≠ w') (g : GLw n w) (g' : GLw n w') :
    locGL E n w g * locGL E n w' g' = locGL E n w' g' * locGL E n w g := by
  have key : ∀ v, GeneralLinearGroup.map (pLoc E v) (locGL E n w g * locGL E n w' g') =
      GeneralLinearGroup.map (pLoc E v) (locGL E n w' g' * locGL E n w g) := fun v => by
    rw [map_mul, map_mul]
    by_cases hv : v = w
    · subst hv
      rw [pLoc_locGL_of_ne h g', mul_one, one_mul]
    · rw [pLoc_locGL_of_ne hv g, mul_one, one_mul]
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v => ?_)
  exact congrArg (fun u : GL (Fin n) (v.adicCompletion E) => u.val i j) (key v)

theorem thF_loc {n : ℕ} {w u : Pl E} (h : w = GlobalTheory.ThetaSatake.cw u) (g : GLw n w) :
    ∃ g₀ : GLw n u, thF E n (locGL E n w g) = locGL E n u g₀ := by
  subst h
  exact ⟨_, GlobalTheory.ThetaSatake.theta_locGL u g⟩

theorem cw_cw (w : Pl E) : w = GlobalTheory.ThetaSatake.cw (GlobalTheory.ThetaSatake.cw w) :=
  (GlobalTheory.ThetaPull.conjSrc_conjSrc w).symm

theorem comm_WT {n : ℕ} {w w' : Pl E} (h : w ≠ GlobalTheory.ThetaSatake.cw w') (g : GLw n w) (g' : GLw n w') :
    locGL E n w g * thF E n (locGL E n w' g') = thF E n (locGL E n w' g') * locGL E n w g := by
  obtain ⟨g₀, e⟩ := thF_loc (cw_cw w') g'
  rw [e]
  exact locGL_comm h g g₀

theorem comm_TT {n : ℕ} {w w' : Pl E} (h : GlobalTheory.ThetaSatake.cw w ≠ GlobalTheory.ThetaSatake.cw w') (g : GLw n w) (g' : GLw n w') :
    thF E n (locGL E n w g) * thF E n (locGL E n w' g') = thF E n (locGL E n w' g') * thF E n (locGL E n w g) := by
  obtain ⟨g₀, e⟩ := thF_loc (cw_cw w) g
  obtain ⟨g₁, e'⟩ := thF_loc (cw_cw w') g'
  rw [e, e']
  exact locGL_comm h g₀ g₁

theorem epsS_comm {S : Set (Pl E)} (hS : IsSection S) {i j : Slot S} (hij : i ≠ j)
    (x : GLw a i.pl × GLw b i.pl) (y : GLw a j.pl × GLw b j.pl) :
    epsS a b i x * epsS a b j y = epsS a b j y * epsS a b i x := by
  rcases i with w | w <;> rcases j with w' | w'
  · have hne : w.1 ≠ w'.1 := fun e => hij (congrArg Sum.inl (Subtype.ext e))
    exact Prod.ext (locGL_comm hne _ _) (locGL_comm hne _ _)
  · have hne : w.1 ≠ GlobalTheory.ThetaSatake.cw w'.1 := fun e =>
      GlobalTheory.CompanionTheory.SuppFinTw.conj_not_mem hS w'.2.1 w'.2.2 (show GlobalTheory.ThetaSatake.cw w'.1 ∈ S from e ▸ w.2)
    exact Prod.ext (comm_WT hne _ _) (comm_WT hne _ _)
  · have hne : w'.1 ≠ GlobalTheory.ThetaSatake.cw w.1 := fun e =>
      GlobalTheory.CompanionTheory.SuppFinTw.conj_not_mem hS w.2.1 w.2.2 (show GlobalTheory.ThetaSatake.cw w.1 ∈ S from e ▸ w'.2)
    exact Prod.ext (comm_WT hne _ _).symm (comm_WT hne _ _).symm
  · have hne : GlobalTheory.ThetaSatake.cw w.1 ≠ GlobalTheory.ThetaSatake.cw w'.1 := fun e =>
      hij (congrArg Sum.inr (Subtype.ext ((cw_cw w.1).trans ((congrArg GlobalTheory.ThetaSatake.cw e).trans (cw_cw w'.1).symm))))
    exact Prod.ext (comm_TT hne _ _) (comm_TT hne _ _)

theorem selS_conv {S : Set (Pl E)} (φ₁ φ₂ ψ₁ ψ₂ : ∀ w : Pl E, LF a b w) (i : Slot S) :
    selS (fun w => PositivityTheory.Rg.BcN.F2.mconv (φ₁ w) (ψ₁ w)) (fun w => PositivityTheory.Rg.BcN.F2.mconv (φ₂ w) (ψ₂ w)) i =
      fun m => hint (K2 a b i.pl) fun m' => selS φ₁ φ₂ i m' * selS ψ₁ ψ₂ i (m'⁻¹ * m) := by
  rcases i with w | w <;> rfl

theorem actAlg : ActAlg := by
  intro E _ _ _ a b S hS φ₁ φ₂ ψ₁ ψ₂ hφ₁ hφ₂ hψ₁ hψ₂ G G' hG hG' i j
  have hGl : Lev (fHm E a b) G := hG
  have hGl' : Lev (fHm E a b) G' := hG'
  obtain ⟨hK, hKo⟩ := pair_maximal_compact_open_compact (a := a) (b := b) i.pl
  obtain ⟨hKj, hKoj⟩ := pair_maximal_compact_open_compact (a := a) (b := b) j.pl
  obtain ⟨A, hA, hf⟩ := hecke_sel (S := S) hφ₁ hφ₂ i
  obtain ⟨B, hB, hg⟩ := hecke_sel (S := S) hψ₁ hψ₂ i
  obtain ⟨B', hB', hg'⟩ := hecke_sel (S := S) hψ₁ hψ₂ j
  have ci := continuous_epsS (a := a) (b := b) i
  have cj := continuous_epsS (a := a) (b := b) j
  refine ⟨?_, fun c => ?_, fun hij => ?_, ?_⟩
  · rw [actS_eq]
    exact act_lev ci hK hKo hA hf hGl
  · simp only [actS_eq]
    exact act_add hK hKo hA hf (sm_of_lev ci hGl) (sm_of_lev ci hGl') c
  · simp only [actS_eq]
    refine act_comm hK hKo hA hKj hKoj hB' hf hg' (sm_of_lev ci hGl) (sm_of_lev cj hGl) fun x y => ?_
    simp only [MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul, epsS_comm hS hij]
  · simp only [actS_eq]
    rw [selS_conv]
    exact act_conv hK hKo hA hB hf hg (sm_of_lev ci hGl)

end GlobalTheory.CompanionTheory.FactorAction

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpenLeIsCompact
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem relIndex_ne_zero_of_isOpen_le_isCompact {H : Type} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (K U : Subgroup H) (hK : IsCompact (K : Set H))
    (hU : IsOpen (U : Set H)) (_hUK : U ≤ K) : U.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hO : IsOpen ((U.subgroupOf K : Subgroup K) : Set K) :=
    hU.preimage continuous_subtype_val
  haveI : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hO
  exact Subgroup.index_ne_zero_of_finite

end GlobalTheory
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.Psmall
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA.Psmall

section Generic

variable {P X : Type} [Group P] [Group X]

theorem hint_smul (K : Subgroup P) (c : ℂ) (v : P → ℂ) : hint K (fun m => c * v m) = c * hint K v := by
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul]
    exact GlobalTheory.CompanionTheory.FamClP.hint_zero K
  · have hst : rStab (fun m => c * v m) = rStab v := by
      ext r
      show (∀ x, c * v (x * r) = c * v x) ↔ ∀ x, v (x * r) = v x
      exact forall_congr' fun x => mul_right_inj' hc
    unfold hint
    rw [hst, show (∑ᶠ q : P ⧸ (rStab v ⊓ K), c * v q.out) = c * ∑ᶠ q : P ⧸ (rStab v ⊓ K), v q.out from
      (smul_finsum c _).symm]
    ring

theorem act_left (K L : Subgroup P) (c : ℂ) (φ : P →* X) (G : X → ℂ) (z : X) (l : P) (hl : l ∈ L) :
    hint K (fun m => (L : Set P).indicator (fun _ => c) m * G (z * φ l * φ m)) =
      hint K (fun m => (L : Set P).indicator (fun _ => c) m * G (z * φ m)) := by
  rw [← GlobalTheory.CompanionTheory.FamClP.hint_left K (fun m => (L : Set P).indicator (fun _ => c) m * G (z * φ m)) l]
  congr 1
  funext m
  have hmem : l * m ∈ L ↔ m ∈ L :=
    ⟨fun h => by simpa using L.mul_mem (L.inv_mem hl) h, fun h => L.mul_mem hl h⟩
  simp only [Set.indicator_apply, SetLike.mem_coe, hmem, map_mul, mul_assoc]

theorem idem_fix_iff (K L : Subgroup P) (hLK : L ≤ K) (hfin : L.relIndex K ≠ 0) (φ : P →* X) (G : X → ℂ) :
    (fun z => hint K (fun m => (L : Set P).indicator (fun _ => ((L.relIndex K : ℕ) : ℂ)) m * G (z * φ m))) = G ↔
      ∀ l ∈ L, ∀ z, G (z * φ l) = G z := by
  constructor
  · intro h l hl z
    have h1 := congrFun h (z * φ l)
    have h2 := congrFun h z
    rw [← h1, ← h2]
    exact act_left K L _ φ G z l hl
  · intro h
    funext z
    have hu : (fun m => (L : Set P).indicator (fun _ => ((L.relIndex K : ℕ) : ℂ)) m * G (z * φ m)) =
        fun m => (L : Set P).indicator (fun _ => ((L.relIndex K : ℕ) : ℂ) * G z) m := by
      funext m
      by_cases hm : m ∈ L
      · simp [hm, h m hm z]
      · simp [hm]
    rw [hu]
    have hst : L ≤ rStab (fun m => (L : Set P).indicator (fun _ => ((L.relIndex K : ℕ) : ℂ) * G z) m) := by
      intro l hl x
      have : x * l ∈ L ↔ x ∈ L :=
        ⟨fun h' => by simpa using L.mul_mem h' (L.inv_mem hl), fun h' => L.mul_mem h' hl⟩
      simp only [Set.indicator_apply, SetLike.mem_coe, this]
    rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level P K L _ hLK hst hfin]
    have hone : ((((1 : P) : P ⧸ L)).out) ∈ L := by
      have := QuotientGroup.eq.1 (QuotientGroup.out_eq' ((1 : P) : P ⧸ L))
      simpa using this
    rw [finsum_eq_single _ ((1 : P) : P ⧸ L)]
    · simp only [Set.indicator_apply, SetLike.mem_coe, hone, if_true]
      have hc : ((L.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hfin
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    · intro q hq
      have : q.out ∉ L := by
        intro hin
        apply hq
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 (by simpa using hin)
      simp [this]

end Generic

section Generic2

variable {P X : Type} [Group P] [Group X]

theorem hecke_eq [TopologicalSpace P] [IsTopologicalGroup P] (K : Subgroup P) (hK : IsOpen (K : Set P)) (φ : P →* X)
    (f : P → ℂ) (G : X → ℂ) (hf : HasCompactSupport f) (hfK : ∀ k ∈ K, ∀ g, f (g * k) = f g)
    (hG : ∀ k ∈ K, ∀ z, G (z * φ k) = G z) :
    (fun z => hint K (fun m => f m * G (z * φ m))) = heckeVec ((rightReg ℂ X ℂ).comp φ) K f G := by
  funext z
  have hst : K ≤ rStab (fun m => f m * G (z * φ m)) := by
    intro k hk x
    show f (x * k) * G (z * φ (x * k)) = f x * G (z * φ x)
    rw [hfK k hk, map_mul, ← mul_assoc, hG k hk]
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level P K K _ le_rfl hst (by simp), Subgroup.relIndex_self, Nat.cast_one, inv_one,
    one_mul]
  have hfin : (Function.support fun c : P ⧸ K => f c.out • ((rightReg ℂ X ℂ).comp φ) c.out G).Finite :=
    (GlobalTheory.TwTrLin.finite_out_support hK hf).subset (Function.support_smul_subset_left (fun c : P ⧸ K => f c.out)
      (fun c : P ⧸ K => ((rightReg ℂ X ℂ).comp φ) c.out G))
  unfold heckeVec
  rw [finsum_apply hfin]
  rfl

end Generic2

end PositivityTheory.Rg.BcB.F.FA.Psmall

namespace PositivityTheory.Rg.BcB.F.FA

open Psmall in
theorem actIdem_holds : ActIdem := by
  intro E _ _ _ a b w L G hL hLK _
  have hK : IsCompact ((K2 a b w : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_prod]
    exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2
  have hfin : L.relIndex (K2 a b w) ≠ 0 := GlobalTheory.relIndex_ne_zero_of_isOpen_le_isCompact _ _ hK hL hLK
  constructor
  · rw [GlobalTheory.TwTrLin.mem_fixed_iff]
    exact (idem_fix_iff (K2 a b w) L hLK hfin ((embW a w).prodMap (embW b w)) G).trans
      ⟨fun h l hl => funext (h l hl), fun h l hl z => congrFun (h l hl) z⟩
  · rw [GlobalTheory.TwTrLin.mem_fixed_iff]
    exact (idem_fix_iff (K2 a b w) L hLK hfin ((embT a w).prodMap (embT b w)) G).trans
      ⟨fun h l hl => funext (h l hl), fun h l hl z => congrFun (h l hl) z⟩

end PositivityTheory.Rg.BcB.F.FA

namespace PositivityTheory.Rg.BcB.F.Tail

open PositivityTheory.Rg.BcB.F.FA.Psmall in
theorem actHecke_holds : ActHecke := by
  intro E _ _ _ a b w f G hf hfK
  have hK : IsOpen ((K2 a b w : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_prod]
    exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1
  constructor
  · intro hG
    rw [GlobalTheory.TwTrLin.mem_fixed_iff] at hG
    exact hecke_eq (K2 a b w) hK ((embW a w).prodMap (embW b w)) f G hf hfK fun k hk z => congrFun (hG k hk) z
  · intro hG
    rw [GlobalTheory.TwTrLin.mem_fixed_iff] at hG
    exact hecke_eq (K2 a b w) hK ((embT a w).prodMap (embT b w)) f G hf hfK fun k hk z => congrFun (hG k hk) z

namespace Psmall

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem actP_smul_fun (w : Pl E) (c : ℂ) (u : GLw a w × GLw b w → ℂ) (G : H E a b → ℂ) :
    actP w (c • u) G = c • actP w u G := by
  funext z
  show hint _ (fun m => (c • u) m * _) = c * hint _ _
  rw [← PositivityTheory.Rg.BcB.F.FA.Psmall.hint_smul]
  congr 1
  funext m
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem actP_smul_vec (w : Pl E) (c : ℂ) (u : GLw a w × GLw b w → ℂ) (G : H E a b → ℂ) :
    actP w u (c • G) = c • actP w u G := by
  funext z
  show hint _ (fun m => u m * pairRt a b w m (c • G) z) = c * hint _ _
  rw [← PositivityTheory.Rg.BcB.F.FA.Psmall.hint_smul]
  congr 1
  funext m
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem actP_zero (w : Pl E) (G : H E a b → ℂ) : actP w (0 : GLw a w × GLw b w → ℂ) G = 0 := by
  funext z
  show hint _ (fun m => (0 : GLw a w × GLw b w → ℂ) m * _) = 0
  simp only [Pi.zero_apply, zero_mul]
  exact GlobalTheory.CompanionTheory.FamClP.hint_zero _

theorem locM_iter_smul (w : Pl E) {k : Type} [Fintype k] (c : ℂ) (M : k → k → GLw a w × GLw b w → ℂ)
    (G : k → H E a b → ℂ) (m : ℕ) :
    (locM w fun x y => c • M x y)^[m] G = c ^ m • (locM w M)^[m] G := by
  have h1 : ∀ Y : k → H E a b → ℂ, (locM w fun x y => c • M x y) Y = c • locM w M Y := by
    intro Y
    funext x
    simp only [locM, actP_smul_fun, Pi.smul_apply, Finset.smul_sum]
  have h2 : ∀ (d : ℂ) (Y : k → H E a b → ℂ), locM w M (d • Y) = d • locM w M Y := by
    intro d Y
    funext x
    simp only [locM, Pi.smul_apply, actP_smul_vec, Finset.smul_sum]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, h1, h2, smul_smul, pow_succ']

theorem locM_iter_diag (w : Pl E) {k : Type} [Fintype k] (q : k → GLw a w × GLw b w → ℂ)
    (G : k → H E a b → ℂ) (m : ℕ) (x : k) :
    (locM w fun x y => if x = y then q x else 0)^[m] G x = (actP w (q x))^[m] (G x) := by
  have h1 : ∀ (Y : k → H E a b → ℂ) (x : k), (locM w fun x y => if x = y then q x else 0) Y x = actP w (q x) (Y x) := by
    intro Y x
    show ∑ y, actP w (if x = y then q x else 0) (Y y) = _
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      rw [if_neg (Ne.symm hy), actP_zero]
    · intro h
      exact absurd (Finset.mem_univ x) h
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h1, ih]

end Psmall

open Psmall in
theorem locPow_holds : LocPow := by
  intro E _ _ _ a b w k _ U G m _ _
  constructor
  · intro c M hne h0
    apply hne
    rw [locM_iter_smul, h0, smul_zero]
  · intro q hne
    by_contra hall
    simp only [not_exists, not_not] at hall
    apply hne
    funext x
    rw [locM_iter_diag]
    exact hall x

end PositivityTheory.Rg.BcB.F.Tail
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.FmTermZero
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA

attribute [local instance] borelG borelF borelH

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {κ : Pl E → Type} [∀ w, Fintype (κ w)]
  {S : Set (Pl E)} {P : Finset (Pl E)} {B : Block E} {e : B.κ ≃ ∀ w : P, κ w}

theorem fm_term_zero (hP : (↑P : Set (Pl E)) ⊆ S) {L : LM κ B.a B.b} (hL : L.Ok P) (x z : B.κ) (w : P)
    (hw : L.m w.1 (e x w) (e z w) = 0) (G : H E B.a B.b → ℂ) (y : H E B.a B.b) :
    ∫ h, fm S P B e L x z h * G (y * finH h) ∂B.ν = 0 := by
  have h0 : ∀ h, finFn S (L.ent P (e x) (e z)) L.t h = 0 := by
    intro h
    by_contra hne
    apply (GlobalTheory.CompanionTheory.FinTestTw.factors_ne_zero (hL.1 _ _) hL.2 hne w.1 (hP w.2)).1
    simp only [LM.ent, dif_pos w.2]
    exact congrFun hw _
  simp [fm, h0]

theorem fm_term_act (hS : IsSection S) (hFC : FinConv) (hFA : FinAct) {L : LM κ B.a B.b} (hL : L.Ok P) (x z : B.κ)
    (i₀ : Slot S) (G : H E B.a B.b → ℂ) (hG : HasLev G)
    (hfix : ∀ i, i ≠ i₀ → actS (L.ent P (e x) (e z)) L.t i G = G) (y : H E B.a B.b) :
    ∫ h, fm S P B e L x z h * G (y * finH h) ∂B.ν = actS (L.ent P (e x) (e z)) L.t i₀ G y := by
  have hv : B.vol ≠ 0 := (hFC E B S hS).1
  have key := hFA E B S hS (L.ent P (e x) (e z)) L.t (hL.1 _ _) hL.2 G hG [i₀] (List.nodup_singleton _)
    (fun i hi => hfix i (by simpa using hi)) y
  simp only [List.foldr_cons, List.foldr_nil] at key
  simp only [fm, mul_assoc]
  rw [integral_const_mul, key, ← mul_assoc, inv_mul_cancel₀ hv, one_mul]

end

theorem fmAtP_holds : FmAtPOf := by
  intro hFC hFA E _ _ _ κ _ S P B e hS hP A L w₀ F hL hF hQ p x
  funext y
  set g : κ w₀ → B.κ := fun t => e.symm (Function.update (e x) w₀ t) with hg
  have hginj : Function.Injective g := by
    intro t t' h
    have := congrArg (fun z => e z w₀) h
    simpa [hg] using this
  have hterm : ∀ z : B.κ, ∫ h, fm S P B e L x z h * F (p, z) (y * finH h) ∂B.ν =
      ∑ t : κ w₀, if z = g t then actP w₀.1 (L.m w₀ (e x w₀) t) (F (p, g t)) y else 0 := by
    intro z
    by_cases hz : ∃ t, z = g t
    · obtain ⟨t, rfl⟩ := hz
      rw [Finset.sum_eq_single t (fun t' _ ht' => if_neg fun h => ht' (hginj h).symm) (by simp), if_pos rfl]
      have hez : e (g t) = Function.update (e x) w₀ t := by simp [hg]
      rw [fm_term_act hS hFC hFA hL x (g t) (Sum.inl ⟨w₀.1, hP w₀.2⟩) (F (p, g t)) (hF _) ?_ y]
      · simp only [actS, LM.ent]
        rw [hez]
        simp
      · intro i hi
        refine hQ.2 i hi p x (g t) fun w hw => ?_
        rw [hez]
        have hne : w ≠ w₀ := by
          rintro rfl
          exact hw (hP w.2) rfl
        rw [Function.update_of_ne hne]
    · rw [Finset.sum_eq_zero fun t _ => if_neg fun h => hz ⟨t, h⟩]
      have : ∃ w : P, w ≠ w₀ ∧ e x w ≠ e z w := by
        by_contra hall
        push Not at hall
        apply hz
        refine ⟨e z w₀, e.injective ?_⟩
        simp only [hg, Equiv.apply_symm_apply]
        funext w
        by_cases hw : w = w₀
        · subst hw; simp
        · rw [Function.update_of_ne hw]; exact (hall w hw).symm
      obtain ⟨w, hw, hne⟩ := this
      refine fm_term_zero hP hL x z w ?_ _ y
      refine hQ.1 w.1 w.2 (fun h hh => ?_) _ _ hne
      apply hw
      apply Subtype.ext
      have := congrArg Slot.pl hh
      simpa [Slot.pl] using this.symm
  show ∑ z, ∫ h, fm S P B e L x z h * F (p, z) (y * finH h) ∂B.ν = _
  rw [Finset.sum_congr rfl fun z _ => hterm z, Finset.sum_comm]
  simp [Finset.sum_ite_eq', hg]

theorem fmOff_holds : FmOffOf := by
  intro hFC hFA E _ _ _ κ _ S P B e hS hP A L i₀ F hL hF hoff hQ p x
  funext y
  show ∑ z, ∫ h, fm S P B e L x z h * F (p, z) (y * finH h) ∂B.ν = _
  rw [Finset.sum_eq_single x]
  · rw [fm_term_act hS hFC hFA hL x x i₀ (F (p, x)) (hF _) (fun i hi => hQ.2 i hi p x x fun _ _ => rfl) y]
    rcases i₀ with ⟨w, hw⟩ | ⟨w, hw⟩
    · have hwP : w ∉ P := fun h => hoff w h hw rfl
      simp [actS, LM.ent, dif_neg hwP]
    · rfl
  · intro z _ hz
    have : ∃ w : P, e x w ≠ e z w := by
      by_contra hall
      push Not at hall
      exact hz (e.injective (funext hall)).symm
    obtain ⟨w, hne⟩ := this
    exact fm_term_zero hP hL x z w (hQ.1 w.1 w.2 (hoff w.1 w.2) _ _ hne) _ y
  · simp

end PositivityTheory.Rg.BcB.F.FA

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.Pfmone
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA

section Gen

set_option linter.unusedSectionVars false

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [FirstCountableTopology Γ] [LocallyCompactSpace Γ] [MeasurableSpace Γ] [BorelSpace Γ]
  (ν : Measure Γ) [ν.IsHaarMeasure]

theorem cont_of_rinv {f : Γ → ℂ} {U : Subgroup Γ} (hU : IsOpen (U : Set Γ)) (hf : ∀ u ∈ U, ∀ g, f (g * u) = f g) :
    Continuous f := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  refine (continuousAt_const (y := f g)).congr ?_
  have hm : {y : Γ | g⁻¹ * y ∈ U} ∈ 𝓝 g :=
    (hU.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [U.one_mem])
  filter_upwards [hm] with y hy
  have := hf _ hy g
  rw [mul_inv_cancel_left] at this
  exact this.symm

theorem cont_convL {φ₁ φ₂ : Γ → ℂ} (h₁ : Continuous φ₁) (s₁ : HasCompactSupport φ₁) (h₂ : Continuous φ₂) :
    Continuous fun g => ∫ h, φ₁ h * φ₂ (h⁻¹ * g) ∂ν := by
  have e : (fun g => ∫ h, φ₁ h * φ₂ (h⁻¹ * g) ∂ν) = fun g => ∫ h in tsupport φ₁, φ₁ h * φ₂ (h⁻¹ * g) ∂ν := by
    funext g
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun h hh => ?_).symm
    rw [image_eq_zero_of_notMem_tsupport hh, zero_mul]
  rw [e]
  refine continuous_parametric_integral_of_continuous ?_ s₁.isCompact
  exact (h₁.comp continuous_snd).mul (h₂.comp (continuous_snd.inv.mul continuous_fst))

theorem supp_convL {φ₁ φ₂ : Γ → ℂ} (s₁ : HasCompactSupport φ₁) (s₂ : HasCompactSupport φ₂) :
    HasCompactSupport fun g => ∫ h, φ₁ h * φ₂ (h⁻¹ * g) ∂ν := by
  refine HasCompactSupport.intro (s₁.isCompact.mul s₂.isCompact) fun g hg => ?_
  have : ∀ h, φ₁ h * φ₂ (h⁻¹ * g) = 0 := by
    intro h
    by_cases h1 : h ∈ tsupport φ₁
    · have h2 : h⁻¹ * g ∉ tsupport φ₂ := fun h2 => hg (Set.mem_mul.2 ⟨h, h1, h⁻¹ * g, h2, mul_inv_cancel_left h g⟩)
      rw [image_eq_zero_of_notMem_tsupport h2, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul]
  simp [this]

theorem cont_convR {φ₂ f : Γ → ℂ} (h₂ : Continuous φ₂) (s₂ : HasCompactSupport φ₂) (hf : Continuous f) :
    Continuous fun h => ∫ k, φ₂ k * f (h * k) ∂ν := by
  have e : (fun h => ∫ k, φ₂ k * f (h * k) ∂ν) = fun h => ∫ k in tsupport φ₂, φ₂ k * f (h * k) ∂ν := by
    funext h
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun k hk => ?_).symm
    rw [image_eq_zero_of_notMem_tsupport hk, zero_mul]
  rw [e]
  refine continuous_parametric_integral_of_continuous ?_ s₂.isCompact
  exact (h₂.comp continuous_snd).mul (hf.comp (continuous_fst.mul continuous_snd))

theorem int_L {φ₁ φ₂ f : Γ → ℂ} (h₁ : Continuous φ₁) (s₁ : HasCompactSupport φ₁) (h₂ : Continuous φ₂)
    (s₂ : HasCompactSupport φ₂) (hf : Continuous f) :
    Integrable (fun g => (∫ h, φ₁ h * φ₂ (h⁻¹ * g) ∂ν) * f g) ν :=
  ((cont_convL ν h₁ s₁ h₂).mul hf).integrable_of_hasCompactSupport ((supp_convL ν s₁ s₂).mul_right)

theorem int_R {φ₁ φ₂ f : Γ → ℂ} (h₁ : Continuous φ₁) (s₁ : HasCompactSupport φ₁) (h₂ : Continuous φ₂)
    (s₂ : HasCompactSupport φ₂) (hf : Continuous f) :
    Integrable (fun h => φ₁ h * ∫ k, φ₂ k * f (h * k) ∂ν) ν :=
  (h₁.mul (cont_convR ν h₂ s₂ hf)).integrable_of_hasCompactSupport s₁.mul_right

theorem swap_key {φ₁ φ₂ f : Γ → ℂ} (h₁ : Continuous φ₁) (s₁ : HasCompactSupport φ₁) (h₂ : Continuous φ₂)
    (s₂ : HasCompactSupport φ₂) (hf : Continuous f) :
    ∫ g, (∫ h, φ₁ h * φ₂ (h⁻¹ * g) ∂ν) * f g ∂ν = ∫ h, φ₁ h * ∫ k, φ₂ k * f (h * k) ∂ν ∂ν := by
  have hc : Continuous (Function.uncurry fun g h : Γ => φ₁ h * φ₂ (h⁻¹ * g) * f g) :=
    ((h₁.comp continuous_snd).mul (h₂.comp (continuous_snd.inv.mul continuous_fst))).mul (hf.comp continuous_fst)
  have hs : HasCompactSupport (Function.uncurry fun g h : Γ => φ₁ h * φ₂ (h⁻¹ * g) * f g) := by
    refine HasCompactSupport.intro ((s₁.isCompact.mul s₂.isCompact).prod s₁.isCompact) fun p hp => ?_
    show φ₁ p.2 * φ₂ (p.2⁻¹ * p.1) * f p.1 = 0
    by_cases h1 : p.2 ∈ tsupport φ₁
    · have h2 : p.2⁻¹ * p.1 ∉ tsupport φ₂ := fun h2 =>
        hp ⟨Set.mem_mul.2 ⟨p.2, h1, p.2⁻¹ * p.1, h2, mul_inv_cancel_left p.2 p.1⟩, h1⟩
      rw [image_eq_zero_of_notMem_tsupport h2, mul_zero, zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul, zero_mul]
  calc ∫ g, (∫ h, φ₁ h * φ₂ (h⁻¹ * g) ∂ν) * f g ∂ν
      = ∫ g, ∫ h, φ₁ h * φ₂ (h⁻¹ * g) * f g ∂ν ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        exact (integral_mul_const _ _).symm
    _ = ∫ h, ∫ g, φ₁ h * φ₂ (h⁻¹ * g) * f g ∂ν ∂ν := integral_integral_swap_of_hasCompactSupport hc hs
    _ = ∫ h, φ₁ h * ∫ k, φ₂ k * f (h * k) ∂ν ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun h => ?_)
        have e1 := integral_mul_left_eq_self (μ := ν) (fun g => φ₂ (h⁻¹ * g) * f g) h
        simp only [inv_mul_cancel_left] at e1
        show ∫ g, φ₁ h * φ₂ (h⁻¹ * g) * f g ∂ν = φ₁ h * ∫ k, φ₂ k * f (h * k) ∂ν
        rw [e1, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        show φ₁ h * φ₂ (h⁻¹ * g) * f g = φ₁ h * (φ₂ (h⁻¹ * g) * f g)
        ring

end Gen

theorem finH_mul' {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (g h : Hf E a b) :
    finH (g * h) = finH g * finH h := by
  simp [finH, map_mul]

attribute [local instance] borelG borelF borelH

theorem convMul_holds : Tail.ConvMul := by
  set_option synthInstance.maxHeartbeats 400000 in
  intro E _ _ _ B A ψ ψ' U F hψ hψ' hU hF
  have := B.hν
  have : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩
  refine ⟨?_, ?_⟩
  · funext i X
    obtain ⟨p, x₀⟩ := i
    have hfc : ∀ z, Continuous fun g => F (p, z) (X * finH g) := by
      intro z
      refine cont_of_rinv hU fun u hu g => ?_
      rw [finH_mul', ← mul_assoc, hF _ u hu]
    simp only [convF, mulF]
    calc ∑ z, ∫ g, (∑ w, ∫ h, ψ x₀ w h * ψ' w z (h⁻¹ * g) ∂B.ν) * F (p, z) (X * finH g) ∂B.ν
        = ∑ z, ∑ w, ∫ g, (∫ h, ψ x₀ w h * ψ' w z (h⁻¹ * g) ∂B.ν) * F (p, z) (X * finH g) ∂B.ν := by
          refine Finset.sum_congr rfl fun z _ => ?_
          simp_rw [Finset.sum_mul]
          exact integral_finsetSum _ fun w _ =>
            int_L B.ν (hψ x₀ w).1 (hψ x₀ w).2 (hψ' w z).1 (hψ' w z).2 (hfc z)
      _ = ∑ w, ∑ z, ∫ g, (∫ h, ψ x₀ w h * ψ' w z (h⁻¹ * g) ∂B.ν) * F (p, z) (X * finH g) ∂B.ν :=
          Finset.sum_comm
      _ = ∑ w, ∑ z, ∫ h, ψ x₀ w h * ∫ k, ψ' w z k * F (p, z) (X * finH h * finH k) ∂B.ν ∂B.ν := by
          refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun z _ => ?_
          rw [swap_key B.ν (hψ x₀ w).1 (hψ x₀ w).2 (hψ' w z).1 (hψ' w z).2 (hfc z)]
          simp only [finH_mul', mul_assoc]
      _ = ∑ w, ∫ h, ψ x₀ w h * ∑ z, ∫ k, ψ' w z k * F (p, z) (X * finH h * finH k) ∂B.ν ∂B.ν := by
          refine Finset.sum_congr rfl fun w _ => ?_
          simp_rw [Finset.mul_sum]
          refine (integral_finsetSum _ fun z _ => ?_).symm
          have := int_R B.ν (hψ x₀ w).1 (hψ x₀ w).2 (hψ' w z).1 (hψ' w z).2 (hfc z)
          simpa only [finH_mul', mul_assoc] using this
  · intro hψU i u hu x
    simp only [convF]
    refine Finset.sum_congr rfl fun z _ => ?_
    have e := integral_mul_left_eq_self (μ := B.ν) (fun k => ψ' i.2 z k * F (i.1, z) (x * finH k)) u
    simp only [hψU _ _ u hu, finH_mul', ← mul_assoc] at e
    exact e

theorem fmOneOf_holds : FmOneOf := by
  intro hOff hIdem E _ _ _ κ _ S P B e hS hP U₁ U₂ L A F w₀ hU₁ hU₂ hL hD hF hw₀
  have hLev : ∀ i, HasLev (F i) := fun i => (hF i).1

  have hxy : ∀ x y : B.κ, (∀ w : P, e x w = e y w) → x = y := fun x y h => e.injective (funext h)

  have hent : ∀ (x : B.κ) (w : Pl E), (w ∉ P → L.s w = idem (U₁ w)) → L.ent P (e x) (e x) w = idem (U₁ w) := by
    intro x w hw
    unfold LM.ent
    split_ifs with h
    · rw [hD w h]; simp
    · exact hw h
  have hP1 : ∀ (w : Pl E) (G : H E B.a B.b → ℂ), w ∈ S → HasLev G → G ∈ fixed (pairRt B.a B.b w) (U₁ w) →
      actP w (idem (U₁ w)) G = G := fun w G _ hG hfx =>
    ((hIdem E B.a B.b w (U₁ w) G (hU₁.1 w).1 (hU₁.1 w).2 hG).1).2 hfx
  have hT1 : ∀ (w : Pl E) (G : H E B.a B.b → ℂ), HasLev G → G ∈ fixed (pairRtT B.a B.b w) (U₂ w) →
      actT w (idem (U₂ w)) G = G := fun w G hG hfx =>
    ((hIdem E B.a B.b w (U₂ w) G (hU₂.1 w).1 (hU₂.1 w).2 hG).2).2 hfx
  refine ⟨fun hw₀P hs ht i => ?_, fun hsp hs ht i => ?_⟩
  · have hne : ∀ w ∈ P, ∀ h : w ∈ S, (Sum.inl ⟨w₀, hw₀⟩ : Slot S) ≠ Sum.inl ⟨w, h⟩ := by
      intro w hwP h heq
      have : w₀ = w := congrArg Subtype.val (Sum.inl_injective heq)
      exact hw₀P (this ▸ hwP)
    have hQ : Quiet S P B e L (Sum.inl ⟨w₀, hw₀⟩) F := by
      refine ⟨fun w hwP hw x y hxy' => ?_, fun j hj p x y hxe => ?_⟩
      · rw [hD w hwP, if_neg hxy']
      · have hx : x = y := hxy x y fun w => hxe w fun h => hne w.1 w.2 h
        subst hx
        rcases j with ⟨w, hwS⟩ | ⟨w, hwS, hwsp⟩
        · have hww : w ≠ w₀ := fun h => hj (by subst h; rfl)
          show actP w (L.ent P (e x) (e x) w) (F (p, x)) = F (p, x)
          rw [hent x w fun _ => hs w hww]
          exact hP1 w _ hwS (hLev _) ((hF _).2 w hwS).1
        · show actT w (L.t w) (F (p, x)) = F (p, x)
          rw [ht w]
          exact hT1 w _ (hLev _) (((hF _).2 w hwS).2 hwsp)
    obtain ⟨p, x⟩ := i
    exact hOff E κ S P B e hS hP A L (Sum.inl ⟨w₀, hw₀⟩) F hL hLev hne hQ p x
  · have hne : ∀ w ∈ P, ∀ h : w ∈ S, (Sum.inr ⟨w₀, hw₀, hsp⟩ : Slot S) ≠ Sum.inl ⟨w, h⟩ := by
      intro w _ h heq
      cases heq
    have hQ : Quiet S P B e L (Sum.inr ⟨w₀, hw₀, hsp⟩) F := by
      refine ⟨fun w hwP hw x y hxy' => ?_, fun j hj p x y hxe => ?_⟩
      · rw [hD w hwP, if_neg hxy']
      · have hx : x = y := hxy x y fun w => hxe w fun h => hne w.1 w.2 h
        subst hx
        rcases j with ⟨w, hwS⟩ | ⟨w, hwS, hwsp⟩
        · show actP w (L.ent P (e x) (e x) w) (F (p, x)) = F (p, x)
          rw [hent x w fun _ => hs w]
          exact hP1 w _ hwS (hLev _) ((hF _).2 w hwS).1
        · have hww : w ≠ w₀ := fun h => hj (by subst h; rfl)
          show actT w (L.t w) (F (p, x)) = F (p, x)
          rw [ht w hww]
          exact hT1 w _ (hLev _) (((hF _).2 w hwS).2 hwsp)
    obtain ⟨p, x⟩ := i
    exact hOff E κ S P B e hS hP A L (Sum.inr ⟨w₀, hw₀, hsp⟩) F hL hLev hne hQ p x

end PositivityTheory.Rg.BcB.F.FA

end
end

namespace PositivityTheory.Rg.BcB.F.FA

theorem position_action_algebra : ActAlg := GlobalTheory.CompanionTheory.FactorAction.actAlg

theorem finAct_of (h1 : IntHint) (h2 : Slots) (h3 : FinConv) : FinAct := GlobalTheory.CompanionTheory.FinActS.finActOf h1 h2 h3 position_action_algebra

theorem fmOne_of (h1 : IntHint) (h2 : Slots) (h3 : FinConv) : Tail.FmOne :=
  fmOneOf_holds (fmOff_holds h3 (finAct_of h1 h2 h3)) actIdem_holds

theorem fmPow_of (h1 : IntHint) (h2 : Slots) (h3 : FinConv) (h4 : FmAlg) : Tail.FmPow :=
  fmPowOf_holds h4 (fmAtP_holds h3 (finAct_of h1 h2 h3)) convMul_holds position_action_algebra actIdem_holds

end PositivityTheory.Rg.BcB.F.FA
