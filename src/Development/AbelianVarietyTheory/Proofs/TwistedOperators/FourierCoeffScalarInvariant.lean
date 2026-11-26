module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaAtEnlargePlaceIdempotentLatticeIndicator
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitThetaGridIsAdmissibleFlipTensor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeightedAverageHaarLifted
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLocalEqCompletedHomLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierCoeffScalarInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

namespace GlobalTheory.MovedKappaArith

theorem selfDualIntertwiner_baseVector_ne_zero {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} (hC : Crv D cc δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) {N N' : ℕ} {e0 : VC D N N' → ℂ} (he : oddE0 D cc δ t0 N N' e0)
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hL : SD D L) (hL' : SD D L') :
    Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) L L') e0 ≠ 0 := by
  have s0 := GlobalTheory.MovedVacuum.sd_stdL D N
  have s0' := GlobalTheory.MovedVacuum.sd_stdL D N'
  have k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := Or.inr ⟨_, _, s0, s0', rfl⟩
  have k1 : KLat D (tor0 D cc δ) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) L L') := Or.inr ⟨_, _, hL, hL', rfl⟩
  have huni := GlobalTheory.theta_translation_intertwiner_unitary D cc δ hC N N' _ _ k0 k1
  intro h
  exact GlobalTheory.TrueTheta.ne_zero_of_like hC ht s0 s0' he.2.2.2.1
    (by rw [← (huni e0 he.1).2.2.2, h, GlobalTheory.VacuumScalar.Iop_zero])

theorem applyAt0_monomial (D : D7) {N N' : ℕ} (α : Mono D N N') (G : VC D N N' → ℂ) :
    Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial α 1) G
      = (α.prod fun _ n => (n.factorial : ℂ)) * Formalism.MainNotions.TaylorLogMetric.taylor D G α := by
  classical
  unfold Formalism.MainNotions.GL3Theta.applyAt0
  rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton, MvPolynomial.coeff_monomial,
    if_pos rfl, one_mul]

end GlobalTheory.MovedKappaArith

namespace GlobalTheory.MovedKappaArith

end GlobalTheory.MovedKappaArith

namespace GlobalTheory.MovedKappaArith

end GlobalTheory.MovedKappaArith
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsFinOf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def locAt (B : Frames G) (t : T) (w : Pl D.host.E) (j : ℕ) (hj : j ≤ D.R.m) :
    GA D (G.V (.grid D.R.m j)) →* GL (Fin ((locGrid G t w).rank (D.R.m, j))) (Kw w) :=
  (inBasis (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, hj⟩) (B.β D.R.m j) w).comp (Lev.finE _)

theorem locAt_inf (B : Frames G) (t : T) (w : Pl D.host.E) (j : ℕ) (hj : j ≤ D.R.m) {a : GA D (G.V (.grid D.R.m j))}
    (ha : a ∈ GinfC _) : locAt B t w j hj a = 1 := by
  have h : Lev.finE (G.V (.grid D.R.m j)) a = 1 := by
    simp only [Lev.finE, GinfC, MonoidHom.mem_ker] at ha ⊢
    rw [MonoidHom.comp_apply, ha, map_one]
  simp only [locAt, MonoidHom.comp_apply, h, map_one]

theorem exists_isFinOf (V : HSp D) (g : GA D V) : ∃ b, GlobalTheory.RowVal.IsFinOf g b := by
  obtain ⟨-, -, -, ⟨e, he⟩, -⟩ := GlobalTheory.AdelicSplit.adelic_split D V
  obtain ⟨p, rfl⟩ := e.surjective g
  exact ⟨p.2, p.2.2, p.1, p.1.2, (he p).symm⟩

theorem elt_succ (t : T) (w : Pl D.host.E) (β : Cosets (G := locGrid G t w) one_le_sLen (givenLevel G t w))
    (i : Fin ((locGrid G t w).m - 2)) :
    (repsAt G t w).elt β ((locGrid G t w).m, i.1 + 1) = (repsAt G t w).rep i (β i) := by
  simp only [Reps.elt]
  rw [onColumn_apply]
  simp only [dif_pos i.2]

end GlobalTheory.RowRep

namespace GlobalTheory.RowRep
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem loc_rep (B : Frames G) (t : T) (s : ℤˣ) (β : CosFam G t) (w : locPl G t) (i : Fin ((locGrid G t w.1).m - 2))
    (hj : i.1 + 1 ≤ D.R.m) (r : GA D (G.V (.grid D.R.m (i.1 + 1))))
    (ρ : GL (Fin ((locGrid G t w.1).rank (D.R.m, i.1 + 1))) (Kw w.1)) (hρ : ρ = (repsAt G t w.1).rep i (β w i))
    (hr : (inBasis (rank_vertex G t w.1 (X := (D.R.m, i.1 + 1)) ⟨le_rfl, hj⟩) (B.β D.R.m (i.1 + 1)) w.1)
      (Lev.finE (G.V (.grid D.R.m (i.1 + 1))) r) =
      GlobalTheory.RowVal.sgnAt G t s w.1 (i.1 + 1) * (repsAt G t w.1).elt (β w) (D.R.m, i.1 + 1)) :
    locAt B t w.1 (i.1 + 1) hj r = GlobalTheory.RowVal.sgnAt G t s w.1 (i.1 + 1) * ρ := by
  rw [hρ, ← elt_succ]
  exact hr

theorem mk_eq_of {Gp : Type} [Group Gp] (H K : Subgroup Gp) {A A' S X Y ρ ρ' : Gp}
    (e : A' * (S * ρ') = X * (A * (S * ρ)) * Y) (hN : (A' * S)⁻¹ * X * (A * S) ∈ H) (hY : Y ∈ K) :
    DoubleCoset.mk H K ρ = DoubleCoset.mk H K ρ' := by
  rw [DoubleCoset.eq]
  refine ⟨_, hN, Y, hY, ?_⟩
  rw [show (A' * S)⁻¹ * X * (A * S) * ρ * Y = (A' * S)⁻¹ * (X * (A * (S * ρ)) * Y) by group, ← e]
  group

theorem idx_le {j : ℕ} (h : j ∈ GlobalTheory.RowVal.idx D) : 1 ≤ j ∧ j + 2 ≤ D.R.m := by
  simp only [GlobalTheory.RowVal.idx, List.mem_range'_1] at h
  omega

end GlobalTheory.RowRep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedLocalTotalTensorFixedByInnerVertexLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedLocalTotalTensorFixedByInnerVertexLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipVertexInv

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.TopLevelInv

theorem flips_isAdmissible {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} {ψ : AddChar k Circle} {ϖ : kˣ}
    {e : ℕ} (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) (he : 1 ≤ e) :
    ∀ (l : List (ℕ × ℕ)) (St : Γ.PiLocalization₂), (∀ x ∈ l, CondLE ϖ e (Γ.nu x.1 x.2)) → CanFlip St.path l →
      (∀ X, IsOpen (St.level X : Set (GL (Fin (Γ.rank X)) k)) ∧ St.level X ≤ KO k _) → St.IsAdmissible .one ϖ e →
      (St.flips .one ψ ϖ e l).IsAdmissible .one ϖ e := by
  intro l
  induction l with
  | nil => intro St _ _ _ hT; exact hT
  | cons x l ih =>
    intro St hν hc hJ hT
    obtain _ | ⟨hp, hc'⟩ := hc
    refine ih (St.flip .one ψ ϖ e x) (fun y hy => hν y (List.mem_cons_of_mem _ hy)) hc' (fun X => ?_)
      (GlobalTheory.T.splitThetaGrid_isAdmissible_flipTensor ψ ϖ e hϖ hψ he St x (hν x List.mem_cons_self) hp hJ hT)
    change IsOpen (Γ.flipLevel x.1 x.2 St.level X : Set (GL (Fin (Γ.rank X)) k)) ∧ Γ.flipLevel x.1 x.2 St.level X ≤ _
    by_cases hX : X = (x.1 + 1, x.2 + 1)
    · subst hX; simp only [Grid.flipLevel, Function.update_self]; exact ⟨isOpen_KO, le_rfl⟩
    · simp only [Grid.flipLevel, Function.update_of_ne hX]; exact hJ X

theorem mem_flipOrder {m : ℕ} {x : ℕ × ℕ} (hx : x ∈ flipOrder m) : x.1 < m ∧ x.2 < m := by
  simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, j, hj, rfl⟩ := hx
  exact ⟨hi, hj⟩

theorem mem_inner_opposite {m j : ℕ} (hj : j + 1 < m) : (j + 1, m) ∈ innerVertices (oppositePath m) := by
  obtain ⟨n, hn⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have h : Edge.ex (j + 1) m ∈ (oppositePath m).tail := by
    rw [oppositePath, hn, List.range_succ_eq_map, List.map_cons, List.cons_append, List.tail_cons]
    exact List.mem_append_left _ (List.mem_map.2 ⟨j + 1, List.mem_map.2 ⟨j, List.mem_range.2 (by omega), rfl⟩, rfl⟩)
  exact List.mem_map.2 ⟨_, h, rfl⟩

theorem main : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} (Φ : G.Datum), t ∈ U → ∀ {μ₀ : T}, L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → ∀ (w : Pl D.host.E), w ∈ locPl G t → ∀ (j : ℕ), j + 1 < D.R.m →
    ∀ (κ : GL (Fin ((locGrid G t w).rank (j + 1, D.R.m))) (Kw w)), κ ∈ givenLevel G t w (j + 1, D.R.m) →
    (locGrid G t w).pathAct .one (oppositePath D.R.m) (Pi.mulSingle (j + 1, D.R.m) κ) (Tflip W S.B t Φ w) =
      Tflip W S.B t Φ w := by
  intro D T L sc G W U S t Φ _ μ₀ hL hde hc w hw j hj κ hκ
  have hg := (Good.locGrid_isGood hL G W t hde hc).1 w hw
  have hm : 0 < D.R.m := by omega
  have h00 := hg.square 0 hm 0 hm
  have hν : ∀ x ∈ flipOrder D.R.m, CondLE (unifAt w) (depthAt G w) ((locGrid G t w).nu x.1 x.2) := by
    intro x hx
    obtain ⟨hi, hj⟩ := mem_flipOrder hx
    rw [← Grid.alpha_div_beta]
    exact (hg.square x.1 hi x.2 hj).condν
  have hfl : (flipStage t w S.B W Φ).IsAdmissible .one (unifAt w) (depthAt G w) :=
    flips_isAdmissible h00.unif h00.cond h00.one_le (flipOrder D.R.m) (givenStage t w S.B Φ) hν (canFlip_flipOrder _).1
      (fun X => GivenAdm.givenLevel_open hL hw X) (GivenAdm.givenStage_isAdmissible hL S.B t Φ hw)
  obtain ⟨hp, hl⟩ := flipStage_path_level t w S.B W Φ
  have := hfl.invariant (j + 1, D.R.m) (hp ▸ mem_inner_opposite hj) κ (hl ▸ hκ)
  rw [hp] at this
  exact this

end GlobalTheory.FlipVertexInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedLocalTotalTensorFixedByInnerVertexLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flippedLocalTotalTensor_fixed_by_innerVertex_level : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} (Φ : G.Datum), t ∈ U → ∀ {μ₀ : T}, L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → ∀ (w : Pl D.host.E), w ∈ locPl G t → ∀ (j : ℕ), j + 1 < D.R.m →
    ∀ (κ : GL (Fin ((locGrid G t w).rank (j + 1, D.R.m))) (Kw w)), κ ∈ givenLevel G t w (j + 1, D.R.m) →
    (locGrid G t w).pathAct .one (oppositePath D.R.m) (Pi.mulSingle (j + 1, D.R.m) κ) (Tflip W S.B t Φ w) =
      Tflip W S.B t Φ w := by
  first | exact @GlobalTheory.FlipVertexInv.main | exact GlobalTheory.FlipVertexInv.main | (intros; apply GlobalTheory.FlipVertexInv.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIteratedInvariantIntegralLinearAndCongr
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIteratedInvariantIntegralLinearAndCongr
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal.NIterLin

section
variable {G : Type} [Group G] [MeasurableSpace G] {R : Subgroup G} {μR : Measure R} {μG : Measure G}

theorem quot_sum {I : Type} (S : Finset I) (x : I → ℂ) (F : I → G → ℂ) (z : I → ℂ)
    (hF : ∀ n ∈ S, IsQuotIntL1 μR μG (F n) (z n)) :
    IsQuotIntL1 μR μG (fun g => ∑ n ∈ S, x n * F n g) (∑ n ∈ S, x n * z n) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have e : (fun g : G => ∑ n ∈ (∅ : Finset I), x n * F n g) = 0 := by funext g; simp
    rw [e, Finset.sum_empty]
    exact IsQuotIntL1.zero
  | insert a s ha ih =>
    have h1 := (hF a (Finset.mem_insert_self _ _)).smul (x a)
    have h2 := ih (fun n hn => hF n (Finset.mem_insert_of_mem hn))
    have h3 := h1.add h2
    rw [Finset.sum_insert ha]
    convert h3 using 1
    funext g
    simp [Finset.sum_insert ha]
end

variable {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)] [∀ i, MeasurableSpace (H i)]
  {R : ∀ i, Subgroup (H i)} (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i))

theorem lin (l : List ι) : ∀ (h : ∀ i, H i) (I : Type) (S : Finset I) (x z : I → ℂ) (q : I → (∀ i, H i) → ℂ),
    (∀ n ∈ S, NIter ρ μ (q n) l h (z n)) → NIter ρ μ (fun g => ∑ n ∈ S, x n * q n g) l h (∑ n ∈ S, x n * z n) := by
  induction l with
  | nil =>
    intro h I S x z q hq
    simp only [NIter] at hq ⊢
    exact Finset.sum_congr rfl fun n hn => by rw [hq n hn]
  | cons i l ih =>
    intro h I S x z q hq
    classical
    simp only [NIter] at hq ⊢
    let F : I → H i → ℂ := fun n => if hn : n ∈ S then Classical.choose (hq n hn) else 0
    have hF : ∀ n ∈ S, IsQuotIntL1 (ρ i) (μ i) (F n) (z n) ∧ ∀ g, NIter ρ μ (q n) l (Function.update h i g) (F n g) := by
      intro n hn
      simp only [F, dif_pos hn]
      exact Classical.choose_spec (hq n hn)
    refine ⟨fun g => ∑ n ∈ S, x n * F n g, quot_sum S x F z fun n hn => (hF n hn).1, fun g => ?_⟩
    exact ih (Function.update h i g) I S x (fun n => F n g) q fun n hn => (hF n hn).2 g

theorem congr (l : List ι) : ∀ (h : ∀ i, H i) (q q' : (∀ i, H i) → ℂ) (z : ℂ),
    (∀ g : ∀ i, H i, (∀ i, i ∉ l → g i = h i) → q g = q' g) → NIter ρ μ q l h z → NIter ρ μ q' l h z := by
  induction l with
  | nil =>
    intro h q q' z hq hz
    simp only [NIter] at hz ⊢
    rw [hz]
    exact hq h fun _ _ => rfl
  | cons i l ih =>
    intro h q q' z hq hz
    simp only [NIter] at hz ⊢
    obtain ⟨f, hf, hf'⟩ := hz
    refine ⟨f, hf, fun g => ih (Function.update h i g) q q' (f g) (fun g' hg' => hq g' fun j hj => ?_) (hf' g)⟩
    have hji : j ≠ i := fun e => hj (e ▸ List.mem_cons_self ..)
    have hjl : j ∉ l := fun e => hj (List.mem_cons_of_mem _ e)
    rw [hg' j hjl, Function.update_of_ne hji]

end GlobalTheory.RowVal.NIterLin

theorem GlobalTheory.RowVal.niter_lin_congr : ∀ (ι : Type) [DecidableEq ι] (H : ι → Type) [∀ i, Group (H i)] [∀ i, MeasurableSpace (H i)] (R : ∀ i, Subgroup (H i)) (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)) (l : List ι) (h : ∀ i, H i), (∀ (I : Type) (S : Finset I) (x z : I → ℂ) (q : I → (∀ i, H i) → ℂ), (∀ n ∈ S, NIter ρ μ (q n) l h (z n)) → NIter ρ μ (fun g => ∑ n ∈ S, x n * q n g) l h (∑ n ∈ S, x n * z n)) ∧ ∀ q q' z, (∀ g : ∀ i, H i, (∀ i, i ∉ l → g i = h i) → q g = q' g) → NIter ρ μ q l h z → NIter ρ μ q' l h z := by
  intro ι _ H _ _ R ρ μ l h
  exact ⟨fun I S x z q hq => GlobalTheory.RowVal.NIterLin.lin ρ μ l h I S x z q hq,
    fun q q' z hq hz => GlobalTheory.RowVal.NIterLin.congr ρ μ l h q q' z hq hz⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIteratedInvariantIntegralLinearAndCongrStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIteratedInvariantIntegral_linear_and_congr : ∀ (ι : Type) [DecidableEq ι] (H : ι → Type) [∀ i, Group (H i)] [∀ i, MeasurableSpace (H i)] (R : ∀ i, Subgroup (H i)) (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)) (l : List ι) (h : ∀ i, H i), (∀ (I : Type) (S : Finset I) (x z : I → ℂ) (q : I → (∀ i, H i) → ℂ), (∀ n ∈ S, NIter ρ μ (q n) l h (z n)) → NIter ρ μ (fun g => ∑ n ∈ S, x n * q n g) l h (∑ n ∈ S, x n * z n)) ∧ ∀ q q' z, (∀ g : ∀ i, H i, (∀ i, i ∉ l → g i = h i) → q g = q' g) → NIter ρ μ q l h z → NIter ρ μ q' l h z := by
  first | exact @GlobalTheory.RowVal.niter_lin_congr | exact GlobalTheory.RowVal.niter_lin_congr | (intros; apply GlobalTheory.RowVal.niter_lin_congr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanUnitaryWeights
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealUnitaryFockColumnActionSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealUnitaryFockColumnActionSurjective
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
open scoped Matrix

namespace GlobalTheory.RealColAct

theorem compAt_eq_infMat {D : D7} (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (h : GA D V) :
    compAt θ τ (Formalism.L2.Theta.mt V h) = infMat D.sp.cm.sig V.gram (θ τ) h := rfl

theorem realCol_surjective {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (hV : HSpace.gram V = 1) :
    Function.Surjective (GlobalTheory.RealColAct.realCol θ hθ V hV) := by
  classical
  intro u
  have hex : ∀ τ, ∃ h : GA D V, IsAtTau θ V τ ((u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᵀ) h := fun τ => by
    refine (GlobalTheory.PointAtPlace.existsUnique_isAtTau V τ θ hθ _ ?_).exists
    have hu := transpose_mem_unitary (u τ).2
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
    show _ * _ * _ = _
    rw [gramAt_of_gram_one hV, Matrix.mul_one, hu]
  choose hτ hhτ using hex
  have key : ∀ (L : List D.what₂.Tau), L.Nodup → ∀ ρ,
      compAt θ ρ (Formalism.L2.Theta.mt V (L.map hτ).prod) =
        if ρ ∈ L then ((u ρ : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᵀ) else 1 := by
    intro L
    induction L with
    | nil => intro _ ρ; simp only [List.map_nil, List.prod_nil, List.not_mem_nil, if_false]; exact GlobalTheory.StdUnn.CartanMove.compAt_mt_one θ ρ V
    | cons a L ih =>
      intro hL ρ
      rw [List.nodup_cons] at hL
      rw [List.map_cons, List.prod_cons, GlobalTheory.StdUnn.CartanMove.compAt_mt_mul, ih hL.2 ρ, compAt_eq_infMat]
      by_cases c : ρ = a
      · subst c
        rw [(hhτ ρ).2.1, if_neg hL.1, if_pos List.mem_cons_self, Matrix.mul_one]
      · rw [(hhτ a).2.2 ρ c, Matrix.one_mul]
        by_cases d : ρ ∈ L
        · rw [if_pos d, if_pos (List.mem_cons_of_mem a d)]
        · rw [if_neg d, if_neg (by simp [c, d])]
  let L := (Finset.univ : Finset D.what₂.Tau).toList
  have hmem : (L.map hτ).prod ∈ GinfC V := by
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
    exact (hhτ τ).1
  refine ⟨(⟨(L.map hτ).prod, hmem⟩ : GinfC V)⁻¹, ?_⟩
  funext ρ
  apply Subtype.ext
  rw [realCol_apply]
  simp only [InvMemClass.coe_inv, inv_inv]
  rw [key L (Finset.nodup_toList _) ρ, if_pos (Finset.mem_toList.2 (Finset.mem_univ ρ)), Matrix.transpose_transpose]

end GlobalTheory.RealColAct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealUnitaryFockColumnActionSurjectiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realUnitaryFockColumnAction_surjective : ∀ {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (hV : HSpace.gram V = 1), Function.Surjective (GlobalTheory.RealColAct.realCol θ hθ V hV) := by
  first | exact @GlobalTheory.RealColAct.realCol_surjective | exact GlobalTheory.RealColAct.realCol_surjective | (intros; apply GlobalTheory.RealColAct.realCol_surjective <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

open scoped Matrix

namespace GlobalTheory.BottomRealAct

theorem substF_one_eq_colSub {ι : Type} {N n : ℕ} (M : ι → Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) M = GlobalTheory.MinorFrame.colSub M := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rw [GlobalTheory.CompactHowe.substF_X]
  simp only [GlobalTheory.MinorFrame.colSub, MvPolynomial.aeval_X]
  rw [Finset.sum_eq_single v.2.1]
  · simp only [Matrix.one_apply_eq, one_mul]
  · intro x _ hx
    simp only [Matrix.one_apply_ne hx, zero_mul, MvPolynomial.C_0, Finset.sum_const_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem rightRegularAction_list_dLR_eq_append {G : Type*} [CommGroup G] (a x y e c : G) : a * x * e / (c * e) = a * y * e / (c * e) * (x * y⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv]
  abel

end GlobalTheory.BottomRealAct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsColumnUnitVacuaFamilyMoved
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsColumnUnitVacuaFamilyMoved
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColVac

variable {D : D7} {T : Type}

theorem xi_mem_xiVals {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) (t : T) (x : (AE D)ˣ) :
    Circle.toUnits (L.xi t x) ∈ xiVals L t := by
  obtain ⟨n, hn0, hn⟩ := hL.xi_fin t
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  have e : L.xi t x = L.xi t (b x) := by
    conv_lhs => rw [hab x, map_mul, GlobalTheory.TupRoot.eq_one_of_finPart (hL.xi t) hn0 hn _ (ha x).2, one_mul]
  rw [e]
  have hx := (hb x).1
  generalize b x = u at hx
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h4 := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 h4 _ _ (hL.xi t)
  let y : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ :=
    ⟨ι (finPart D (u : AE D)), ι (finPart D ((u⁻¹ : (AE D)ˣ) : AE D)),
      by rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one],
      by rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]⟩
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN y
  have h5 := hprod u hx S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS'
  have h6 : Circle.toUnits (L.xi t u) = ∏ P ∈ S, (L.xiH t).locK P (k P) := by
    apply Units.ext
    rw [Units.coe_prod]
    exact h5
  rw [h6]
  exact prod_mem fun P _ => Subgroup.subset_closure ⟨P, _, rfl⟩

theorem attChr_mu {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) (t : T) (j n : ℕ) :
    Formalism.IndefR.Lift.attChr (L.mu t j) L.eta n = Formalism.IndefR.Lift.attChr (L.mu μ0 j) L.eta n * L.xi t := by
  have hb : L.xi μ0 = 1 :=
    MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi μ0))
  have e : L.mu t j = L.mu μ0 j * L.xi t := by
    show L.mu0 j * L.xi t = L.mu0 j * L.xi μ0 * L.xi t
    rw [hb, mul_one]
  unfold Formalism.IndefR.Lift.attChr
  rw [e]
  split_ifs
  · exact mul_right_comm _ _ _
  · rfl

section Move

variable {V : HSp D} {k : GA D V} {C Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}


set_option synthInstance.maxHeartbeats 400000 in
theorem fwd (h : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) C ↔
      (Formalism.IndefR.Lev.finE V k).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) (s : Fin V.rank → D.host.E) (hs : s ∈ C) :
    (fun i => Formalism.IndefR.Datum.toEAf D ((mt V k *ᵥ fun j => incA D (s j)) i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  rw [GlobalTheory.MovedHomLat.bridge]
  exact (h _).1 (Submodule.subset_span ⟨s, hs, rfl⟩)


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem bwd (h : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) C ↔
      (Formalism.IndefR.Lev.finE V k).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) (s : Fin V.rank → D.host.E) (hs : s ∈ Λ) :
    (fun i => Formalism.IndefR.Datum.toEAf D ((mt V k⁻¹ *ᵥ fun j => incA D (s j)) i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) C := by
  have e2 : (Formalism.IndefR.Lev.finE V k).1 * (Formalism.IndefR.Lev.finE V k⁻¹).1 = 1 :=
    congrArg Units.val (((Formalism.IndefR.Lev.finE V).map_mul k k⁻¹).symm.trans
      ((congrArg (Formalism.IndefR.Lev.finE V) (mul_inv_cancel k)).trans (Formalism.IndefR.Lev.finE V).map_one))
  rw [GlobalTheory.MovedHomLat.bridge]
  refine (h _).2 ?_
  rw [Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]
  exact Submodule.subset_span ⟨s, hs, rfl⟩

end Move

variable {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} {N : Std G U}

theorem isVac_moved (Z : Normal W N) (t : T) {j : ℕ} (hj : j < D.R.m) :
    W.IsVac (.top t j) (W.om (.top t j) ((N.u (.top j)).1, (N.u (.top (j + 1))).1) (Z.vac (.top t j))) := by
  have h0 := N.u_lat (.top j) hj.le
  have h1 := N.u_lat (.top (j + 1)) hj
  have H := GlobalTheory.MovedHomLat.actO_latO_onto (G.V (.top j)) (G.V (.top (j + 1))) (N.u (.top j)).1 (N.u (.top (j + 1))).1
    _ _ _ _ (fwd h0) (fwd h1) (bwd h0) (bwd h1)
  refine GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ _ _ _ _ _ (W.om_is (.top t j) (show j + 1 ≤ D.R.m from hj)) W.θ_is
    _ _ _ _ _ _ _ _ _ _ (fun τ => ?_) (fun τ => ?_) (fun u => ⟨fun hu => ?_, ?_⟩) _ (Z.vac_is (.top t j) hj)
  · rw [GlobalTheory.FockRealMove.compAt_mt_of_mem_GfC W.θ τ _ (N.u (.top j)).2, Matrix.mul_one, Matrix.one_mul]
  · rw [GlobalTheory.FockRealMove.compAt_mt_of_mem_GfC W.θ τ _ (N.u (.top (j + 1))).2, Matrix.mul_one, Matrix.one_mul]
  · obtain ⟨w, hw, e⟩ := H.2 u hu
    exact ⟨w, hw, e.symm⟩
  · rintro ⟨w, hw, rfl⟩
    exact H.1 w hw

theorem colVac : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∃ v, IsColVac ch v ∧ ∃ (κ : ℕ → ℂˣ) (z : T → ℕ → ℂˣ), (∀ t j, z t j ∈ xiVals R.toLevCh t) ∧ ∀ (t : T) (j : ℕ), j < D.R.m → ch.W.om (.top t j) (ch.G.toPair (.top t j) (ch.S.N.u (Pair.top t j : Pair T).small).1 (ch.S.N.u (Pair.top t j : Pair T).big).1) (ch.S.Z.vac (.top t j)) = ((κ j * z t j : ℂˣ) : ℂ) • v j := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R large₂ F hS ch _
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  choose x hx using fun j => GlobalTheory.RecDict.exists_isDetRoot D (ch.G.V (.top j)) (ch.S.N.u (.top j)).1
  refine ⟨fun j => ch.W.om (.top A.μ0 j) ((ch.S.N.u (.top j)).1, (ch.S.N.u (.top (j + 1))).1) (ch.S.Z.vac (.top A.μ0 j)),
    fun t j hj => isVac_moved ch.S.Z A.μ0 hj, fun _ => 1,
    fun t j => Circle.toUnits (R.toLevCh.xi t ((x j)⁻¹ * x (j + 1))),
    fun t j => xi_mem_xiVals hL t _, fun t j hj => ?_⟩
  have hW0 := ch.W.om_is (.top A.μ0 j) (show j + 1 ≤ D.R.m from hj)
  have hWt := ch.W.om_is (.top t j) (show j + 1 ≤ D.R.m from hj)
  have eS : ch.G.chrS (.top t j) = ch.G.chrS (.top A.μ0 j) * R.toLevCh.xi t := attChr_mu hL t _ _
  have eT : ch.G.chrT (.top t j) = ch.G.chrT (.top A.μ0 j) * R.toLevCh.xi t := attChr_mu hL t _ _
  rw [eS, eT] at hWt
  have e := GlobalTheory.TupRoot.twist_eq hW0 hWt (hx j) (hx (j + 1)) (ch.S.Z.vac_is (.top A.μ0 j) hj).2.theta
  rw [(ch.S.Z.free t A.μ0 j).2.1]
  refine e.trans ?_
  congr 1
  rw [one_mul, ← MonoidHom.map_inv, ← MonoidHom.map_mul]
  rfl

end GlobalTheory.ColVac

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsColumnUnitVacuaFamilyMovedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_columnUnitVacuaFamily_moved : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∃ v, IsColVac ch v ∧ ∃ (κ : ℕ → ℂˣ) (z : T → ℕ → ℂˣ), (∀ t j, z t j ∈ xiVals R.toLevCh t) ∧ ∀ (t : T) (j : ℕ), j < D.R.m → ch.W.om (.top t j) (ch.G.toPair (.top t j) (ch.S.N.u (Pair.top t j : Pair T).small).1 (ch.S.N.u (Pair.top t j : Pair T).big).1) (ch.S.Z.vac (.top t j)) = ((κ j * z t j : ℂˣ) : ℂ) • v j := by
  first | exact @GlobalTheory.ColVac.colVac | exact GlobalTheory.ColVac.colVac | (intros; apply GlobalTheory.ColVac.colVac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstColumnTypeTwistDatumEqGivenFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstColumnTypeTwistDatumEqGivenFunction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipTop

theorem prodHalf_topFn_eq_givenFn : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (B : Frames G) {μ₀ : T}, L.Is μ₀ →
    ∀ (t : T) {e e' : AE D}, IsIdemSum e (locPl G t) → IsIdemSum e' (GlobalTheory.FlipTop.topPl L t) → (∀ w ∈ locPl G t, w ∉ GlobalTheory.FlipTop.topPl L t → ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) → ∀ (Φ : G.Datum) (j : ℕ) (hj : j < D.R.m),
    GlobalTheory.HalfProd.prodHalf e' (e - e') (halfInd (e - e') (latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _) (G.latT (.mu t 0 j) : Set _) fun _ => True)) (GlobalTheory.FlipTop.topFn B t e' j (GlobalTheory.FlipTop.rank_col G hj.le) (GlobalTheory.FlipTop.rank_col G hj)) =
      GlobalTheory.FlipStart.givenFn B t Φ e (.down t 0 j) := by
  intro D T L sc G B μ₀ hL t e e' he he' hAA Φ j hj
  classical
  have hsub : GlobalTheory.FlipTop.topPl L t ⊆ locPl G t := by
    intro w hw
    rcases Finset.mem_union.1 hw with h | h
    · exact Finset.mem_union_left _ (levelChainTypePlaces_subset_chosenPlaces G hL t h)
    · exact Finset.mem_union_right _ h
  obtain ⟨he₁, -⟩ := GlobalTheory.T.isIdemSum_sub_of_subset_and_orthogonal he he' hsub
  have h1 := GlobalTheory.PlaceDatum.idemSum_mul_self he'
  have h2 := GlobalTheory.PlaceDatum.idemSum_mul_self he₁
  obtain ⟨-, c1, c0⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he'
  obtain ⟨-, d1, -⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he₁
  have ha := GlobalTheory.FlipTop.rank_col G hj.le
  have hb := GlobalTheory.FlipTop.rank_col G hj
  funext x
  rw [GlobalTheory.HalfProd.prodHalf_apply, add_sub_cancel]
  unfold GlobalTheory.FlipStart.givenFn
  by_cases hx : IsHalf e x
  swap
  · rw [if_neg hx, if_neg hx, mul_zero]
  rw [if_pos hx, if_pos hx, mul_one]
  set N := GlobalTheory.FunObj.Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D)) with hN
  have hfr : ∀ a : AE D, GlobalTheory.FunObj.Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) ((a • x).map (toEAf D)) = toEAf D a • N := by
    intro a
    rw [hN, ← GlobalTheory.FunObj.Comparison₂.fr_smul]
    congr 1
    ext p q
    simp [Matrix.map_apply, Matrix.smul_apply, RingHom.map_mul]
  have hcomp : ∀ (a : AE D) (w : Pl D.host.E), cpt (D := D) w (toEAf D a) = 1 →
      (GlobalTheory.FunObj.Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) ((a • x).map (toEAf D))).map (cpt (D := D) w) = N.map (cpt (D := D) w) := by
    intro a w hw
    rw [hfr]
    ext p q
    simp [Matrix.map_apply, Matrix.smul_apply, RingHom.map_mul, hw]

  have hsubm : ∀ w : Pl D.host.E, GlobalTheory.StepData.IntM ((N.map (cpt (D := D) w)).submatrix (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb)
      (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) ↔ GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) := fun w =>
    ⟨fun h i l => by simpa using h ((GlobalTheory.FunObj.Comparison₂.ixOf G t w hb).symm i) ((GlobalTheory.FunObj.Comparison₂.ixOf G t w ha).symm l),
      fun h i l => h _ _⟩
  have hR : ∀ w, givenDatum t w B Φ (edgeOf (.down t 0 j)) (locArg B t w (.down t 0 j) x) =
      stepFn L t w j ((N.map (cpt (D := D) w)).submatrix (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb) (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) := by
    intro w
    have hla : locArg B t w (.down t 0 j) x = B.coord t w (X := (0, j + 1)) (Y := (0, j)) ⟨Nat.zero_le _, hj⟩
        ⟨Nat.zero_le _, hj.le⟩ ((x.map (toEAf D)).map (cpt (D := D) w)) := by
      rw [Matrix.map_map]
      exact dif_pos ⟨Nat.zero_le _, hj⟩
    rw [hla]
    exact GlobalTheory.FunObj.Comparison₂.givenDatum_theta_coord B t w Φ hj ha hb (x.map (toEAf D))
  rw [Finset.prod_congr rfl fun w _ => hR w, ← Finset.prod_sdiff hsub]
  have hout : ∀ w ∈ locPl G t \ GlobalTheory.FlipTop.topPl L t, stepFn L t w j ((N.map (cpt (D := D) w)).submatrix
      (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb) (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) =
      if GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) then 1 else 0 := by
    intro w hw
    obtain ⟨-, hw2⟩ := Finset.mem_sdiff.1 hw
    have hP : w ∉ L.Pg := fun h => hw2 (Finset.mem_union_left _ h)
    have hQ : w ∉ L.Q t := fun h => hw2 (Finset.mem_union_right _ h)
    unfold stepFn
    rw [if_neg hP, if_neg hQ, Set.indicator_apply]
    exact if_congr (hsubm w) rfl rfl
  rw [Finset.prod_congr rfl hout, Finset.prod_boole]

  have hx1 : IsHalf (e - e') ((e - e') • x) := fun p q => by
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, h2]
  have hS : IsSelfDualC (G.pS (.mu t 0 j)) (G.latS (.mu t 0 j)) := (colY_isV D T L μ₀ hL j hj.le).sd
  have hT : IsSelfDualC (G.pT (.mu t 0 j)) (G.latT (.mu t 0 j)) := (colY_isV D T L μ₀ hL (j + 1) hj).sd
  have hAA' : ∀ w ∈ locPl G t \ GlobalTheory.FlipTop.topPl L t, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := fun w hw =>
    hAA w (Finset.mem_sdiff.1 hw).1 (Finset.mem_sdiff.1 hw).2
  have hlat := GlobalTheory.T.mem_completedHomLattice_iff_integral_on_unit_half hS hT (B.isFrame_β hL (Nat.zero_le _) hj.le) (B.isFrame_β hL (Nat.zero_le _) hj) he₁ hAA'
    ((e - e') • x) hx1
  have k1 : halfInd (e - e') (latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _)
      (G.latT (.mu t 0 j) : Set _) fun _ => True) ((e - e') • x) =
      if ∀ w ∈ locPl G t \ GlobalTheory.FlipTop.topPl L t, GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) then 1 else 0 := by
    unfold halfInd
    refine if_congr ?_ rfl rfl
    rw [and_iff_left hx1, hlat]
    exact forall₂_congr fun w hw => by rw [hcomp _ w (d1 w hw)]

  have hint : IsIntM (toEAf D e' • N) ↔ ∀ w ∈ GlobalTheory.FlipTop.topPl L t, GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) := by
    constructor
    · intro h w hw i l
      have := (mem_OA_iff _).1 (h i l) w
      rw [Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, c1 w hw, one_mul] at this
      exact (GlobalTheory.FunObj.Comparison₂.vEq w).le_one_iff_le_one.2 this
    · intro h i l
      refine (mem_OA_iff _).2 fun w => ?_
      rw [Matrix.smul_apply, smul_eq_mul, RingHom.map_mul]
      by_cases hw : w ∈ GlobalTheory.FlipTop.topPl L t
      · rw [c1 w hw, one_mul]
        exact (GlobalTheory.FunObj.Comparison₂.vEq w).le_one_iff_le_one.1 (h w hw i l)
      · rw [c0 w hw, zero_mul]
        exact zero_mem _
  have hx0 : IsHalf e' (e' • x) := fun p q => by
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, h1]
  have k0 : GlobalTheory.FlipTop.topFn B t e' j ha hb (e' • x) = ∏ w ∈ GlobalTheory.FlipTop.topPl L t, stepFn L t w j
      ((N.map (cpt (D := D) w)).submatrix (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb) (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) := by
    unfold GlobalTheory.FlipTop.topFn
    rw [Finset.prod_congr rfl fun w hw => by rw [hcomp e' w (c1 w hw)]]
    by_cases H : ∀ w ∈ GlobalTheory.FlipTop.topPl L t, GlobalTheory.StepData.IntM (N.map (cpt (D := D) w))
    · rw [if_pos ⟨hx0, by rw [hfr]; exact hint.2 H⟩]
    · rw [if_neg fun h => H (by have h' := h.2; rw [hfr] at h'; exact hint.1 h')]
      push_neg at H
      obtain ⟨w, hw, hn⟩ := H
      refine (Finset.prod_eq_zero hw ?_).symm
      by_contra h0
      exact hn ((hsubm w).1 (GlobalTheory.FunObj.LocTest.intM_of_stepFn t w j h0))
  rw [k0, k1, mul_comm]

end GlobalTheory.FlipTop

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstColumnTypeTwistDatumEqGivenFunctionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.first_column_type_twist_datum_eq_given_function : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (B : Frames G) {μ₀ : T}, L.Is μ₀ →
    ∀ (t : T) {e e' : AE D}, IsIdemSum e (locPl G t) → IsIdemSum e' (GlobalTheory.FlipTop.topPl L t) → (∀ w ∈ locPl G t, w ∉ GlobalTheory.FlipTop.topPl L t → ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) → ∀ (Φ : G.Datum) (j : ℕ) (hj : j < D.R.m),
    GlobalTheory.HalfProd.prodHalf e' (e - e') (halfInd (e - e') (latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _) (G.latT (.mu t 0 j) : Set _) fun _ => True)) (GlobalTheory.FlipTop.topFn B t e' j (GlobalTheory.FlipTop.rank_col G hj.le) (GlobalTheory.FlipTop.rank_col G hj)) =
      GlobalTheory.FlipStart.givenFn B t Φ e (.down t 0 j) := by
  first | exact @GlobalTheory.FlipTop.prodHalf_topFn_eq_givenFn | exact GlobalTheory.FlipTop.prodHalf_topFn_eq_givenFn | (intros; apply GlobalTheory.FlipTop.prodHalf_topFn_eq_givenFn <;> assumption)
end
end
