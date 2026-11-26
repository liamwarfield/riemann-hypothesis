module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOmegaField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLocalIntegralPointsMemOpenSubgroupDefi
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.ExtEmbEquivComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowSizesNR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformFixedBySmallFiniteHeisenberg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharactersArchExponentsGapGtRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeisenbergInvariantThetaMeanSquareForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.OneMapAll

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  Formalism.L2.DIV GlobalTheory.FieldBC Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.MainNotions Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Compare

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}

def RowAt {Tp : Type} {tup : Tp → T0} (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))
    (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (ph : ℂ) : Prop :=
  OneMapRow (C.Q.Xo ((i : ℕ) + 1)) O.c' (Wc D i) (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c')) O.dict O.mu (xiR D) (wtA κ)
    (actLev O.c' O.lev2) O.dδ O.Cl' O.w O.La O.Nc O.gam O.vol O.ep O.io O.thAd O.Plc D.what₂.embLL.toRatAlgHom.fieldRange
    (cusp (C.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (C.U ((i : ℕ) + 1))) (wtA κ) (Vc D i).rank) cc ph

abbrev IsSum {Tp : Type} {tup : Tp → T0} (O : OMDat C R i Tp tup) (t : Tp) (x : O.Cl' t → VsV D i O.c'.F)
    (f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c') : Prop :=
  IsThClsD (C.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ t) (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t) O.io x f

abbrev cuspOver {Tp : Type} {tup : Tp → T0} (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) :
    Submodule O.c'.F (Rul (C.Q.Xo ((i : ℕ) + 1)) O.c') :=
  cusp (C.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (C.U ((i : ℕ) + 1))) (wtA κ) (Vc D i).rank

def ClassSumsSpan {t₀ : T0} (O : OMDat C R i Unit (fun _ => t₀)) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) : Prop :=
  cuspOver O κ ≤ Submodule.span O.c'.F {g | g ∈ cuspOver O κ ∧ ∃ x, O.Plc () x ∧ IsSum O () x g}

def geo {Tp : Type} {tup : Tp → T0} (O : OMDat C R i Tp tup) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (z : G)
    (f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c') (q : AutQ (Wc D i)) : ℂ :=
  cc (O.dict q.out).1 * jFn (Wc D i) (inC O.c') (rdU (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c'))) O.dict O.mu
    (actLev O.c' O.lev2 z f) q

variable {Tp : Type} {tup : Tp → T0}

theorem geo_add (O : OMDat C R i Tp tup) (cc z f g q) : geo O cc z (f + g) q = geo O cc z f q + geo O cc z g q := by
  unfold geo
  rw [map_add (f := _), map_add (f := _), Pi.add_apply, mul_add]

theorem geo_smul (O : OMDat C R i Tp tup) (cc z) (a : O.c'.F) (f q) : geo O cc z (a • f) q = (a : ℂ) * geo O cc z f q := by
  unfold geo
  rw [map_smul, map_smulₛₗ, Pi.smul_apply, smul_eq_mul, mul_left_comm]
  rfl

theorem geo_of_isBC (O : OMDat C R i Tp tup) (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c O.lev2) (cc z)
    {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n m : ℕ} {f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c'} (hf : f ∈ sec _ O.c' a n)
    {as : Fin m → O.c'.F} {fs : Fin m → Rul (C.Q.Xo ((i : ℕ) + 1)) C.Q.c} (hfs : ∀ k, fs k ∈ sec _ C.Q.c a n)
    (h : IsBC O.hle f as fs) (q : AutQ (Wc D i)) :
    geo O cc z f q = ∑ k, (as k : ℂ) * O.phi cc (actLev C.Q.c O.lev2 z (fs k)) q.out := by
  have h1 := (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hact).2 a n z m as fs f hf hfs h
  have h2 := congrFun (congrFun (rdU_unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c') h1) (O.dict q.out).1) (O.dict q.out).2
  rw [Finset.sum_apply, Finset.sum_apply] at h2
  refine (congrArg (fun w => cc (O.dict q.out).1 * (O.mu q.out * w)) h2).trans ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show cc _ * (O.mu _ * ((as k : ℂ) * _)) = (as k : ℂ) * (cc _ * O.mu _ * _)
  ring

theorem phi_eq {Tp' : Type} {tup' : Tp' → T0} (O : OMDat C R i Tp tup) (O' : OMDat C R i Tp' tup')
    (cE : ∀ s : C.Q.c.F →+* ℂ, (C.U ((i : ℕ) + 1) s).Comp → ℂ) : O.phi (cE O.s0) = O'.phi (cE O'.s0) := by
  have key : ∀ (s s' : C.Q.c.F →+* ℂ) (_ : s = s') (hV : C.V ((i : ℕ) + 1) s = Wc D i) (hV' : C.V ((i : ℕ) + 1) s' = Wc D i)
      (f : C.R ((i : ℕ) + 1)),
      adel (Wc D i) (castDict hV (C.dict ((i : ℕ) + 1) s)) (muPin (Wc D i) (castDict hV (C.dict ((i : ℕ) + 1) s))
        (castDict hV (C.mu ((i : ℕ) + 1) s)) (cE s)) (rdU (C.U ((i : ℕ) + 1) s) f) =
      adel (Wc D i) (castDict hV' (C.dict ((i : ℕ) + 1) s')) (muPin (Wc D i) (castDict hV' (C.dict ((i : ℕ) + 1) s'))
        (castDict hV' (C.mu ((i : ℕ) + 1) s')) (cE s')) (rdU (C.U ((i : ℕ) + 1) s') f) := by
    intro s s' e hV hV' f
    subst e
    rfl
  funext f
  exact key _ _ ((sOv_eq C _ _).trans (sOv_eq C _ _).symm) O.hV O'.hV f

theorem geo_rulBC {Tp' : Type} {tup' : Tp' → T0} (O : OMDat C R i Tp tup) (M : OMDat C R i Tp' tup') (hle : O.c'.F ≤ M.c'.F)
    (hlev : M.lev = O.lev) (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c O.lev2)
    (cE : ∀ s : C.Q.c.F →+* ℂ, (C.U ((i : ℕ) + 1) s).Comp → ℂ) (z : G) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c'} (hf : f ∈ sec _ O.c' a n) (q : AutQ (Wc D i)) :
    geo M (cE M.s0) z (rulBC hle f) q = geo O (cE O.s0) z f q := by
  have e : M.lev2 = O.lev2 := by funext g; simp only [OMDat.lev2, hlev]
  obtain ⟨m, as, fs, hfs, h⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O.hle).1 a n f hf
  rw [geo_of_isBC O hact _ z hf hfs h, geo_of_isBC M (e ▸ hact) _ z (GlobalTheory.FieldBCModel.rulBC_mem_sec hle hf) hfs
    (isBC_rulBC_trans O.hle hle M.hle hf h), phi_eq M O cE, e]
  rfl

theorem isSum_unique {O : OMDat C R i Tp tup} {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ ι x₀} (h : O.Pins κ v₀ ι x₀) (t : Tp)
    {x : O.Cl' t → VsV D i O.c'.F} {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f f' : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c'}
    (hf : f ∈ sec _ O.c' a n) (hf' : f' ∈ sec _ O.c' a n) (h1 : IsSum O t x f) (h2 : IsSum O t x f') : f = f' := by
  obtain ⟨-, cga, -, -, hr, -⟩ := h.io
  refine GlobalTheory.ClassSumUnique.isThClsD_unique GlobalTheory.chartIndependence_unconditional _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (h.cov t).1 (h.cov t).2.2
    (fun k => ⟨((h.reps t).1 k).1, ((h.reps t).1 k).2.2.1, ((h.reps t).1 k).2.2.2.1⟩) (wtA κ) (fun v => ?_) x a n f hf f' hf' h1 h2
  have hv := hr.le (LinearMap.mem_range_self O.io v)
  exact (Submodule.span_le (p := GlobalTheory.FrameRead.CoefMap.harmSub _ _ _ _ _ _)).2 (fun _ hP => hP) hv

theorem geo_agree {t₀ : T0} (O : OMDat C R i Unit (fun _ => t₀)) (M : OMDat C R i Tp tup) (hle : O.c'.F ≤ M.c'.F)
    (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c M.lev2) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} (hspan : ClassSumsSpan O κ)
    {cc cc' : (C.U ((i : ℕ) + 1) M.s0).Comp → ℂ} {z z' : G} {α β : ℂ} (q : AutQ (Wc D i))
    (h : ∀ g ∈ cuspOver O κ, (∃ x, O.Plc () x ∧ IsSum O () x g) →
      α * geo M cc z (rulBC hle g) q = β * geo M cc' z' (rulBC hle g) q) :
    ∀ f ∈ cuspOver M κ, α * geo M cc z f q = β * geo M cc' z' f q := by
  have hlin := (GlobalTheory.FieldBC.rulBC_sec_val_linear _ _ _ _ (C.Q.Xo ((i : ℕ) + 1)) _ _ hle).2
  have h0 : rulBC hle (0 : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c') = 0 := by
    have := hlin (-1) 0 0
    rwa [smul_zero, zero_add, map_neg, map_one, neg_one_smul, neg_add_cancel] at this
  have h1 : ∀ g ∈ cuspOver O κ, α * geo M cc z (rulBC hle g) q = β * geo M cc' z' (rulBC hle g) q := by
    intro g hg
    have hg' := hspan hg
    clear hg
    induction hg' using Submodule.span_induction with
    | mem g hg => exact h g hg.1 hg.2
    | zero =>
      have e := geo_smul M cc z 0 0 q
      have e' := geo_smul M cc' z' 0 0 q
      rw [zero_smul] at e e'
      rw [h0, e, e']
      simp
    | add f g _ _ hf hg =>
      have e := hlin 1 f g
      rw [one_smul, map_one, one_smul] at e
      rw [e, geo_add, geo_add, mul_add, mul_add, hf, hg]
    | smul a f _ hf =>
      have e := hlin a f 0
      rw [add_zero, h0, add_zero] at e
      rw [e, geo_smul, geo_smul, mul_left_comm, hf, mul_left_comm]
  intro f hf
  obtain ⟨m, as, fs, hfs, hBC⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ M.hle).2 _ (C.U ((i : ℕ) + 1)) _ _ f hf
  have hs : ∀ k, fs k ∈ sec _ C.Q.c (wtA κ) (Vc D i).rank := fun k => ((mem_cusp _ _ _ _ _ _).1 (hfs k)).1
  have hf' := ((mem_cusp _ _ _ _ _ _).1 hf).1
  rw [geo_of_isBC M hact cc z hf' hs hBC, geo_of_isBC M hact cc' z' hf' hs hBC, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := GlobalTheory.FieldBCModel.rulBC_mem_sec O.hle (hs k)
  have hb := isBC_rulBC_trans O.hle hle M.hle hk (GlobalTheory.FieldBCModel.isBC_rulBC O.hle (hs k).1)
  have hs1 : ∀ k', ![fs k] k' ∈ sec _ C.Q.c (wtA κ) (Vc D i).rank := fun k' => by
    rw [Subsingleton.elim k' 0]; exact hs k
  have e := h1 _ (((GlobalTheory.FieldBC.rulBC_cusp _ _ _ _ _ _ _ O.hle _ (C.U ((i : ℕ) + 1)) _ _ _ (hs k)).2).2 (hfs k))
  rw [geo_of_isBC M hact cc z (GlobalTheory.FieldBCModel.rulBC_mem_sec hle hk) hs1 hb,
    geo_of_isBC M hact cc' z' (GlobalTheory.FieldBCModel.rulBC_mem_sec hle hk) hs1 hb] at e
  simp only [Fin.sum_univ_one, Matrix.cons_val_zero, map_one, OneMemClass.coe_one, one_mul] at e
  rw [mul_left_comm, e, mul_left_comm]


set_option maxHeartbeats 1000000 in
theorem oneMapOf_of_extends (O : OMDat C R i Unit (fun _ => A.μ0)) (M : OMDat C R i Tp tup) (t₀ : Tp) (hle : O.c'.F ≤ M.c'.F)
    (hlev : M.lev = O.lev) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ ι x₀} (hM : M.Pins κ v₀ ι x₀)
    (hext : ∀ x, O.Plc () x → ∃ x', M.Plc t₀ x' ∧ M.thAd t₀ x' = O.thAd () x ∧
      ∀ f ∈ sec _ O.c' (wtA κ) (Vc D i).rank, IsSum O () x f → IsSum M t₀ x' (rulBC hle f))
    (hspan : ClassSumsSpan O κ) (cE : ∀ s : C.Q.c.F →+* ℂ, (C.U ((i : ℕ) + 1) s).Comp → ℂ) {ph : ℂ}
    (hO : O.OneMapOf κ v₀ (cE O.s0) ph) {cc' ph'} (hrow : RowAt M κ cc' ph') : M.OneMapOf κ v₀ (cE M.s0) ph := by
  have e : M.lev2 = O.lev2 := by funext g; simp only [OMDat.lev2, hlev]
  have hact := hM.act.1
  obtain ⟨hEq, ⟨hL, -, -, hcU, hph, z, hz, hO⟩, hRat⟩ := hO
  obtain ⟨ζ, hζL, ⟨m, hm, hζ⟩, hO⟩ := hO ()
  obtain ⟨-, hph', z', -, hrow⟩ := hrow
  obtain ⟨ζ₀, hζ₀L, ⟨m₀, hm₀, hζ₀⟩, hrow₀⟩ := hrow t₀
  have hζ₀0 : ζ₀ ≠ 0 := fun h0 => by simp [h0, hm₀.ne'] at hζ₀
  have hph0 : ph' ≠ 0 := fun h0 => by simp [h0] at hph'
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℝ) := ⟨_, rfl⟩
  have mul4 : ∀ a b d : ℂ, a * b * (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℝ) * d = a * s * (b * d) :=
    fun a b d => by rw [hs]; ring
  have key : ∀ q, ∀ f ∈ cuspOver M κ, (ph' * ζ * s) * geo M (cE M.s0) z f q = (ph * ζ₀ * s) * geo M cc' z' f q := by
    intro q
    refine geo_agree O M hle hact hspan q ?_
    rintro g hg ⟨x, hx, hgx⟩
    have hg' := ((mem_cusp _ _ _ _ _ _).1 hg).1
    obtain ⟨x', hx', hth, hsum⟩ := hext x hx
    have h1 : ph * O.thAd () x q = ζ * s * geo O (cE O.s0) z g q := ((hO x hx).2 g hg' hgx q).trans (mul4 _ _ _)
    have h2 : ph' * M.thAd t₀ x' q = ζ₀ * s * geo M cc' z' (rulBC hle g) q :=
      ((hrow₀ x' hx').2 _ (GlobalTheory.FieldBCModel.rulBC_mem_sec hle hg') (hsum g hg' hgx) q).trans (mul4 _ _ _)
    rw [geo_rulBC O M hle hlev (e ▸ hact) cE z hg']
    rw [hth] at h2
    linear_combination ph * h2 - ph' * h1
  refine ⟨?_, ⟨hL.trans hle, (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ M.hle).2 _ _,
    (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ M.hle _ _ hact).2, ?_, hph, z, hz, fun t => ?_⟩, ?_⟩
  · unfold OMDat.EquivAt
    rw [phi_eq M O cE, e]
    exact hEq
  · have : ∀ s, s = O.s0 → ∀ k, ‖cE s k‖ = 1 := fun s hs => hs ▸ hcU
    exact this _ ((sOv_eq C _ _).trans (sOv_eq C _ _).symm)
  · obtain ⟨ζt, hζtL, ⟨mt, hmt, hζt⟩, ht⟩ := hrow t
    refine ⟨ζt * ζ * ζ₀⁻¹, mul_mem (mul_mem hζtL hζL) (inv_mem hζ₀L), ⟨mt * m * m₀, by positivity, ?_⟩,
      fun x hx => ⟨(ht x hx).1, fun f hf hfx q => ?_⟩⟩
    · have a1 : ζt ^ (mt * m * m₀) = 1 := by rw [mul_assoc, pow_mul, hζt, one_pow]
      have a2 : ζ ^ (mt * m * m₀) = 1 := by rw [mul_comm mt m, mul_assoc, pow_mul, hζ, one_pow]
      have a3 : ζ₀ ^ (mt * m * m₀) = 1 := by rw [mul_comm, pow_mul, hζ₀, one_pow]
      rw [mul_pow, mul_pow, inv_pow, a1, a2, a3]
      simp
    · obtain ⟨f₀, hf₀, hf₀x⟩ := (ht x hx).1
      obtain rfl : f = f₀ := isSum_unique hM t hf ((mem_cusp _ _ _ _ _ _).1 hf₀).1 hfx hf₀x
      have h1 : ph' * M.thAd t x q = ζt * s * geo M cc' z' f q := ((ht x hx).2 f hf hfx q).trans (mul4 _ _ _)
      have h2 := key q f hf₀
      have i1 := mul_inv_cancel₀ hζ₀0
      refine Eq.trans ?_ (mul4 _ _ _).symm
      show ph * M.thAd t x q = ζt * ζ * ζ₀⁻¹ * s * geo M (cE M.s0) z f q
      apply mul_left_cancel₀ (mul_ne_zero hph0 hζ₀0)
      linear_combination (ph * ζ₀) * h1 - ζt * h2 - (ph' * ζt * ζ * s * geo M (cE M.s0) z f q) * i1
  · unfold OMDat.PhRat
    rw [phi_eq M O cE]
    exact hRat

theorem oneMapOf_comap {Tp' : Type} {O : OMDat C R i Tp tup} (f : Tp' → Tp) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ cc ph}
    (h : O.OneMapOf κ v₀ cc ph) : (comap O f).OneMapOf κ v₀ cc ph := by
  obtain ⟨h1, ⟨h2, h3, h4, h5, h6, z, hz, h7⟩, h8⟩ := h
  exact ⟨h1, ⟨h2, h3, h4, h5, h6, z, hz, fun t => h7 (f t)⟩, h8⟩

end Compare

section Row

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

def IdentityRow (i : Fin D.R.m) : Prop :=
  ∀ (Tp : Type) (tup : Tp → T0) (O' : OMDat T.toCore R i Tp tup), D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F →
    O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0) → ∃ cc ph, RowAt O' (κ i) cc ph

def PinnedDataExist (i : Fin D.R.m) : Prop :=
  QGuard R → ∃ O' : OMDat T.toCore R i T0 id, D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F ∧
    O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0)

variable {T R κ v₀}


variable (T R κ v₀)

end Row

end GlobalTheory.OneMapAll
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharSupportedIdeleEqLocalAbsValue
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharSupportedIdeleEqLocalAbsValue
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ModuLocal

theorem infComp_eq_one {F : Type} [Field F] [NumberField F] {v : Pl (F := F)} {u : (AF F)ˣ}
    (hu : At (evFin F v) ((u : AF F) - 1)) (w : NumberField.InfinitePlace F) : (u : AF F).1 w = 1 := by
  have h := hu (pairA F 1 0) (by change evalV F v 0 = 0; exact map_zero _)
  have h' : (1 : Ainf F) * ((u : AF F).1 - 1) = 0 := congrArg Prod.fst h
  rw [one_mul, sub_eq_zero] at h'
  rw [h']
  rfl

theorem finComp_eq_one {F : Type} [Field F] [NumberField F] {v : Pl (F := F)} {u : (AF F)ˣ}
    (hu : At (evFin F v) ((u : AF F) - 1)) {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    (u : AF F).2 w = 1 := by
  have h := hu (pairA F 0 (GlobalTheory.AdelicU.singleFin w 1))
    (by change evalV F v (GlobalTheory.AdelicU.singleFin w 1) = 0; exact GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hw) 1)
  have h2 : GlobalTheory.AdelicU.singleFin w 1 * ((u : AF F).2 - 1) = 0 := congrArg Prod.snd h
  have h' := congrArg (evalV F w) h2
  rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul, map_sub, map_zero, sub_eq_zero] at h'
  rw [← (map_one (evalV F w) : evalV F w 1 = 1)]
  exact h'

end GlobalTheory.ModuLocal

theorem GlobalTheory.ModuLocal.distribHaarChar_eq_nabs_of_at : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (u : (AF F)ˣ), At (evFin F v) ((u : AF F) - 1) →
    ((MeasureTheory.distribHaarChar (AF F) u : NNReal) : ℝ) = GlobalTheory.SplitWeil.nabs (Fv F v) (Units.map (evFin F v : AF F →* Fv F v) u) := by
  intro F _ _ v u hu
  rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing F u, GroundTheory.Global.IdeleGroup.ideleModule_eq]
  have hinf : (∏ w : NumberField.InfinitePlace F, ‖(u : AF F).1 w‖ ^ w.mult) = 1 :=
    Finset.prod_eq_one fun w _ => by rw [GlobalTheory.ModuLocal.infComp_eq_one hu w, norm_one, one_pow]
  have hfin : (∏ᶠ w : HeightOneSpectrum (𝓞 F), ‖(u : AF F).2 w‖) = ‖(u : AF F).2 v‖ :=
    finprod_eq_single _ v fun w hw => by rw [GlobalTheory.ModuLocal.finComp_eq_one hu hw, norm_one]
  have hloc := ((GlobalTheory.CompletionNorm.norm_nabs_valuation F v).1 (Units.map (evFin F v : AF F →* Fv F v) u)).1
  refine (congrArg₂ (· * ·) hinf hfin).trans ?_
  rw [one_mul]
  exact hloc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharSupportedIdeleEqLocalAbsValueStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.distribHaarChar_supportedIdele_eq_localAbsValue : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (u : (AF F)ˣ), At (evFin F v) ((u : AF F) - 1) →
    ((MeasureTheory.distribHaarChar (AF F) u : NNReal) : ℝ) = GlobalTheory.SplitWeil.nabs (Fv F v) (Units.map (evFin F v : AF F →* Fv F v) u) := by
  first | exact @GlobalTheory.ModuLocal.distribHaarChar_eq_nabs_of_at | exact GlobalTheory.ModuLocal.distribHaarChar_eq_nabs_of_at | (intros; apply GlobalTheory.ModuLocal.distribHaarChar_eq_nabs_of_at <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepLevelCoverPrincipalLevelLawsGalois
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepLevelCoverPrincipalLevelLawsGalois
set_option autoImplicit false

noncomputable section

open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC

namespace GlobalTheory.DeepLaws

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isGalois_of_aut (K L : IntermediateField ℚ ℂ) [FiniteDimensional ℚ L] (j : K →+* L)
    (hj : ∀ a : K, ((j a : L) : ℂ) = a)
    (hs : ∀ s : ℂ ≃+* ℂ, (∀ a ∈ K, s a = a) → ∀ a ∈ L, s a ∈ L) :
    letI : Algebra K L := j.toAlgebra
    IsGalois K L := by
  letI : Algebra K L := j.toAlgebra
  haveI : IsScalarTower K L ℂ := IsScalarTower.of_algebraMap_eq fun a => (hj a).symm
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun a => by simp
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  have : Normal K L := by
    refine normal_iff.2 fun x => ⟨Algebra.IsIntegral.isIntegral x, ?_⟩
    refine Polynomial.Splits.of_splits_map (algebraMap L ℂ) (IsAlgClosed.splits _) fun a ha => ?_
    have hroot : a ∈ (minpoly K x).rootSet ℂ := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at ha
      exact Finset.mem_coe.2 (Multiset.mem_toFinset.2 ha)
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at hroot
    obtain ⟨φ, rfl⟩ := hroot
    obtain ⟨s, hsφ⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.extendEmb_holds L inferInstance (φ.restrictScalars ℚ)
    have hfix : ∀ a ∈ K, s a = a := by
      intro a ha
      have h1 := hsφ (j ⟨a, ha⟩)
      rw [hj] at h1
      refine h1.trans ?_
      exact φ.commutes (⟨a, ha⟩ : K)
    have hmem : s (x : ℂ) ∈ L := hs s hfix _ x.2
    refine ⟨⟨s (x : ℂ), hmem⟩, ?_⟩
    exact hsφ x
  exact IsGalois.mk

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l}

theorem frPt_eq {S : Type} [CommRing S] [Algebra c.F S] {y z : FrPt Xo c S} (hx : y.x = z.x) (hu : y.u = z.u)
    (hs : HEq y.s z.s) : y = z := by
  obtain ⟨x, xo, u, t, e, b, s, g⟩ := y
  obtain ⟨x', xo', u', t', e', b', s', g'⟩ := z
  obtain rfl : x = x' := hx
  obtain rfl : u = u' := hu
  obtain rfl : s = s' := eq_of_heq hs
  rfl

theorem laws_galois_pull : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ g τ k, ‖dmin ((Y.U σ).X (Y.dict σ g).1).Gm (Y.dict σ g).2 τ k‖ = 1) → (∀ σ, GoodEmb Y.d.c₂ σ → ∃ hr : (D.sp.W j).rank = D.R.r, ∀ k, ModelW (D.sp.W j) hr ((Y.U σ).X k)) → Laws D j Y.d.Xo₂ Y.d.c₂ Y.U Y.dict ∧ (letI : Algebra T.Q.c.F Y.d.c₂.F := ((Y.d.eF : Y.c'.F →+* Y.d.c₂.F).comp (incF T.Q.c Y.c' Y.hle)).toAlgebra; IsGalois T.Q.c.F Y.d.c₂.F) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ g, Y.Pull f g ↔ Pull Y.d (rulBC Y.hle f) g := by
  intro D T j Y e o hJ hj hG hdm hmod
  refine ⟨?_, ?_, ?_⟩
  · exact
      { inR := hj
        host := hJ.pins.1
        dat := hJ.pins.2.2.2 j hj
        levA := hG.lev.2
        unf := hG.unf
        chiTriv := hG.chiTriv
        dictU := fun σ hσ => by
          obtain ⟨th, hr, h1, h2⟩ := hG.dictU σ hσ
          refine ⟨Y.Kf, th, hr, ?_, h1, h2, hdm σ hσ⟩
          have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * Y.d.pd := by
            rw [hG.lev.1.2.1, hJ.pins.2.1.1]
          rw [hM]
          exact hG.levelK
        modelW := hmod }
  · haveI := Y.d.c₂.fin
    refine isGalois_of_aut T.Q.c.F Y.d.c₂.F _ (fun a => rfl) fun s hs a ha => ?_
    have hF := Y.d.hF
    rw [hF] at ha ⊢
    exact hG.normal s hs a ha
  · intro a n f hf g
    have hV := (rulBC_sec_val_linear D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c Y.c' Y.hle).1 a n f hf
    constructor
    · intro hP k _ _ _ _ hk y₂ y hO
      letI : Algebra T.Q.c.F k := resAlg Y.hle k
      have hA : AlgOver T.Q.c Y.c' Y.hle k := fun _ => rfl
      rw [hV.2 k hA y]
      exact hP k hA hk y₂ y (y.res Y.hle hA) hO rfl rfl HEq.rfl
    · intro hP k _ _ _ _ _ hA hk y₂ y' y hO hx hu hs
      have hy : y = y'.res Y.hle hA := frPt_eq hx hu hs
      rw [hy, ← hV.2 k hA y']
      exact hP k hk y₂ y' hO

end GlobalTheory.DeepLaws

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepLevelCoverPrincipalLevelLawsGaloisStatement
open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deepLevelCover_principalLevel_laws_galois : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ g τ k, ‖dmin ((Y.U σ).X (Y.dict σ g).1).Gm (Y.dict σ g).2 τ k‖ = 1) → (∀ σ, GoodEmb Y.d.c₂ σ → ∃ hr : (D.sp.W j).rank = D.R.r, ∀ k, ModelW (D.sp.W j) hr ((Y.U σ).X k)) → Laws D j Y.d.Xo₂ Y.d.c₂ Y.U Y.dict ∧ (letI : Algebra T.Q.c.F Y.d.c₂.F := ((Y.d.eF : Y.c'.F →+* Y.d.c₂.F).comp (incF T.Q.c Y.c' Y.hle)).toAlgebra; IsGalois T.Q.c.F Y.d.c₂.F) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ g, Y.Pull f g ↔ Pull Y.d (rulBC Y.hle f) g := by
  first | exact @GlobalTheory.DeepLaws.laws_galois_pull | exact GlobalTheory.DeepLaws.laws_galois_pull | (intros; apply GlobalTheory.DeepLaws.laws_galois_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOfLowSmoothLines
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.IoExtPf

section Rep

open Formalism.MainNotions.S

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool} {lam : Fin n → ℝ}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem exists_ext_mem (hU : IsURepOn (UJset ε) σ) {Λ : Fin n → ℝ} {S : Submodule ℂ H} (hS : IsKTypeOf ε σ Λ S) :
    ∃ w ∈ S, ‖w‖ = 1 ∧ IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Λ (revNeg ε a)) w := by
  obtain ⟨v, hvS, hv0, hv⟩ := hS.2.2.2.1
  have hK := pM_mem (revNeg ε) (eps_revNeg ε)
  have hn : ‖σ (pM (revNeg ε)) v‖ = ‖v‖ := hU.2.1 _ (kset_uj hK) v
  have hp : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
  refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • σ (pM (revNeg ε)) v, ?_, ?_, isWtOn_smul (isWtOn_perm hU _ (eps_revNeg ε) hv) _⟩
  · exact Submodule.smul_mem _ _ (hS.2.1 _ hK v hvS)
  · rw [norm_smul, hn, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hp]

theorem lowK_irred (hσ : IsDS ε lam σ)
    (hl : ∀ w w' : H, ‖w‖ = 1 → w ∈ lowKSub ε lam σ →
      IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) w → ‖w'‖ = 1 → w' ∈ lowKSub ε lam σ →
      IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) w' → ∃ c : ℂ, w' = c • w)
    (N : Submodule ℂ H) (hN : N ≤ lowKSub ε lam σ) (hst : IsKStableOn ε σ N) : N = ⊥ ∨ N = lowKSub ε lam σ := by
  obtain ⟨-, -, hU, -, -, ⟨S, hS⟩, -⟩ := hσ
  have hle : ∀ S', IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S' → S' ≤ lowKSub ε lam σ := fun S' h =>
    le_sSup (s := {S | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S}) h
  have key : lowKSub ε lam σ = S := by
    refine le_antisymm (sSup_le fun S' hS' => ?_) (hle S hS)
    obtain ⟨w, hw, hw1, hwt⟩ := exists_ext_mem hU hS
    obtain ⟨w', hw', hw1', hwt'⟩ := exists_ext_mem hU hS'
    obtain ⟨c, hc⟩ := hl w w' hw1 (hle S hS hw) hwt hw1' (hle S' hS' hw') hwt'
    have hm : w' ∈ S' ⊓ S := ⟨hw', hc ▸ S.smul_mem c hw⟩
    rcases hS'.2.2.1 (S' ⊓ S) inf_le_left (fun g hg v hv => ⟨hS'.2.1 g hg v hv.1, hS.2.1 g hg v hv.2⟩) with h | h
    · rw [h, Submodule.mem_bot] at hm
      rw [hm, norm_zero] at hw1'
      exact absurd hw1' zero_ne_one
    · exact h ▸ inf_le_right
  rw [key] at hN ⊢
  exact hS.2.2.1 N hN hst

end Rep

section Minors

variable {D : D7} {m n : ℕ}

theorem minor_ne (τ : D.what₂.Tau) (a b k : ℕ) (ha : a + k ≤ m) (hb : b + k ≤ n) :
    (Matrix.of fun α β : Fin k => (varF τ (a + β) (b + α) : MvPolynomial (FVar D m n) ℂ)).det ≠ 0 := by
  intro h
  have h1 := congrArg (MvPolynomial.eval fun x : FVar D m n => if (x.2.1 : ℕ) + b = x.2.2 + a then (1 : ℂ) else 0) h
  rw [RingHom.map_det, map_zero] at h1
  have h2 : (MvPolynomial.eval fun x : FVar D m n => if (x.2.1 : ℕ) + b = x.2.2 + a then (1 : ℂ) else 0).mapMatrix
      (Matrix.of fun α β : Fin k => (varF τ (a + β) (b + α) : MvPolynomial (FVar D m n) ℂ)) = 1 := by
    ext α β
    have hα := α.2
    have hβ := β.2
    have hr : a + β < m ∧ b + α < n := ⟨by omega, by omega⟩
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, varF, dif_pos hr, MvPolynomial.eval_X,
      Matrix.one_apply, Fin.ext_iff]
    exact if_congr ⟨fun h => by omega, fun h => by omega⟩ rfl rfl
  rw [h2, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem delta_ne (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (hpq : ∀ τ, p τ + q τ ≤ m) (hmn : m ≤ n) :
    (delta p q ap am : MvPolynomial (FVar D m n) ℂ) ≠ 0 := by
  unfold delta deltaAt
  refine Finset.prod_ne_zero_iff.2 fun τ _ => mul_ne_zero
    (Finset.prod_ne_zero_iff.2 fun i hi => pow_ne_zero _ ?_) (Finset.prod_ne_zero_iff.2 fun i hi => pow_ne_zero _ ?_)
  · have := Finset.mem_range.1 hi
    have := hpq τ
    have h := minor_ne (m := m) (n := n) τ 0 0 (i + 1) (by omega) (by omega)
    simpa only [minorPlus, zero_add] using h
  · have := Finset.mem_range.1 hi
    have := hpq τ
    exact minor_ne (m := m) (n := n) τ (p τ) (n - (i + 1)) (i + 1) (by omega) (by omega)

theorem Delta_ne (i : Fin D.R.m) : RealDat.Delta (D := D) i ≠ 0 := by
  refine delta_ne _ _ _ _ (fun τ => ?_) ((rank_Wc i).le.trans (r_le_V i))
  rw [D.sp.W_sigval _ (Nat.le_add_left _ _) i.2, rank_Wc]
  have := i.2
  simp only [Ranks.sigW, Ranks.r]
  omega

end Minors

section Io

open Formalism.MainNotions.S Formalism.IndefR.Mult

variable {D : D7} {W : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel W S)

theorem model_irred (hs : LowSm M) (hl : ExtLine M) (τ : D.what₂.Tau) (N : Submodule ℂ (M.H τ))
    (hN : N ≤ lowKSub (M.ε τ) (M.lam τ) (M.σ τ)) (hst : IsKStableOn (M.ε τ) (M.σ τ) N) :
    N = ⊥ ∨ N = lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := by
  refine lowK_irred (M.ds τ) (fun w w' h1 h2 h3 h1' h2' h3' => ?_) N hN hst
  obtain ⟨e, he⟩ := exists_isExtVec M hs
  have hu : ∀ (x : M.sm τ), ‖(x : M.H τ)‖ = 1 → (x : M.H τ) ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) →
      IsWtOn (Formalism.REAL.Kset (M.ε τ)) (M.σ τ) (extWt M τ) (x : M.H τ) → IsExtVec M (Function.update e τ x) := by
    intro x a b c ρ
    by_cases h : ρ = τ
    · subst h
      rw [Function.update_self]
      exact ⟨a, b, c⟩
    · rw [Function.update_of_ne h]
      exact he ρ
  obtain ⟨c, -, hc⟩ := hl _ _ (hu ⟨w, hs τ h2⟩ h1 h2 h3) (hu ⟨w', hs τ h2'⟩ h1' h2' h3') τ
  rw [Function.update_self, Function.update_self] at hc
  exact ⟨c, congrArg Subtype.val hc⟩

theorem inj_factor (hs : LowSm M) (hl : ExtLine M) (τ : D.what₂.Tau) {X : Type} [AddCommGroup X] [Module ℂ X]
    (f : LowT M →ₗ[ℂ] X) (om : Matrix (Fin W.rank) (Fin W.rank) ℂ → X →ₗ[ℂ] X)
    (hf : ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (v : ∀ ρ, lowT M ρ) (u : lowT M τ),
      ((u : M.sm τ) : M.H τ) = M.σ τ k ((v τ : M.sm τ) : M.H τ) →
      om k (f (PiTensorProduct.tprod ℂ v)) = f (PiTensorProduct.tprod ℂ (Function.update v τ u)))
    (v : ∀ ρ, lowT M ρ) (hv : f (PiTensorProduct.tprod ℂ v) ≠ 0) (x : lowT M τ)
    (hx : f (PiTensorProduct.tprod ℂ (Function.update v τ x)) = 0) : x = 0 := by
  let g : lowT M τ →ₗ[ℂ] X := f ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap v τ
  have hg : ∀ y, g y = f (PiTensorProduct.tprod ℂ (Function.update v τ y)) := fun y => rfl
  let j : lowT M τ →ₗ[ℂ] M.H τ := (M.sm τ).subtype ∘ₗ (lowT M τ).subtype
  have hj : Function.Injective j := Subtype.val_injective.comp Subtype.val_injective
  have hst := GlobalTheory.LowKProj.lowKSub_stable (M.ε τ) (M.lam τ) (M.σ τ)
  rcases model_irred M hs hl τ ((LinearMap.ker g).map j) (by rintro _ ⟨y, -, rfl⟩; exact y.2) (by
      rintro k hk _ ⟨y, hy, rfl⟩
      have hm : M.σ τ k (j y) ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := hst k hk _ y.2
      refine ⟨⟨⟨_, hs τ hm⟩, hm⟩, ?_, rfl⟩
      have := hf k hk (Function.update v τ y) ⟨⟨_, hs τ hm⟩, hm⟩ (by rw [Function.update_self]; rfl)
      rw [Function.update_idem, ← hg, ← hg, (LinearMap.mem_ker.1 hy : g y = 0), map_zero] at this
      exact this.symm) with h | h
  · have : j x ∈ (LinearMap.ker g).map j := ⟨x, hx, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact hj (this.trans (map_zero j).symm)
  · have : j (v τ) ∈ (LinearMap.ker g).map j := by rw [h]; exact (v τ).2
    obtain ⟨y, hy, hy'⟩ := this
    rw [hj hy'] at hy
    have h0 : g (v τ) = 0 := hy
    rw [hg, Function.update_eq_self] at h0
    exact absurd h0 hv

end Io

end GlobalTheory.AdTh.IoExtPf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFinitePointReadsClassicalTranslation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFinitePointReadsClassicalTranslation
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.NormExact

theorem heisO_finPt_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ G f, Reads ψ θ hS hT cc δ r G f → ∀ z : Matrix (Fin d) (Fin a) D.host.E,
    Reads ψ θ hS hT cc δ r (U D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) G) (heisO ψ S T (finPt hS hT r z) f) := by
  intro D ψ θ S T a d hS hT cc δ r hs G f hf z
  subst hS hT
  have hc := hs.crv
  have hr := hs.scale
  have hr0 : r ≠ 0 := IsScale.ne_zero hc.1.1 hr
  rw [reads_iff hc hr] at hf ⊢
  refine ⟨GlobalTheory.TwistFactorCompare.isTheta_heisO hs.std hf.1 _, fun w hw => ?_⟩
  set X : VC D S.rank T.rank := fun τ i j => embT D τ (r⁻¹ * z i j) with hXdef
  have hX : (fun τ a b => -(((GlobalTheory.FockPos.frAt (1 : GL (Fin T.rank) D.host.E) τ)⁻¹ *
      Matrix.of (GlobalTheory.VacUnique.infRat S T (Matrix.of fun i j => -(r⁻¹ * z i j)) τ) *
      GlobalTheory.FockPos.frAt (1 : GL (Fin S.rank) D.host.E) τ) a b)) = X := by
    funext τ a b
    have e : ∀ n, GlobalTheory.FockPos.frAt (D := D) (1 : GL (Fin n) D.host.E) τ = 1 := fun n =>
      Matrix.map_one _ (map_zero _) (map_one _)
    simp only [e, inv_one, Matrix.one_mul, Matrix.mul_one]
    show -(embT D τ (-(r⁻¹ * z a b))) = embT D τ (r⁻¹ * z a b)
    rw [map_neg, neg_neg]
  have h := GlobalTheory.MovedTrans.heisO_finRat_real ψ θ S T 1 1 (by simp [Formalism.UG.cT_one, hs.gS])
    (by simp [Formalism.UG.cT_one, hs.gT]) hs.std hs.inf f hf.1 (fun Z => G fun τ i j => δ * embT D τ r * Z τ i j) hf.2
    (Matrix.of fun i j => -(r⁻¹ * z i j)) _ hX.symm w hw
  have e1 : finPt (rfl : S.rank = S.rank) (rfl : T.rank = T.rank) r z =
      GlobalTheory.VacUnique.finRat S T (Matrix.of fun i j => -(r⁻¹ * z i j)) := rfl
  have hpt : pt D (tor0 D cc δ) δ z = fun τ i j => δ * embT D τ r * X τ i j := by
    funext τ i j
    show δ * embT D τ (z i j) = δ * embT D τ r * embT D τ (r⁻¹ * z i j)
    rw [mul_assoc, ← map_mul, ← mul_assoc, mul_inv_cancel₀ hr0, one_mul]
  rw [e1, h, hpt]
  simp only [U]
  rw [Hf_scale hc hr, Hf_scale hc hr]
  have hY : ((fun τ i j => δ * embT D τ r * GlobalTheory.FockPos.zCo θ 1 1 w τ i j) + fun τ i j => δ * embT D τ r * X τ i j) =
      fun τ i j => δ * embT D τ r * (GlobalTheory.FockPos.zCo θ 1 1 w + X) τ i j := by
    funext τ i j
    simp only [Pi.add_apply]
    ring
  rw [hY]

end GlobalTheory.NormExact
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFinitePointReadsClassicalTranslationStatement
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergFinitePoint_reads_classicalTranslation : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ G f, Reads ψ θ hS hT cc δ r G f → ∀ z : Matrix (Fin d) (Fin a) D.host.E,
    Reads ψ θ hS hT cc δ r (U D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) G) (heisO ψ S T (finPt hS hT r z) f) := by
  first | exact @GlobalTheory.NormExact.heisO_finPt_reads | exact GlobalTheory.NormExact.heisO_finPt_reads | (intros; apply GlobalTheory.NormExact.heisO_finPt_reads <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionThetaTransformRationalDarboux
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionThetaTransformRationalDarboux
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaTransformTheta

theorem isThetaFunO_thetaTr : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
          Formalism.IndefR.Datum.IsThetaFunO ψ S T (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ) := by
  intro D ψ hψ S T JA JB ξ hA hB κ _ co hco φ hφ
  exact
    { quasi := fun γ w => GlobalTheory.T.thetaTransform_rational_translate_quasiInvariant D ψ hψ S T JA JB ξ hA hB κ co hco φ hφ γ w
      level := GlobalTheory.T.thetaTransform_fixed_by_small_finiteHeisenberg D ψ hψ S T JA JB ξ hA hB κ co hco φ hφ
      cont := GlobalTheory.T.continuous_thetaTransform_adelicSchwartz D ψ hψ S T JA JB ξ hA hB κ co hco φ hφ
      smooth := fun k L hL hfin w => GlobalTheory.T.contDiff_thetaTransform_adelicSchwartz_realDirections D ψ hψ S T JA JB ξ hA hB κ co hco φ hφ k L hL hfin w }

end GlobalTheory.ThetaTransformTheta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionThetaTransformRationalDarbouxStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFunction_thetaTransform_rationalDarboux : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
          Formalism.IndefR.Datum.IsThetaFunO ψ S T (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ) := by
  first | exact @GlobalTheory.ThetaTransformTheta.isThetaFunO_thetaTr | exact GlobalTheory.ThetaTransformTheta.isThetaFunO_thetaTr | (intros; apply GlobalTheory.ThetaTransformTheta.isThetaFunO_thetaTr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceSchwartzBruhatVacuumConditionEqSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceTensorLatticeSelfDualSymplectic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceTensorLatticeSelfDualSymplectic
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertLatSelfDual

theorem latAtV_selfDual_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ), X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z →
      (z ∈ latAtV X Y v ↔ ∀ γ ∈ latAtV X Y v,
        B.ψ (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) Y.J) z γ) = 1) := by
  intro F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY v _w _hin z hz
  exact GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B n d X Y r s r' s' hB hX hY v z hz

end GlobalTheory.InertLatSelfDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceTensorLatticeSelfDualSymplecticStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_tensorLattice_selfDual_symplectic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ), X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z →
      (z ∈ latAtV X Y v ↔ ∀ γ ∈ latAtV X Y v,
        B.ψ (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) Y.J) z γ) = 1) := by
  first | exact @GlobalTheory.InertLatSelfDual.latAtV_selfDual_inert | exact GlobalTheory.InertLatSelfDual.latAtV_selfDual_inert | (intros; apply GlobalTheory.InertLatSelfDual.latAtV_selfDual_inert <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceSchwartzBruhatVacuumConditionEqSmul
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.VacUniqInert

theorem eq_smul_of_eigen {K κ : Type} [Field K] [Fintype κ] [Invertible (2 : K)] (ψ₀ : AddChar K ℂ) {ι : Type}
    (L : ι → (κ → K) × (κ → K)) (c : ι → ℂ)
    (hD : ∀ u : κ → K, (∀ i, (L i).1 = 0 → ψ₀ (u ⬝ᵥ (L i).2) = 1) → ∃ i, (L i).1 = u)
    (f η : (κ → K) → ℂ) (hf : ∀ i, schr ψ₀ (L i) f = c i • f) (hη : ∀ i, schr ψ₀ (L i) η = c i • η)
    (hη0 : η ≠ 0) : ∃ c' : ℂ, f = c' • η := by
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, η X₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hη0 (funext h)
  have hne : ∀ t, ψ₀ t ≠ 0 := fun t h => by
    have e := AddChar.map_add_eq_mul ψ₀ t (-t)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at e
    exact one_ne_zero e
  refine ⟨f X₀ / η X₀, funext fun X => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hu : ∀ i, (L i).1 = 0 → ψ₀ ((X - X₀) ⬝ᵥ (L i).2) = 1
  · obtain ⟨i, hi⟩ := hD _ hu
    have hX : X₀ + (L i).1 = X := by rw [hi]; abel
    have e1 := congrFun (hf i) X₀
    have e2 := congrFun (hη i) X₀
    simp only [schr, Pi.smul_apply, smul_eq_mul, hX] at e1 e2
    have hA := hne (X₀ ⬝ᵥ (L i).2 + ⅟(2 : K) * ((L i).1 ⬝ᵥ (L i).2))
    field_simp
    refine mul_left_cancel₀ hA ?_
    linear_combination η X₀ * e1 - f X₀ * e2
  · push_neg at hu
    obtain ⟨i, hi0, hne1⟩ := hu
    have key : ∀ g : (κ → K) → ℂ, schr ψ₀ (L i) g = c i • g → ∀ Y, ψ₀ (Y ⬝ᵥ (L i).2) * g Y = c i * g Y := by
      intro g hg Y
      have e := congrFun hg Y
      simpa [schr, hi0] using e
    have hc : ψ₀ (X₀ ⬝ᵥ (L i).2) = c i := mul_right_cancel₀ hX₀ (key η (hη i) X₀)
    have hz : ∀ g : (κ → K) → ℂ, schr ψ₀ (L i) g = c i • g → g X = 0 := by
      intro g hg
      by_contra hgX
      have h1 : ψ₀ (X ⬝ᵥ (L i).2) = ψ₀ (X₀ ⬝ᵥ (L i).2) := by
        rw [hc]; exact mul_right_cancel₀ hgX (key g hg X)
      apply hne1
      have e : X ⬝ᵥ (L i).2 = (X - X₀) ⬝ᵥ (L i).2 + X₀ ⬝ᵥ (L i).2 := by rw [sub_dotProduct]; ring
      rw [e, AddChar.map_add_eq_mul] at h1
      exact mul_right_cancel₀ (hne _) (h1.trans (one_mul _).symm)
    rw [hz f (hf i), hz η (hη i), mul_zero]

theorem vac_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ (θ : 𝓞 E), (θ : E) + σ θ = 1 →
      (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) (G.M'.vac v)
          (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • (G.M'.vac v))) →
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ
          (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • φ)) → ∃ c : ℂ, φ = c • G.M'.vac v := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hin θ _ hvac φ hφ hfix
  classical
  have hat : ∀ γ ∈ latAtV G.V' G.W v, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).1
  let cf : latAtV G.V' G.W v → ℂ := fun γ =>
    B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ)
  have hloc : ∀ f ∈ SB (Fin a' × Fin (a + a') → Fv F v), (∀ γ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (G.M'.co.rho B.ψ γ) f
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • f)) →
      ∀ γ : latAtV G.V' G.W v, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) f = cf γ • f := by
    intro f hf h γ
    exact GlobalTheory.TensUniq.eq_of_tens_eq v f _ _ hf fun r hr =>
      (GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v γ (hat γ γ.2) f r hr).symm.trans (h γ γ.2 r hr)
  have hsd : ∀ z, z ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v) ↔
      ∀ l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v), GlobalTheory.LatVac.psiAt B.ψ v (z.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ z.2) = 1 :=
    GlobalTheory.LatVac.DualLoc.map_selfDual v G.M'.co B.ψ (latAtV G.V' G.W v) hat
      (fun z hz => GlobalTheory.T.inertPlace_tensorLattice_selfDual_symplectic F E σ B hTr.base G.V' G.W _ _ _ _ hTr.geo.hV' hTr.geo.hW v w hin z hz)
  have hst : ∀ t ∈ v.adicCompletionIntegers F, ∀ l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v),
      t • l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v) := by
    rintro t ht _ ⟨γ, hγ, rfl⟩
    refine ⟨GlobalTheory.LatVac.liftV v t • γ, (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).2 t ht γ hγ, ?_⟩
    rw [GlobalTheory.LatOpenCpt.locCo_smul, GlobalTheory.LatVac.evFin_liftV]
  have hbd : ∃ c : Fv F v, c ≠ 0 ∧ ∀ l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v), ∀ i,
      c * l.1 i ∈ v.adicCompletionIntegers F := by
    obtain ⟨c, hc0, hc⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded G.V' G.W v G.M'.co hTr.geo.hV'.lat.toIsLattice hTr.geo.hW.lat.toIsLattice
    exact ⟨c, hc0, by rintro _ ⟨γ, hγ, rfl⟩ i; exact (hc γ hγ i).1⟩
  have hD := GlobalTheory.T.exists_second_coordinate_of_orthogonal_selfDual v (GlobalTheory.LatVac.psiAt B.ψ v) _ hsd hst hbd
  refine eq_smul_of_eigen (GlobalTheory.LatVac.psiAt B.ψ v) (fun γ : latAtV G.V' G.W v => GlobalTheory.LatVac.locCo G.M'.co v γ) cf
    (fun u hu => ?_) φ (G.M'.vac v) (hloc φ hφ hfix) (hloc _ (hTr.geo.hM'.vac v).1 hvac) (hTr.geo.hM'.vac v).2.1
  obtain ⟨y', γ, hγ, he⟩ := hD u (by
    rintro y ⟨γ, hγ, he⟩
    have h1 := hu ⟨γ, hγ⟩ (congrArg Prod.fst he)
    have h2 : (GlobalTheory.LatVac.locCo G.M'.co v γ).2 = y := congrArg Prod.snd he
    simp only at h1
    rw [h2] at h1
    exact h1)
  exact ⟨⟨γ, hγ⟩, congrArg Prod.fst he⟩

end GlobalTheory.VacUniqInert
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceSchwartzBruhatVacuumConditionEqSmulStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_schwartzBruhat_vacuumCondition_eq_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ (θ : 𝓞 E), (θ : E) + σ θ = 1 →
      (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) (G.M'.vac v)
          (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • (G.M'.vac v))) →
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ
          (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • φ)) → ∃ c : ℂ, φ = c • G.M'.vac v := by
  first | exact @GlobalTheory.VacUniqInert.vac_unique | exact GlobalTheory.VacUniqInert.vac_unique | (intros; apply GlobalTheory.VacUniqInert.vac_unique <;> assumption)
end
end
