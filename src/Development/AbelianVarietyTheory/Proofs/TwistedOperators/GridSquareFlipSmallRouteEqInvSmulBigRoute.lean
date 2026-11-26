module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SandwichedFlipRouteThroughSmallEqInvConstRouteBi

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TotalTensorThetaLiftEqOfSchwartzEq
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TotalTensorThetaLiftEqOfSchwartzEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FlipRun

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

theorem kerA_sum_of_grid {t : T} {a : Arrow T} (ha : IsGridArrow D.R.m t a) {ι : Type} (L : Finset ι) (w : ι → ℂ)
    (gs : ι → Sch G a) (g₀ : GA D (G.V a.src)) (h : GA D (G.V a.tgt)) :
    W.kerA a (∑ l ∈ L, w l • gs l) g₀ h = ∑ l ∈ L, w l * W.kerA a (gs l) g₀ h := by
  rcases ha with ⟨i, j, -, -, rfl⟩ | ⟨i, j, -, -, rfl⟩ <;>
    set_option synthInstance.maxHeartbeats 100000 in
      simp [GridData.Weil.kerA, GridData.Weil.ker, thetaKO, map_sum, map_smul, Finset.sum_apply]

theorem liftA_sum_datum (M : Vol G) {t : T} {a : Arrow T} (ha : IsGridArrow D.R.m t a) {ι : Type} (L : Finset ι)
    (w : ι → ℂ) (gs : ι → Sch G a) (F : Fn G a.src) (hc : ∀ l ∈ L, LiftConv W M a (gs l) F) :
    liftA W M a (∑ l ∈ L, w l • gs l) F = ∑ l ∈ L, w l • liftA W M a (gs l) F := by
  funext h
  simp only [liftA_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, kerA_sum_of_grid ha, Finset.sum_mul]
  rw [integral_finsetSum _ fun l hl => ?_]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun x => ?_)
    ring
  · have := (hc l hl h).const_mul (w l)
    refine this.congr (.of_forall fun x => ?_)
    simp only
    ring

theorem liftA_sum_form (M : Vol G) (a : Arrow T) (f : Sch G a) {ι : Type} (s : Finset ι) (w : ι → ℂ)
    (Fs : ι → Fn G a.src) (hc : ∀ k ∈ s, LiftConv W M a f (Fs k)) :
    liftA W M a f (∑ k ∈ s, w k • Fs k) = ∑ k ∈ s, w k • liftA W M a f (Fs k) := by
  funext h
  simp only [liftA_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum _ fun k hk => ?_]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun x => ?_)
    ring
  · have := (hc k hk h).const_mul (w k)
    refine this.congr (.of_forall fun x => ?_)
    simp only
    ring

theorem liftA_zero_form (M : Vol G) (a : Arrow T) (f : Sch G a) : liftA W M a f 0 = 0 := by
  have := liftA_smul W M a f 0 0
  rwa [zero_smul, zero_smul] at this

theorem sum_liftP_eq_zero {μ₀ : T} (hL : L.Is μ₀) (M : Vol G) (ρ : RealMatch W) (t : T) {e : AE D}
    (he : IsIdemSum e (locPl G t)) (hC : CuspStep W M ρ t) {X : Node} :
    ∀ {Y : Node} (p : Path T X Y), OnGrid D.R.m t p → ∀ {ι : Type} (s : Finset ι) (c : ι → ℂ) (φ d : ι → PureT G p),
      (∀ k ∈ s, VecAll ρ e p (φ k) (d k)) → (∀ x : ArgT G p, HalfAll e p x → ∑ k ∈ s, c k * famProd p (φ k) x = 0) →
      ∀ (P : PolT G p) (F : Fn G X), IsCuspListed W.θ X F →
      ∑ k ∈ s, c k • liftP W M p (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) (d k) P) F = 0
  | _, .nil, _, ι, s, c, φ, d, _, hsum, P, F, _ => by
    have h0 : ∑ k ∈ s, c k = 0 := by
      have := hsum () trivial
      simpa [famProd] using this
    show ∑ k ∈ s, c k • F = 0
    rw [← Finset.sum_smul, h0, zero_smul]
  | _, .snoc a p, hg, ι, s, c, φ, d, hv, hsum, P, F, hF => by
    classical
    have ha : IsGridArrow D.R.m t a := hg.last
    have hmodel := GlobalTheory.FlipRun.exists_arrowModel (G := G) (t := t) ρ hL he ha
    rcases hmodel with ⟨Tm, h1, -, h3⟩
    have hmem : ∀ k ∈ s, (φ k).2 ∈ LocTensor.sbSpace e (latA G a) := fun k hk => ((h1 _ _).1 (hv k hk).2).1
    have hd2 : ∀ k ∈ s, (d k).2 = Tm (φ k).2 := fun k hk => ((h1 _ _).1 (hv k hk).2).2
    let b := Module.Basis.ofVectorSpace ℂ (LocTensor.sbSpace e (latA G a))
    let v : ι → LocTensor.sbSpace e (latA G a) := fun k => if h : (φ k).2 ∈ LocTensor.sbSpace e (latA G a) then ⟨_, h⟩ else 0
    have hv' : ∀ k ∈ s, ((v k : LocTensor.sbSpace e (latA G a)) : Sch G a) = (φ k).2 := fun k hk => by
      simp only [v, dite_eq_left (hmem k hk)]
    let r : ι → Module.Basis.ofVectorSpaceIndex ℂ (LocTensor.sbSpace e (latA G a)) → ℂ := fun k l => b.repr (v k) l
    let Ls := s.biUnion fun k => (b.repr (v k)).support
    have hexp : ∀ k ∈ s, (φ k).2 = ∑ l ∈ Ls, r k l • ((b l : LocTensor.sbSpace e (latA G a)) : Sch G a) := by
      intro k hk
      rw [← hv' k hk]
      conv_lhs => rw [← b.linearCombination_repr (v k)]
      rw [Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem (fun k => (b.repr (v k)).support) hk)
          (fun i (x : ℂ) => x • b i) (fun _ _ => zero_smul _ _), Submodule.coe_sum]
      rfl
    let Fk : ι → Fn G a.src := fun k => liftP W M p (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) (d k).1 P.1) F
    have cusp_zip : ∀ {Y : Node} (q : Path T X Y), OnGrid D.R.m t q →
        ∀ (φq dq : PureT G q), VecAll ρ e q φq dq → ∀ Q : PolT G q,
          IsCuspListed W.θ Y
            (liftP W M q (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) dq Q) F) := by
      intro Y q
      induction q with
      | nil =>
        intro _ _ _ _ _
        exact hF
      | snoc b q ih =>
        intro hq φq dq hvq Q
        exact (hC b hq.last e he φq.2 dq.2 hvq.2 Q.2 _ (ih hq.init φq.1 dq.1 hvq.1 Q.1)).2
    have hFk : ∀ k ∈ s, IsCuspListed W.θ a.src (Fk k) := fun k hk =>
      cusp_zip p hg.init (φ k).1 (d k).1 (hv k hk).1 P.1
    let g : Module.Basis.ofVectorSpaceIndex ℂ (LocTensor.sbSpace e (latA G a)) → Sch G a :=
      fun l => W.fock a.pair (Tm (b l)) P.2
    have hconv : ∀ l, ∀ k ∈ s, LiftConv W M a (g l) (Fk k) := fun l k hk =>
      (hC a hg.last e he (b l) (Tm (b l)) ((h1 _ _).2 ⟨(b l).2, rfl⟩) P.2 (Fk k) (hFk k hk)).1
    have hstep : ∀ k ∈ s, W.fock a.pair (d k).2 P.2 = ∑ l ∈ Ls, r k l • g l := by
      intro k hk
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hd2 k hk, hexp k hk, map_sum]
      simp only [map_smul]
      exact GlobalTheory.SpecFac.pureTensorO_sum W.ψ_std W.θ_is _ _ _ _ Ls (r k) (fun l => Tm (b l))
        (fun l _ => h3 _ (b l).2) P.2
    have hIH : ∀ l, ∑ k ∈ s, (c k * r k l) • Fk k = 0 := by
      intro l
      refine sum_liftP_eq_zero hL M ρ t he hC p hg.init s (fun k => c k * r k l) (fun k => (φ k).1) (fun k => (d k).1)
        (fun k hk => (hv k hk).1) (fun x hx => ?_) P.1 F hF
      have hV : ∑ k ∈ s, (c k * famProd p (φ k).1 x) • v k = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        funext y
        rw [Finset.sum_apply]
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Submodule.coe_zero, Pi.zero_apply]
        rw [Finset.sum_congr rfl fun k hk => by rw [hv' k hk]]
        by_cases hy : IsHalf e y
        · have := hsum (x, y) ⟨hx, hy⟩
          rw [← this]
          refine Finset.sum_congr rfl fun k _ => ?_
          show _ = c k * (famProd p (φ k).1 x * (φ k).2 y)
          ring
        · refine Finset.sum_eq_zero fun k hk => ?_
          have : (φ k).2 y = 0 := by
            by_contra h0
            exact hy ((hmem k hk).1 y h0)
          rw [this, mul_zero]
      have := congrArg (fun z => b.repr z l) hV
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
        map_zero, Finsupp.coe_zero, Pi.zero_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [r]
      ring
    have hsum_lift :
        (∑ k ∈ s, c k • liftA W M a (W.fock a.pair (d k).2 P.2) (Fk k)) =
          ∑ k ∈ s, ∑ l ∈ Ls, (c k * r k l) • liftA W M a (g l) (Fk k) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hstep k hk, liftA_sum_datum M ha Ls (r k) g (Fk k) (fun l _ => hconv l k hk),
        Finset.smul_sum]
      simp only [smul_smul]
    show ∑ k ∈ s, c k • liftA W M a (W.fock a.pair (d k).2 P.2) (Fk k) = 0
    rw [hsum_lift, Finset.sum_comm]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← liftA_sum_form M a (g l) s (fun k => c k * r k l) Fk (fun k hk => hconv l k hk),
      hIH l, liftA_zero_form]

theorem liftT_tensE_expand (M : Vol G) {X Y : Node} (p : Path T X Y) (Q : PolE G →₀ ℂ) (τ : TotT G p) (F : Fn G X) :
    liftT W M p (tensE W p Q τ) F =
      ∑ P ∈ (Q.mapDomain fun P => restrictPol P p).support, (Q.mapDomain fun P => restrictPol P p) P •
        ∑ d ∈ τ.support, τ d • liftP W M p (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P) F := by
  unfold tensE tensT
  rw [Finsupp.sum, liftT_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Finsupp.sum, liftT_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [liftT_single, mul_smul]

theorem liftT_tensE_eq_of_famProd : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ {W : G.Weil} (M : Vol G) (ρ : RealMatch W) (t : T) {e : AE D}, IsIdemSum e (locPl G t) → GlobalTheory.FlipRun.CuspStep W M ρ t → ∀ {X Y : Node} (p : Path T X Y), GlobalTheory.FlipRun.OnGrid D.R.m t p → ∀ (τ₁ τ₂ : TotT G p) (φ₁ φ₂ : PureT G p → PureT G p), (∀ d ∈ τ₁.support, GlobalTheory.FlipRun.VecAll ρ e p (φ₁ d) d) → (∀ d ∈ τ₂.support, GlobalTheory.FlipRun.VecAll ρ e p (φ₂ d) d) → (∀ x : GlobalTheory.FlipRun.ArgT G p, GlobalTheory.FlipRun.HalfAll e p x → (τ₁.sum fun d c => c * GlobalTheory.FlipRun.famProd p (φ₁ d) x) = τ₂.sum fun d c => c * GlobalTheory.FlipRun.famProd p (φ₂ d) x) → ∀ F : Fn G X, GlobalTheory.FlipRun.IsCuspListed W.θ X F → ∀ Q : GlobalTheory.FlipRun.PolE G →₀ ℂ, liftT W M p (GlobalTheory.FlipRun.tensE W p Q τ₁) F = liftT W M p (GlobalTheory.FlipRun.tensE W p Q τ₂) F := by
  intro D T L sc G μ₀ hL W M ρ t e he hC X Y p hg τ₁ τ₂ φ₁ φ₂ hv₁ hv₂ heq F hF Q
  classical
  rw [liftT_tensE_expand, liftT_tensE_expand]
  refine Finset.sum_congr rfl fun P _ => ?_
  congr 1
  have key := sum_liftP_eq_zero hL M ρ t he hC p hg (τ₁.support.disjSum τ₂.support)
    (Sum.elim (fun d => τ₁ d) fun d => -τ₂ d) (Sum.elim φ₁ φ₂) (Sum.elim id id)
    (by
      rintro (k | k) hk
      · exact hv₁ k (Finset.inl_mem_disjSum.1 hk)
      · exact hv₂ k (Finset.inr_mem_disjSum.1 hk))
    (fun x hx => by
      rw [Finset.sum_disjSum]
      have := heq x hx
      simp only [Finsupp.sum] at this
      simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, this, add_neg_cancel])
    P F hF
  rw [Finset.sum_disjSum] at key
  simp only [Sum.elim_inl, Sum.elim_inr, id, neg_smul, Finset.sum_neg_distrib] at key
  exact sub_eq_zero.1 ((sub_eq_add_neg _ _).trans key)

end GlobalTheory.FlipRun

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TotalTensorThetaLiftEqOfSchwartzEqStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totalTensorThetaLift_eq_of_schwartz_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ {W : G.Weil} (M : Vol G) (ρ : RealMatch W) (t : T) {e : AE D}, IsIdemSum e (locPl G t) → GlobalTheory.FlipRun.CuspStep W M ρ t → ∀ {X Y : Node} (p : Path T X Y), GlobalTheory.FlipRun.OnGrid D.R.m t p → ∀ (τ₁ τ₂ : TotT G p) (φ₁ φ₂ : PureT G p → PureT G p), (∀ d ∈ τ₁.support, GlobalTheory.FlipRun.VecAll ρ e p (φ₁ d) d) → (∀ d ∈ τ₂.support, GlobalTheory.FlipRun.VecAll ρ e p (φ₂ d) d) → (∀ x : GlobalTheory.FlipRun.ArgT G p, GlobalTheory.FlipRun.HalfAll e p x → (τ₁.sum fun d c => c * GlobalTheory.FlipRun.famProd p (φ₁ d) x) = τ₂.sum fun d c => c * GlobalTheory.FlipRun.famProd p (φ₂ d) x) → ∀ F : Fn G X, GlobalTheory.FlipRun.IsCuspListed W.θ X F → ∀ Q : GlobalTheory.FlipRun.PolE G →₀ ℂ, liftT W M p (GlobalTheory.FlipRun.tensE W p Q τ₁) F = liftT W M p (GlobalTheory.FlipRun.tensE W p Q τ₂) F := by
  first | exact @GlobalTheory.FlipRun.liftT_tensE_eq_of_famProd | exact GlobalTheory.FlipRun.liftT_tensE_eq_of_famProd | (intros; apply GlobalTheory.FlipRun.liftT_tensE_eq_of_famProd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClassSumSchwartzProductsGridPath
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClassSumSchwartzProductsGridPath
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FlipRun

open GlobalTheory.FunObj.LocTensor
open scoped ValuativeRel

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem locArg_eq_locM (B : Frames G) {t : T} {a : Arrow T} (ha : IsGridArrow D.R.m t a) :
    ∃ (β : GL (Fin (G.pT a.pair).rank) (Lev.EAf D)) (β' : GL (Fin (G.pS a.pair).rank) (Lev.EAf D)), ∀ w,
      ∃ (f : Fin ((locGrid G t w).rank (edgeOf a).tgt) → Fin (G.pS a.pair).rank)
        (g : Fin ((locGrid G t w).rank (edgeOf a).src) → Fin (G.pT a.pair).rank),
        f.Surjective ∧ g.Surjective ∧ ∀ x r c, locArg B t w a x r c = locM β β' w x (g c) (f r) := by
  have sur : ∀ {m n : ℕ} (h : m = n), (Fin.cast h).Surjective := fun h y => ⟨Fin.cast h.symm y, by simp⟩
  rcases ha with ⟨i, j, hi, hj, rfl⟩ | ⟨i, j, hi, hj, rfl⟩
  · refine ⟨B.β i j, B.β (i + 1) j, fun w => ⟨Fin.cast (rank_vertex G t w (X := (i + 1, j)) ⟨hi, hj⟩),
      Fin.cast (rank_vertex G t w (X := (i, j)) ⟨hi.le, hj⟩), sur _, sur _, fun x r c => ?_⟩⟩
    have e : locArg B t w (.right i j) x = B.coord t w (X := (i, j)) (Y := (i + 1, j)) ⟨hi.le, hj⟩ ⟨hi, hj⟩
        (x.map fun c => cpt w (toEAf D c)) := dite_eq_left ⟨hi, hj⟩
    rw [e]
    rfl
  · refine ⟨B.β i (j + 1), B.β i j, fun w => ⟨Fin.cast (rank_vertex G t w (X := (i, j)) ⟨hi, hj.le⟩),
      Fin.cast (rank_vertex G t w (X := (i, j + 1)) ⟨hi, hj⟩), sur _, sur _, fun x r c => ?_⟩⟩
    have e : locArg B t w (.down t i j) x = B.coord t w (X := (i, j + 1)) (Y := (i, j)) ⟨hi, hj⟩ ⟨hi, hj.le⟩
        (x.map fun c => cpt w (toEAf D c)) := dite_eq_left ⟨hi, hj⟩
    rw [e]
    rfl

theorem locArg_add (B : Frames G) {t : T} {a : Arrow T} (ha : IsGridArrow D.R.m t a) (w : Pl D.host.E)
    (x u : WO (G.pS a.pair) (G.pT a.pair)) : locArg B t w a (x + u) = locArg B t w a x + locArg B t w a u := by
  obtain ⟨β, β', h⟩ := locArg_eq_locM B ha
  obtain ⟨f, g, -, -, h⟩ := h w
  ext r c
  rw [Matrix.add_apply, h, h, h, locM_add, Matrix.add_apply]

theorem arrow_sb {W : G.Weil} (B : Frames G) (ρ : RealMatch W) {μ₀ : T} (hL : L.Is μ₀) {t : T} {e : AE D}
    (he : IsIdemSum e (locPl G t)) (n : Pl D.host.E → ℕ) {a : Arrow T} (ha : IsGridArrow D.R.m t a) {Y : Type}
    (F : WO (G.pS a.pair) (G.pT a.pair) → Y → ℂ)
    (h1 : ∀ x u y, (∀ w ∈ locPl G t, GivenAdm.CongM (unifAt w ^ n w) (locArg B t w a u)) → F (x + u) y = F x y)
    (h2 : ∀ x y, F x y ≠ 0 → ∀ w ∈ locPl G t, ∀ r c, locArg B t w a x r c ∈ 𝒪[Kw w]) :
    ∃ (ι : Type) (s : Finset ι) (φ : ι → Sch G a) (r : ι → WO (G.pS a.pair) (G.pT a.pair)),
      (∀ i ∈ s, IsSBHalf e (latA G a) (φ i)) ∧ ∀ x y, IsHalf e x → F x y = ∑ i ∈ s, φ i x * F (r i) y := by
  obtain ⟨hS, hT, -⟩ := arrow_data ρ hL ha
  obtain ⟨β, β', hβ⟩ := locArg_eq_locM B ha
  obtain ⟨k, hk, k1, k2⟩ := exists_mult
    (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hS)
    (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hT) he β β' n
  exact exists_sb hS.1.fg hT.1.fg (GlobalTheory.PlaceVec.idemSum_mul_self he) F hk
    (fun u hu x y => h1 x (k • u) y fun w hw r c => by
      obtain ⟨f, g, -, -, h⟩ := hβ w
      rw [h]
      exact k1 u hu w hw _ _)
    fun x y hx h0 => k2 x hx fun w hw i j => by
      obtain ⟨f, g, hf, hg, h⟩ := hβ w
      obtain ⟨c, rfl⟩ := hg i
      obtain ⟨r, rfl⟩ := hf j
      rw [← h]
      exact h2 x y h0 w hw r c

theorem exists_classSum_schwartzProducts_pathInduction {μ₀ : T} (hL : L.Is μ₀) {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) {e : AE D}
    (he : IsIdemSum e (locPl G t)) (n : Pl D.host.E → ℕ) {X : Node} : ∀ {Y : Node} (p : Path T X Y), OnGrid D.R.m t p →
    (edges p).Nodup → ∀ {U : Type} (K : (∀ w, (locGrid G t w).Args) → U → ℂ),
    (∀ (x z : ∀ w, (locGrid G t w).Args) (y : U), (∀ w ∈ locPl G t, ∀ b,
      z w b ∈ GlobalTheory.SplitFlip.matLat _ (unifAt w ^ n w • GlobalTheory.SplitFlip.stdLat (Kw w) _)) → K (x + z) y = K x y) →
    (∀ (x : ∀ w, (locGrid G t w).Args) (y : U), K x y ≠ 0 → ∀ w ∈ locPl G t, ∀ b ∈ edges p,
      x w b ∈ GlobalTheory.SplitFlip.matLat _ (GlobalTheory.SplitFlip.stdLat (Kw w) _)) →
    ∃ (ι : Type) (s : Finset ι) (φ d : ι → PureT G p) (r : ι → ArgT G p), (∀ κ ∈ s, VecAll ρ e p (φ κ) (d κ)) ∧
      ∀ (x : ArgT G p) (y : U), HalfAll e p x →
        K (fun w => pathArgs B t w p x) y = ∑ κ ∈ s, famProd p (φ κ) x * K (fun w => pathArgs B t w p (r κ)) y := by
  intro Y p
  induction p with
  | nil =>
    intro _ _ U K _ _
    refine ⟨Unit, {()}, fun _ => (), fun _ => (), fun _ => (), fun _ _ => trivial, fun x y _ => ?_⟩
    rw [Finset.sum_singleton]
    exact (one_mul _).symm
  | snoc a p ih =>
    intro hg hnd U K hK1 hK2
    have hnd' : (edges p ++ [edgeOf a]).Nodup :=
      edges_snoc a p ▸ (hnd : (edges (.snoc a p)).Nodup)
    have hnd1 : (edges p).Nodup := hnd'.of_append_left
    have hne : edgeOf a ∉ edges p :=
      List.disjoint_right.mp hnd'.disjoint (List.mem_singleton_self _)
    have ha : IsGridArrow D.R.m t a := hg.last
    let F (x : WO (G.pS a.pair) (G.pT a.pair)) (z : ArgT G p × U) : ℂ :=
      K (fun w => Function.update (pathArgs B t w p z.1) (edgeOf a) (locArg B t w a x)) z.2
    have hF1 : ∀ x u z, (∀ w ∈ locPl G t, GivenAdm.CongM (unifAt w ^ n w) (locArg B t w a u)) →
        F (x + u) z = F x z := by
      intro x u z hu
      have e1 : (fun w => Function.update (pathArgs B t w p z.1) (edgeOf a) (locArg B t w a (x + u))) =
          (fun w => Function.update (pathArgs B t w p z.1) (edgeOf a) (locArg B t w a x)) +
            fun w => Function.update (0 : (locGrid G t w).Args) (edgeOf a) (locArg B t w a u) := by
        funext w b
        rcases eq_or_ne b (edgeOf a) with rfl | hb
        · simp only [Pi.add_apply, Function.update_self, locArg_add B ha]
        · simp only [Pi.add_apply, Function.update_of_ne hb, Pi.zero_apply, add_zero]
      dsimp only [F]
      rw [e1]
      refine hK1 _ _ _ fun w hw b => ?_
      rcases eq_or_ne b (edgeOf a) with rfl | hb
      · rw [Function.update_self]
        exact GivenAdm.mem_matLat_smul.2 (hu w hw)
      · rw [Function.update_of_ne hb]
        exact zero_mem _
    have hF2 : ∀ x z, F x z ≠ 0 → ∀ w ∈ locPl G t, ∀ r c, locArg B t w a x r c ∈ 𝒪[Kw w] := by
      intro x z h0 w hw r c
      have hm : edgeOf a ∈ edges (.snoc a p) := by
        rw [edges_snoc]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      have h := hK2 (fun w => Function.update (pathArgs B t w p z.1) (edgeOf a) (locArg B t w a x))
        z.2 h0 w hw (edgeOf a) hm
      rw [Function.update_self] at h
      exact GlobalTheory.SplitFlip.mem_matLat_stdLat.1 h r c
    have hArrowExpansion :
        ∃ (ι : Type) (s : Finset ι) (φ : ι → Sch G a) (r : ι → WO (G.pS a.pair) (G.pT a.pair)),
          (∀ i ∈ s, IsSBHalf e (latA G a) (φ i)) ∧
            ∀ x y, IsHalf e x → F x y = ∑ i ∈ s, φ i x * F (r i) y := by
      exact arrow_sb (W := W) B ρ (μ₀ := μ₀) hL (t := t) (e := e) he n (a := a) ha
        (Y := ArgT G p × U) F hF1 hF2
    obtain ⟨ι₁, s₁, φa, r₁, hφa, hexp⟩ := hArrowExpansion
    let K' (x : ∀ w, (locGrid G t w).Args) (y : ι₁ × U) : ℂ :=
      K (fun w => Function.update (x w) (edgeOf a) (locArg B t w a (r₁ y.1))) y.2
    have hK'1 : ∀ x z y, (∀ w ∈ locPl G t, ∀ b,
        z w b ∈ GlobalTheory.SplitFlip.matLat _ (unifAt w ^ n w • GlobalTheory.SplitFlip.stdLat (Kw w) _)) →
        K' (x + z) y = K' x y := by
      intro x z y hz
      have e1 : (fun w => Function.update ((x + z) w) (edgeOf a) (locArg B t w a (r₁ y.1))) =
          (fun w => Function.update (x w) (edgeOf a) (locArg B t w a (r₁ y.1))) +
            fun w => Function.update (z w) (edgeOf a) 0 := by
        funext w b
        rcases eq_or_ne b (edgeOf a) with rfl | hb
        · simp only [Pi.add_apply, Function.update_self, add_zero]
        · simp only [Pi.add_apply, Function.update_of_ne hb]
      dsimp only [K']
      rw [e1]
      refine hK1 _ _ _ fun w hw b => ?_
      rcases eq_or_ne b (edgeOf a) with rfl | hb
      · rw [Function.update_self]
        exact zero_mem _
      · rw [Function.update_of_ne hb]
        exact hz w hw b
    have hK'2 : ∀ x y, K' x y ≠ 0 → ∀ w ∈ locPl G t, ∀ b ∈ edges p,
        x w b ∈ GlobalTheory.SplitFlip.matLat _ (GlobalTheory.SplitFlip.stdLat (Kw w) _) := by
      intro x y h0 w hw b hb
      have hm : b ∈ edges (.snoc a p) := by
        rw [edges_snoc]
        exact List.mem_append_left _ hb
      have h := hK2 (fun w => Function.update (x w) (edgeOf a) (locArg B t w a (r₁ y.1))) y.2 h0 w hw b hm
      have hba : b ≠ edgeOf a := fun hEq => hne (hEq ▸ hb)
      rwa [Function.update_of_ne hba] at h
    obtain ⟨ι₂, s₂, φ₂, d₂, r₂, hv, hexp₂⟩ := ih hg.init hnd1 (U := ι₁ × U) K' hK'1 hK'2
    obtain ⟨Tm, hTm, -, -⟩ := exists_arrowModel ρ hL he ha
    refine ⟨ι₂ × ι₁, s₂ ×ˢ s₁, fun κ => (φ₂ κ.1, φa κ.2), fun κ => (d₂ κ.1, Tm (φa κ.2)), fun κ => (r₂ κ.1, r₁ κ.2),
      fun κ hκ => ?_, fun x y hx => ?_⟩
    · obtain ⟨h1, h2⟩ := Finset.mem_product.1 hκ
      exact ⟨hv _ h1, (hTm _ _).2 ⟨hφa _ h2, rfl⟩⟩
    · have hx' : HalfAll e p x.1 ∧ IsHalf e x.2 := hx
      have e1 : (fun w => pathArgs B t w (.snoc a p) x) =
          fun w => Function.update (pathArgs B t w p x.1) (edgeOf a) (locArg B t w a x.2) :=
        funext fun w => pathArgs_snoc B t w a p x
      calc K (fun w => pathArgs B t w (.snoc a p) x) y
          = ∑ i ∈ s₁, φa i x.2 * K (fun w => Function.update (pathArgs B t w p x.1) (edgeOf a) (locArg B t w a (r₁ i))) y := by
            rw [e1]
            exact hexp x.2 (x.1, y) hx'.2
        _ = ∑ i ∈ s₁, φa i x.2 * ∑ κ ∈ s₂, famProd p (φ₂ κ) x.1 *
              K (fun w => Function.update (pathArgs B t w p (r₂ κ)) (edgeOf a) (locArg B t w a (r₁ i))) y :=
            Finset.sum_congr rfl fun i _ => congrArg _ (hexp₂ x.1 (i, y) hx'.1)
        _ = _ := by
            rw [Finset.sum_product_right]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun κ _ => ?_
            have e2 : (fun w => pathArgs B t w (.snoc a p) ((r₂ κ, r₁ i) : ArgT G (.snoc a p))) =
                fun w => Function.update (pathArgs B t w p (r₂ κ)) (edgeOf a) (locArg B t w a (r₁ i)) :=
              funext fun w => pathArgs_snoc B t w a p _
            show _ = famProd p (φ₂ κ) x.1 * φa i x.2 * K (fun w => pathArgs B t w (.snoc a p) ((r₂ κ, r₁ i) : ArgT G (.snoc a p))) y
            rw [e2]
            ring

theorem exists_classes_path : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) {e : AE D}, IsIdemSum e (locPl G t) → ∀ (n : Pl D.host.E → ℕ) {X Y : Node} (p : Path T X Y), GlobalTheory.FlipRun.OnGrid D.R.m t p → (GlobalTheory.FlipRun.edges p).Nodup → ∀ {U : Type} (K : (∀ w, (locGrid G t w).Args) → U → ℂ), (∀ (x z : ∀ w, (locGrid G t w).Args) (y : U), (∀ w ∈ locPl G t, ∀ b, z w b ∈ GlobalTheory.SplitFlip.matLat _ (unifAt w ^ n w • GlobalTheory.SplitFlip.stdLat (Kw w) _)) → K (x + z) y = K x y) → (∀ (x : ∀ w, (locGrid G t w).Args) (y : U), K x y ≠ 0 → ∀ w ∈ locPl G t, ∀ b ∈ GlobalTheory.FlipRun.edges p, x w b ∈ GlobalTheory.SplitFlip.matLat _ (GlobalTheory.SplitFlip.stdLat (Kw w) _)) → ∃ (ι : Type) (s : Finset ι) (φ d : ι → PureT G p) (r : ι → GlobalTheory.FlipRun.ArgT G p), (∀ κ ∈ s, GlobalTheory.FlipRun.VecAll ρ e p (φ κ) (d κ)) ∧ ∀ (x : GlobalTheory.FlipRun.ArgT G p) (y : U), GlobalTheory.FlipRun.HalfAll e p x → K (fun w => GlobalTheory.FlipRun.pathArgs B t w p x) y = ∑ κ ∈ s, GlobalTheory.FlipRun.famProd p (φ κ) x * K (fun w => GlobalTheory.FlipRun.pathArgs B t w p (r κ)) y :=
  by
  intro D T L sc G μ₀ hL W B ρ t e he n X Y p hg hnd U K hK1 hK2
  exact exists_classSum_schwartzProducts_pathInduction hL B ρ t he n p hg hnd K hK1 hK2

end GlobalTheory.FlipRun

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClassSumSchwartzProductsGridPathStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_classSum_schwartzProducts_gridPath : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) {e : AE D}, IsIdemSum e (locPl G t) → ∀ (n : Pl D.host.E → ℕ) {X Y : Node} (p : Path T X Y), GlobalTheory.FlipRun.OnGrid D.R.m t p → (GlobalTheory.FlipRun.edges p).Nodup → ∀ {U : Type} (K : (∀ w, (locGrid G t w).Args) → U → ℂ), (∀ (x z : ∀ w, (locGrid G t w).Args) (y : U), (∀ w ∈ locPl G t, ∀ b, z w b ∈ GlobalTheory.SplitFlip.matLat _ (unifAt w ^ n w • GlobalTheory.SplitFlip.stdLat (Kw w) _)) → K (x + z) y = K x y) → (∀ (x : ∀ w, (locGrid G t w).Args) (y : U), K x y ≠ 0 → ∀ w ∈ locPl G t, ∀ b ∈ GlobalTheory.FlipRun.edges p, x w b ∈ GlobalTheory.SplitFlip.matLat _ (GlobalTheory.SplitFlip.stdLat (Kw w) _)) → ∃ (ι : Type) (s : Finset ι) (φ d : ι → PureT G p) (r : ι → GlobalTheory.FlipRun.ArgT G p), (∀ κ ∈ s, GlobalTheory.FlipRun.VecAll ρ e p (φ κ) (d κ)) ∧ ∀ (x : GlobalTheory.FlipRun.ArgT G p) (y : U), GlobalTheory.FlipRun.HalfAll e p x → K (fun w => GlobalTheory.FlipRun.pathArgs B t w p x) y = ∑ κ ∈ s, GlobalTheory.FlipRun.famProd p (φ κ) x * K (fun w => GlobalTheory.FlipRun.pathArgs B t w p (r κ)) y := by
  first | exact @GlobalTheory.FlipRun.exists_classes_path | exact GlobalTheory.FlipRun.exists_classes_path | (intros; apply GlobalTheory.FlipRun.exists_classes_path <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridSquareFlipSmallRouteEqInvSmulBigRoute
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FlipRun

section Local

open GlobalTheory.SplitFlip Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {Γ : Grid k}


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem update_two_add (x z : Γ.Args) (b₁ b₂ : Edge) (u u' : Matrix (Fin (Γ.rank b₁.tgt)) (Fin (Γ.rank b₁.src)) k)
    (v v' : Matrix (Fin (Γ.rank b₂.tgt)) (Fin (Γ.rank b₂.src)) k) :
    (Function.update (Function.update (x + z) b₁ (u + u')) b₂ (v + v') : Γ.Args) =
      Function.update (Function.update x b₁ u) b₂ v + Function.update (Function.update z b₁ u') b₂ v' := by
  funext b
  by_cases hb : b = b₂
  · subst hb; simp
  · by_cases hb' : b = b₁
    · subst hb'; simp [Function.update_of_ne hb]
    · simp [Function.update_of_ne hb, Function.update_of_ne hb']

theorem mem_update_two {c : kˣ} {z : Γ.Args} (hz : ∀ b, z b ∈ matLat _ (c • stdLat k _)) {b₁ b₂ : Edge}
    {u : Matrix (Fin (Γ.rank b₁.tgt)) (Fin (Γ.rank b₁.src)) k} {v : Matrix (Fin (Γ.rank b₂.tgt)) (Fin (Γ.rank b₂.src)) k}
    (hu : u ∈ matLat _ (c • stdLat k _)) (hv : v ∈ matLat _ (c • stdLat k _)) (b : Edge) :
    (Function.update (Function.update z b₁ u) b₂ v : Γ.Args) b ∈ matLat _ (c • stdLat k _) := by
  by_cases hb : b = b₂
  · subst hb; rwa [Function.update_self]
  · by_cases hb' : b = b₁
    · subst hb'; rwa [Function.update_of_ne hb, Function.update_self]
    · rw [Function.update_of_ne hb, Function.update_of_ne hb']; exact hz b

def setA (i j : ℕ) (x : Γ.Args) (Z : Matrix (Fin (Γ.rank (i + 1, j + 1))) (Γ.Cols i j) k) : Γ.Args :=
  Function.update (Function.update x (.ex i (j + 1)) Z.toCols₁) (.theta (i + 1) j) Z.toCols₂ᵀ


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem joinA_setA (i j : ℕ) (x : Γ.Args) (Z : Matrix (Fin (Γ.rank (i + 1, j + 1))) (Γ.Cols i j) k) :
    Γ.joinA i j (setA i j x Z) = Z := by
  rw [Grid.joinA, setA, Function.update_self, Function.update_of_ne (by simp), Function.update_self, transpose_transpose,
    fromCols_toCols]

variable {ϖ : kˣ} {e : ℕ} {γ : List Edge} {S : Γ.Args → ℂ}

theorem isNatDatum_two (hS : Γ.IsTensor ϖ e γ S) {b₁ b₂ : Edge} (h1 : b₁ ∈ γ) (h2 : b₂ ∈ γ) (hne : b₁ ≠ b₂) (x : Γ.Args)
    {A B : Type} (f₁ : Matrix A B k →+ Matrix (Fin (Γ.rank b₁.tgt)) (Fin (Γ.rank b₁.src)) k)
    (f₂ : Matrix A B k →+ Matrix (Fin (Γ.rank b₂.tgt)) (Fin (Γ.rank b₂.src)) k)
    (hf : ∀ (c : kˣ) Z, Z ∈ matLat A (c • stdLat k B) ↔ f₁ Z ∈ matLat _ (c • stdLat k _) ∧ f₂ Z ∈ matLat _ (c • stdLat k _)) :
    IsNatDatum ϖ e fun Z => S (Function.update (Function.update x b₁ (f₁ Z)) b₂ (f₂ Z)) := by
  refine ⟨fun Z hZ => ?_, fun Z Z₀ hZ₀ => ?_⟩
  · have h := hf 1 Z
    simp only [one_smul] at h
    rcases not_and_or.1 (mt h.2 hZ) with h' | h'
    · exact hS.2.1 _ _ h1 (by rwa [Function.update_of_ne hne, Function.update_self])
    · exact hS.2.1 _ _ h2 (by rwa [Function.update_self])
  · beta_reduce
    rw [map_add (f := _), map_add (f := _), ← hS.2.2 (Function.update (Function.update x b₁ (f₁ Z)) b₂ (f₂ Z)) _
      (mem_update_two (z := 0) (fun _ => zero_mem _) ((hf _ _).1 hZ₀).1 ((hf _ _).1 hZ₀).2), ← update_two_add, add_zero]

theorem mem_matLat_cols {A B₁ B₂ : Type} (c : kˣ) (Z : Matrix A (B₁ ⊕ B₂) k) :
    Z ∈ matLat A (c • stdLat k _) ↔ Z.toCols₁ ∈ matLat _ (c • stdLat k _) ∧ Z.toCols₂ᵀ ∈ matLat _ (c • stdLat k _) := by
  simp only [mem_matLat, SplitFlip.stdLat, smul_diagLat, mem_diagLat, Matrix.row, Sum.forall, toCols₁, toCols₂, of_apply, transpose_apply,
    Pi.one_apply, forall_and]
  exact and_congr_right fun _ => forall_comm


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
def colsL (A B₁ B₂ : Type) : Matrix A (B₁ ⊕ B₂) k →+ Matrix A B₁ k := ⟨⟨toCols₁, rfl⟩, fun _ _ => rfl⟩


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
def colsR (A B₁ B₂ : Type) : Matrix A (B₁ ⊕ B₂) k →+ Matrix B₂ A k := ⟨⟨fun Z => Z.toCols₂ᵀ, rfl⟩, fun _ _ => rfl⟩

theorem isNatDatum_small (hS : Γ.IsTensor ϖ e γ S) {i j : ℕ} (h1 : Edge.theta i j ∈ γ) (h2 : Edge.ex i j ∈ γ) (x : Γ.Args) :
    IsNatDatum ϖ e (Γ.sliceB i j S x) :=
  isNatDatum_two hS h1 h2 (by simp) x (colsL _ _ _) (colsR _ _ _) mem_matLat_cols

theorem isNatDatum_big (hS : Γ.IsTensor ϖ e γ S) {i j : ℕ} (h1 : Edge.ex i (j + 1) ∈ γ) (h2 : Edge.theta (i + 1) j ∈ γ)
    (x : Γ.Args) : IsNatDatum ϖ e fun Z => S (setA i j x Z) :=
  isNatDatum_two hS h1 h2 (by simp) x (colsL _ _ _) (colsR _ _ _) mem_matLat_cols

theorem sliceB_add (hS : Γ.IsTensor ϖ e γ S) (i j : ℕ) (x z : Γ.Args) (hz : ∀ b, z b ∈ matLat _ (ϖ ^ e • stdLat k _)) :
    Γ.sliceB i j S (x + z) = Γ.sliceB i j S x := by
  funext Z
  rw [Grid.sliceB, Grid.sliceB, ← hS.2.2 (Function.update (Function.update x _ _) _ _) _
    (mem_update_two (b₁ := .theta i j) (b₂ := .ex i j) hz (zero_mem _) (zero_mem _)), ← update_two_add, add_zero, add_zero]

theorem sliceB_setA (hS : Γ.IsTensor ϖ e γ S) {i j : ℕ} (h1 : Edge.ex i (j + 1) ∉ γ) (h2 : Edge.theta (i + 1) j ∉ γ)
    (x : Γ.Args) (Y : Matrix (Fin (Γ.rank (i + 1, j + 1))) (Γ.Cols i j) k) :
    Γ.sliceB i j S (setA i j x Y) = Γ.sliceB i j S x := by
  funext Z
  refine hS.1 fun b hb => ?_
  have a1 : b ≠ .ex i (j + 1) := fun h => h1 (h ▸ hb)
  have a2 : b ≠ .theta (i + 1) j := fun h => h2 (h ▸ hb)
  by_cases hb : b = .ex i j
  · subst hb; rw [Function.update_self, Function.update_self]
  · by_cases hb' : b = .theta i j
    · subst hb'; rw [Function.update_of_ne hb, Function.update_of_ne hb, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hb, Function.update_of_ne hb, Function.update_of_ne hb', Function.update_of_ne hb', setA,
        Function.update_of_ne a2, Function.update_of_ne a1]

theorem mem_of_update_two (hS : Γ.IsTensor ϖ e γ S) {b₁ b₂ : Edge} {x : Γ.Args} {u v}
    (h : S (Function.update (Function.update x b₁ u) b₂ v) ≠ 0) {b : Edge} (hb : b ∈ γ) (h1 : b ≠ b₁) (h2 : b ≠ b₂) :
    x b ∈ matLat _ (stdLat k _) := by
  by_contra h'
  exact h (hS.2.1 _ b hb (by rwa [Function.update_of_ne h2, Function.update_of_ne h1]))


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem add_update_two {x y : Γ.Args} {b₁ b₂ : Edge} (h1 : x b₁ = 0) (h2 : x b₂ = 0) (h1' : y b₁ = 0) (h2' : y b₂ = 0) (u v) :
    x + Function.update (Function.update (0 : Γ.Args) b₁ u) b₂ v + y = Function.update (Function.update (x + y) b₁ u) b₂ v := by
  funext b
  by_cases hb : b = b₂
  · subst hb; simp [h2, h2']
  · by_cases hb' : b = b₁
    · subst hb'; simp [Function.update_of_ne hb, h1, h1']
    · simp [Function.update_of_ne hb, Function.update_of_ne hb']

end Local

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem exists_rep_sandwich {W : G.Weil} (ρ : RealMatch W) {μ₀ : T} (hL : L.Is μ₀) {t : T} {e : AE D}
    (he : IsIdemSum e (locPl G t)) {X Y Z U : Node} {A : Path T X Y} {r : Path T Y Z} {B' : Path T Z U}
    (hg : OnGrid D.R.m t ((A.comp r).comp B')) {ι : Type} (s : Finset ι) (α φA : ι → PureT G A) (β φB : ι → PureT G B')
    (σ : ι → TotT G r) (ψ : ι → PureT G r → PureT G r) (hA : ∀ κ ∈ s, VecAll ρ e A (φA κ) (α κ))
    (hB : ∀ κ ∈ s, VecAll ρ e B' (φB κ) (β κ)) (hσ : ∀ κ ∈ s, ∀ d ∈ (σ κ).support, VecAll ρ e r (ψ κ d) d)
    (H : ArgT G ((A.comp r).comp B') → ℂ)
    (hH : ∀ x y z, HalfAll e A x → HalfAll e r y → HalfAll e B' z → H ((x.append y).append z) =
      ∑ κ ∈ s, famProd A (φA κ) x * famProd B' (φB κ) z * (σ κ).sum fun d c => c * famProd r (ψ κ d) y) :
    ∃ φ : PureT G ((A.comp r).comp B') → PureT G ((A.comp r).comp B'),
      (∀ d ∈ (∑ κ ∈ s, sandwich (α κ) (σ κ) (β κ)).support, VecAll ρ e _ (φ d) d) ∧
      ∀ x, HalfAll e _ x → ((∑ κ ∈ s, sandwich (α κ) (σ κ) (β κ)).sum fun d c => c * famProd _ (φ d) x) = H x := by
  classical
  let rec vecAll_unique {W : G.Weil} (ρ : RealMatch W) {μ₀ : T} (hL : L.Is μ₀) {t : T} {e : AE D}
      (he : IsIdemSum e (locPl G t)) {X : Node} : ∀ {Y : Node} (p : Path T X Y), OnGrid D.R.m t p → ∀ (φ φ' d : PureT G p),
        VecAll ρ e p φ d → VecAll ρ e p φ' d → φ = φ'
    | _, .nil, _, _, _, _, _, _ => rfl
    | _, .snoc a p, hg, φ, φ', d, h, h' => by
      obtain ⟨Tm, h1, h2, -⟩ := exists_arrowModel ρ hL he hg.last
      obtain ⟨a1, a2⟩ := (h1 _ _).1 h.2
      obtain ⟨b1, b2⟩ := (h1 _ _).1 h'.2
      refine Prod.ext (vecAll_unique ρ hL he p hg.init φ.1 φ'.1 d.1 h.1 h'.1) (sub_eq_zero.1 (h2 _ ?_ ?_))
      · exact (LocTensor.sbSpace e (latA G a)).sub_mem a1 b1
      · rw [map_sub, ← a2, ← b2, sub_self]
  let rec exists_append {S : Arrow T → Type} {X Y : Node} (p : Path T X Y) :
      ∀ {Z : Node} (q : Path T Y Z) (z : (p.comp q).Fam S), ∃ (x : p.Fam S) (y : q.Fam S), z = x.append y
    | _, .nil, z => ⟨z, (), rfl⟩
    | _, .snoc a q, z => by
      obtain ⟨x, y, h⟩ := exists_append p q z.1
      exact ⟨x, (y, z.2), Prod.ext h rfl⟩
  have hv : ∀ κ ∈ s, ∀ d ∈ (σ κ).support, VecAll ρ e _ (((φA κ).append (ψ κ d)).append (φB κ)) (((α κ).append d).append (β κ)) :=
    fun κ hκ d hd => (vecAll_append ρ e _ _ _ _ _ _).2 ⟨(vecAll_append ρ e _ _ _ _ _ _).2 ⟨hA κ hκ, hσ κ hκ d hd⟩, hB κ hκ⟩
  let φ : PureT G ((A.comp r).comp B') → PureT G ((A.comp r).comp B') := fun d =>
    if h : ∃ φ, VecAll ρ e _ φ d then h.choose else d
  have hφ : ∀ d φ', VecAll ρ e _ φ' d → φ d = φ' := fun d φ' h => by
    have h' : ∃ φ, VecAll ρ e _ φ d := ⟨φ', h⟩
    simp only [φ, dif_pos h']
    exact vecAll_unique ρ hL he _ hg _ _ d h'.choose_spec h
  refine ⟨φ, fun d hd => ?_, fun x hx => ?_⟩
  · have hd0 : (∑ κ ∈ s, sandwich (α κ) (σ κ) (β κ)) d ≠ 0 := Finsupp.mem_support_iff.mp hd
    rw [Finset.sum_apply'] at hd0
    obtain ⟨κ, hκ, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd0
    have hd : d ∈ (sandwich (α κ) (σ κ) (β κ)).support := Finsupp.mem_support_iff.mpr hd
    unfold sandwich at hd
    obtain ⟨d', hd', hd⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hd)
    obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hd)
    rw [hφ _ _ (hv κ hκ d' hd')]
    exact hv κ hκ d' hd'
  · obtain ⟨x', z, rfl⟩ := exists_append _ _ x
    obtain ⟨x, y, rfl⟩ := exists_append _ _ x'
    rw [halfAll_append, halfAll_append] at hx
    rw [hH x y z hx.1.1 hx.1.2 hx.2]
    have e1 : ∀ τ : TotT G ((A.comp r).comp B'), (τ.sum fun d c => c * famProd _ (φ d) ((x.append y).append z)) =
      Finsupp.linearCombination ℂ (fun d => famProd _ (φ d) ((x.append y).append z)) τ := fun τ => rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum]
    refine Finset.sum_congr rfl fun κ hκ => ?_
    rw [sandwich, map_finsuppSum, Finsupp.mul_sum]
    refine Finsupp.sum_congr fun d hd => ?_
    rw [Finsupp.linearCombination_single, hφ _ _ (hv κ hκ d hd), famProd_append, famProd_append, smul_eq_mul]
    ring

theorem edges_routes (t : T) (i j : ℕ) : edges (routeSmall t i j) = [.theta i j, .ex i j] ∧
    edges (routeBig t i j) = [.ex i (j + 1), .theta (i + 1) j] := ⟨rfl, rfl⟩

theorem edges_outer {m : ℕ} {t : T} {i j : ℕ} {A : Path T (.grid 0 m) (.grid i (j + 1))} {Bp : Path T (.grid (i + 1) j) (.grid m 0)}
    (hA : OnGrid m t A) (hB : OnGrid m t Bp) : (edges A).Nodup ∧ (edges Bp).Nodup ∧ (∀ b ∈ edges Bp, b ∉ edges A) ∧
      ∀ b, b ∈ edges A ∨ b ∈ edges Bp → b ≠ .theta i j ∧ b ≠ .ex i j ∧ b ≠ .ex i (j + 1) ∧ b ≠ .theta (i + 1) j := by
  let rec edges_bound {m : ℕ} {t : T} {i j : ℕ} : ∀ {Y : Node} (p : Path T (.grid i j) Y), OnGrid m t p →
      ∃ i' j', Y = .grid i' j' ∧ i ≤ i' ∧ j' ≤ j ∧ (edges p).Nodup ∧
        ∀ b ∈ edges p, i ≤ b.src.1 ∧ b.tgt.1 ≤ i' ∧ j' ≤ b.tgt.2 ∧ b.src.2 ≤ j
    | _, .nil, _ => ⟨i, j, rfl, le_rfl, le_rfl, List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩
    | _, .snoc a p, hg => by
      obtain ⟨i', j', h1, h2, h3, h4, h5⟩ := edges_bound p hg.init
      rw [edges_snoc]
      rcases hg.last with ⟨k, l, -, -, rfl⟩ | ⟨k, l, -, -, rfl⟩
      · obtain ⟨rfl, rfl⟩ : k = i' ∧ l = j' := Node.grid.inj h1
        refine ⟨k + 1, l, rfl, by omega, h3, List.nodup_append.2 ⟨h4, List.nodup_singleton _, fun b hb c hc e => ?_⟩, fun b hb => ?_⟩
        · obtain rfl := List.mem_singleton.1 hc
          subst e
          have := (h5 _ hb).2.1
          simp [edgeOf] at this
        · rcases List.mem_append.1 hb with hb | hb
          · have := h5 b hb; omega
          · obtain rfl := List.mem_singleton.1 hb
            simp only [edgeOf]; omega
      · obtain ⟨rfl, rfl⟩ : k = i' ∧ l + 1 = j' := Node.grid.inj h1
        refine ⟨k, l, rfl, h2, by omega, List.nodup_append.2 ⟨h4, List.nodup_singleton _, fun b hb c hc e => ?_⟩, fun b hb => ?_⟩
        · obtain rfl := List.mem_singleton.1 hc
          subst e
          have := (h5 _ hb).2.2.1
          simp [edgeOf] at this
        · rcases List.mem_append.1 hb with hb | hb
          · have := h5 b hb; omega
          · obtain rfl := List.mem_singleton.1 hb
            simp only [edgeOf]; omega
  obtain ⟨_, _, h1, -, -, a1, a2⟩ := edges_bound A hA
  obtain ⟨rfl, rfl⟩ := Node.grid.inj h1
  obtain ⟨_, _, -, -, -, b1, b2⟩ := edges_bound Bp hB
  refine ⟨a1, b1, fun b hb hb' => ?_, fun b hb => ?_⟩
  · have := a2 b hb'
    have := b2 b hb
    cases b <;> simp only at * <;> omega
  · rcases hb with hb | hb
    · have := a2 b hb
      refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> simp only at this <;> omega
    · have := b2 b hb
      refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> simp only at this <;> omega

theorem exists_classes_two {μ₀ : T} (hL : L.Is μ₀) {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) {e : AE D}
    (he : IsIdemSum e (locPl G t)) (n : Pl D.host.E → ℕ) {X Y X' Y' : Node} (p : Path T X Y) (q : Path T X' Y')
    (hp : OnGrid D.R.m t p) (hq : OnGrid D.R.m t q) (np : (edges p).Nodup) (nq : (edges q).Nodup)
    (hpq : ∀ b ∈ edges q, b ∉ edges p) {U : Type} (K : (∀ w, (locGrid G t w).Args) → U → ℂ)
    (h1 : ∀ (x z : ∀ w, (locGrid G t w).Args) (y : U), (∀ w ∈ locPl G t, ∀ b,
      z w b ∈ SplitFlip.matLat _ (unifAt w ^ n w • SplitFlip.stdLat (Kw w) _)) → K (x + z) y = K x y)
    (h2 : ∀ (x : ∀ w, (locGrid G t w).Args) (y : U), K x y ≠ 0 → ∀ w ∈ locPl G t, ∀ b, b ∈ edges p ∨ b ∈ edges q →
      x w b ∈ SplitFlip.matLat _ (SplitFlip.stdLat (Kw w) _)) :
    ∃ (ι : Type) (s : Finset ι) (φ d : ι → PureT G p) (φ' d' : ι → PureT G q) (r : ι → ArgT G p) (r' : ι → ArgT G q),
      (∀ κ ∈ s, VecAll ρ e p (φ κ) (d κ)) ∧ (∀ κ ∈ s, VecAll ρ e q (φ' κ) (d' κ)) ∧
      ∀ x x' y, HalfAll e p x → HalfAll e q x' → K (fun w => pathArgs B t w p x + pathArgs B t w q x') y =
        ∑ κ ∈ s, famProd p (φ κ) x * famProd q (φ' κ) x' * K (fun w => pathArgs B t w p (r κ) + pathArgs B t w q (r' κ)) y := by
  obtain ⟨ι, s, φ, d, r, a1, a2⟩ := GlobalTheory.T.exists_classSum_schwartzProducts_gridPath hL B ρ t he n p hp np (U := ArgT G q × U)
    (fun x y => K (x + fun w => pathArgs B t w q y.1) y.2) (fun x z y hz => by rw [add_right_comm, h1 _ z _ hz])
    fun x y h w hw b hb => by
      have := h2 _ _ h w hw b (.inl hb)
      rwa [Pi.add_apply, Pi.add_apply, pathArgs_of_notMem B t w q _ b fun h' => hpq b h' hb, add_zero] at this
  obtain ⟨ι', s', φ', d', r', b1, b2⟩ := GlobalTheory.T.exists_classSum_schwartzProducts_gridPath hL B ρ t he n q hq nq (U := ι × U)
    (fun x y => K ((fun w => pathArgs B t w p (r y.1)) + x) y.2) (fun x z y hz => by rw [← add_assoc, h1 _ z _ hz])
    fun x y h w hw b hb => by
      have := h2 _ _ h w hw b (.inr hb)
      rwa [Pi.add_apply, Pi.add_apply, pathArgs_of_notMem B t w p _ b (hpq b hb), zero_add] at this
  refine ⟨ι × ι', s ×ˢ s', fun κ => φ κ.1, fun κ => d κ.1, fun κ => φ' κ.2, fun κ => d' κ.2, fun κ => r κ.1, fun κ => r' κ.2,
    fun κ hκ => a1 _ (Finset.mem_product.1 hκ).1, fun κ hκ => b1 _ (Finset.mem_product.1 hκ).2, fun x x' y hx hx' => ?_⟩
  refine (a2 x (x', y) hx).trans ?_
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun κ _ => ?_
  refine (congrArg _ (b2 x' (κ, y) hx')).trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => (mul_assoc _ _ _).symm

theorem exists_decomp : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : ℕ) (hi : i < D.R.m) (hj : j < D.R.m) (A : Path T (.grid 0 D.R.m) (.grid i (j + 1))) (Bp : Path T (.grid (i + 1) j) (.grid D.R.m 0)), GlobalTheory.FlipRun.OnGrid D.R.m t A → GlobalTheory.FlipRun.OnGrid D.R.m t Bp → ∀ (Tl : ∀ w, (locGrid G t w).Args → ℂ), (∀ w ∈ locPl G t, (locGrid G t w).IsTensor (unifAt w) (depthAt G w) (GlobalTheory.FlipRun.edges ((A.comp (routeSmall t i j)).comp Bp)) (Tl w)) → (∀ w ∈ locPl G t, (locGrid G t w).IsTensor (unifAt w) (depthAt G w) (GlobalTheory.FlipRun.edges ((A.comp (routeBig t i j)).comp Bp)) ((locGrid G t w).flipTensor .one (psiAt W w) (unifAt w) (depthAt G w) i j (givenLevel G t w) (Tl w))) → ∀ e : AE D, IsIdemSum e (locPl G t) → ∃ (ι : Type) (s : Finset ι) (α : ι → PureT G A) (β : ι → PureT G Bp) (σs : ι → TotT G (routeSmall t i j)) (σb : ι → TotT G (routeBig t i j)), (∀ κ ∈ s, ∃ Φ : ∀ w, Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) → ℂ, (∀ w ∈ locPl G t, GlobalTheory.SplitFlip.IsNatDatum (unifAt w) (depthAt G w) (Φ w)) ∧ HasFlip B t ρ ⟨i, hi⟩ ⟨j, hj⟩ (depthAt G) Φ (σb κ) (σs κ)) ∧ (∀ κ ∈ s, (∃ φA, GlobalTheory.FlipRun.VecAll ρ e A φA (α κ)) ∧ ∃ φB, GlobalTheory.FlipRun.VecAll ρ e Bp φB (β κ)) ∧ (∃ φ : PureT G ((A.comp (routeSmall t i j)).comp Bp) → PureT G ((A.comp (routeSmall t i j)).comp Bp), (∀ d ∈ (∑ κ ∈ s, ((σs κ).sum fun d c => Finsupp.single (((α κ).append d).append (β κ)) c)).support, GlobalTheory.FlipRun.VecAll ρ e ((A.comp (routeSmall t i j)).comp Bp) (φ d) d) ∧ ∀ x : GlobalTheory.FlipRun.ArgT G ((A.comp (routeSmall t i j)).comp Bp), GlobalTheory.FlipRun.HalfAll e ((A.comp (routeSmall t i j)).comp Bp) x → ((∑ κ ∈ s, ((σs κ).sum fun d c => Finsupp.single (((α κ).append d).append (β κ)) c)).sum fun d c => c * GlobalTheory.FlipRun.famProd ((A.comp (routeSmall t i j)).comp Bp) (φ d) x) = ∏ w ∈ locPl G t, (Tl) w (GlobalTheory.FlipRun.pathArgs B t w ((A.comp (routeSmall t i j)).comp Bp) x)) ∧ (∃ φ : PureT G ((A.comp (routeBig t i j)).comp Bp) → PureT G ((A.comp (routeBig t i j)).comp Bp), (∀ d ∈ (∑ κ ∈ s, ((σb κ).sum fun d c => Finsupp.single (((α κ).append d).append (β κ)) c)).support, GlobalTheory.FlipRun.VecAll ρ e ((A.comp (routeBig t i j)).comp Bp) (φ d) d) ∧ ∀ x : GlobalTheory.FlipRun.ArgT G ((A.comp (routeBig t i j)).comp Bp), GlobalTheory.FlipRun.HalfAll e ((A.comp (routeBig t i j)).comp Bp) x → ((∑ κ ∈ s, ((σb κ).sum fun d c => Finsupp.single (((α κ).append d).append (β κ)) c)).sum fun d c => c * GlobalTheory.FlipRun.famProd ((A.comp (routeBig t i j)).comp Bp) (φ d) x) = ∏ w ∈ locPl G t, (fun w => (locGrid G t w).flipTensor .one (psiAt W w) (unifAt w) (depthAt G w) i j (givenLevel G t w) (Tl w)) w (GlobalTheory.FlipRun.pathArgs B t w ((A.comp (routeBig t i j)).comp Bp) x)) := by
  intro D T L sc G μ₀ hL W B ρ t i j hi hj A Bp hA hB Tl hT hTb e he
  obtain ⟨nA, nB, hAB, ho⟩ := edges_outer hA hB
  rw [edges_comp, edges_comp, (edges_routes t i j).1] at hT
  rw [edges_comp, edges_comp, (edges_routes t i j).2] at hTb
  have hm : ∀ (l : List SplitFlip.Edge) b, b ∈ edges A ∨ b ∈ edges Bp → b ∈ edges A ++ l ++ edges Bp := fun l b hb => by
    rcases hb with hb | hb <;> simp [hb]
  have hflip : ∀ w ∈ locPl G t, ∀ x Z, flipAt W t i j w (depthAt G w) ((locGrid G t w).sliceB i j (Tl w) x) Z =
      (locGrid G t w).flipTensor .one (psiAt W w) (unifAt w) (depthAt G w) i j (givenLevel G t w) (Tl w) (setA i j x Z) :=
    fun w hw x Z => by
      rw [flipTensor_eq, joinA_setA, sliceB_setA (hT w hw)]
      · simp only [List.mem_append, not_or]
        exact ⟨⟨fun h => (ho _ (.inl h)).2.2.1 rfl, by simp⟩, fun h => (ho _ (.inr h)).2.2.1 rfl⟩
      · simp only [List.mem_append, not_or]
        exact ⟨⟨fun h => (ho _ (.inl h)).2.2.2 rfl, by simp⟩, fun h => (ho _ (.inr h)).2.2.2 rfl⟩
  obtain ⟨ι, s, φA, α, φB, β, rA, rB, vA, vB, hK⟩ := exists_classes_two hL B ρ t he (depthAt G) A Bp hA hB nA nB hAB
    (U := (∀ w, Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w)) ⊕
      ∀ w, Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w))
    (fun x => Sum.elim (fun Z => ∏ w ∈ locPl G t, (locGrid G t w).sliceB i j (Tl w) (x w) (Z w))
      fun Z => ∏ w ∈ locPl G t, flipAt W t i j w (depthAt G w) ((locGrid G t w).sliceB i j (Tl w) (x w)) (Z w))
    (fun x z y hz => by
      rcases y with Z | Z <;> refine Finset.prod_congr rfl fun w hw => ?_ <;> rw [Pi.add_apply, sliceB_add (hT w hw) _ _ _ _ (hz w hw)])
    (fun x y h w hw b hb => by
      rcases y with Z | Z
      · exact mem_of_update_two (hT w hw) (Finset.prod_ne_zero_iff.1 h w hw) (hm _ b hb) (ho b hb).1 (ho b hb).2.1
      · have := Finset.prod_ne_zero_iff.1 h w hw
        rw [hflip w hw] at this
        exact mem_of_update_two (hTb w hw) this (hm _ b hb) (ho b hb).2.2.1 (ho b hb).2.2.2)
  let Φ : ι → ∀ w, Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) → ℂ := fun κ w =>
    (locGrid G t w).sliceB i j (Tl w) (pathArgs B t w A (rA κ) + pathArgs B t w Bp (rB κ))
  have hΦ : ∀ κ, ∀ w ∈ locPl G t, SplitFlip.IsNatDatum (unifAt w) (depthAt G w) (Φ κ w) := fun κ w hw =>
    isNatDatum_small (hT w hw) (by simp) (by simp) _
  have hΦ' : ∀ κ, ∀ w ∈ locPl G t, SplitFlip.IsNatDatum (unifAt w) (depthAt G w) (flipAt W t i j w (depthAt G w) (Φ κ w)) :=
    fun κ w hw => by
      rw [funext (hflip w hw _)]
      exact isNatDatum_big (hTb w hw) (by simp) (by simp) _
  choose σs hs using fun κ => LocTensor.exists_hasLocal_small B ρ t ⟨i, hi⟩ ⟨j, hj⟩ hL he (hΦ κ)
  choose σb hb using fun κ => LocTensor.exists_hasLocal_big B ρ t ⟨i, hi⟩ ⟨j, hj⟩ hL he (hΦ' κ)
  refine ⟨ι, s, α, β, σs, σb, fun κ _ => ⟨Φ κ, hΦ κ, e, he, hs κ, hb κ⟩, fun κ hκ => ⟨⟨_, vA κ hκ⟩, _, vB κ hκ⟩, ?_, ?_⟩
  · choose φ₁ φ₂ c1 c2 using hs
    refine exists_rep_sandwich ρ hL he (onGrid_comp (onGrid_comp hA (onGrid_routeSmall t hi hj)) hB) s α φA β φB σs
      (fun κ d => (((), φ₁ κ d), φ₂ κ d)) vA vB (fun κ _ d hd => ⟨⟨trivial, (c1 κ d hd).1⟩, (c1 κ d hd).2⟩) _
      fun x y z hx hy hz => ?_
    refine Eq.trans (Finset.prod_congr rfl fun w hw => ?_) ((hK x z (.inl fun w => Matrix.fromCols
      (locArg B t w (.down t i j) y.1.2) (locArg B t w (.right i j) y.2).transpose) hx hz).trans
      (Finset.sum_congr rfl fun κ _ => congrArg _ ?_))
    · rw [pathArgs_append, pathArgs_append, pathArgs_snoc, pathArgs_snoc, SplitFlip.Grid.sliceB]
      · exact congrArg _ (add_update_two (pathArgs_of_notMem B t w A x _ fun h => (ho _ (.inl h)).1 rfl)
          (pathArgs_of_notMem B t w A x _ fun h => (ho _ (.inl h)).2.1 rfl)
          (pathArgs_of_notMem B t w Bp z _ fun h => (ho _ (.inr h)).1 rfl)
          (pathArgs_of_notMem B t w Bp z _ fun h => (ho _ (.inr h)).2.1 rfl) _ _)
      · intro b hb h
        rw [(edges_routes t i j).1] at hb
        have := ho b (.inl h)
        simp [this.1, this.2.1] at hb
      · intro b hb h
        have := ho b (.inr hb)
        rw [edges_comp, (edges_routes t i j).1] at h
        simp [this.1, this.2.1, hAB b hb] at h
    · refine Eq.trans ?_ ((c2 κ y.1.2 y.2 hy.1.2 hy.2).symm.trans (Finsupp.sum_congr fun d _ => ?_))
      · refine Finset.prod_congr rfl fun w _ => ?_
        exact congrArg (Φ κ w) (congrArg₂ Matrix.fromCols (dif_pos (And.intro hi.le hj))
          (congrArg Matrix.transpose (dif_pos (And.intro hi hj.le))))
      · exact congrArg _ (congrArg (· * _) (one_mul _).symm)
  · choose φ₁ φ₂ c1 c2 using hb
    refine exists_rep_sandwich ρ hL he (onGrid_comp (onGrid_comp hA (onGrid_routeBig t hi hj)) hB) s α φA β φB σb
      (fun κ d => (((), φ₁ κ d), φ₂ κ d)) vA vB (fun κ _ d hd => ⟨⟨trivial, (c1 κ d hd).1⟩, (c1 κ d hd).2⟩) _
      fun x y z hx hy hz => ?_
    refine Eq.trans (Finset.prod_congr rfl fun w hw => ?_) ((hK x z (.inr fun w => Matrix.fromCols
      (locArg B t w (.right i (j + 1)) y.1.2) (locArg B t w (.down t (i + 1) j) y.2).transpose) hx hz).trans
      (Finset.sum_congr rfl fun κ _ => congrArg _ ?_))
    · rw [hflip w hw, pathArgs_append, pathArgs_append, pathArgs_snoc, pathArgs_snoc, setA]
      · exact congrArg _ (add_update_two (pathArgs_of_notMem B t w A x _ fun h => (ho _ (.inl h)).2.2.1 rfl)
          (pathArgs_of_notMem B t w A x _ fun h => (ho _ (.inl h)).2.2.2 rfl)
          (pathArgs_of_notMem B t w Bp z _ fun h => (ho _ (.inr h)).2.2.1 rfl)
          (pathArgs_of_notMem B t w Bp z _ fun h => (ho _ (.inr h)).2.2.2 rfl) _ _)
      · intro b hb h
        rw [(edges_routes t i j).2] at hb
        have := ho b (.inl h)
        simp [this.2.2.1, this.2.2.2] at hb
      · intro b hb h
        have := ho b (.inr hb)
        rw [edges_comp, (edges_routes t i j).2] at h
        simp [this.2.2.1, this.2.2.2, hAB b hb] at h
    · refine Eq.trans ?_ ((c2 κ y.1.2 y.2 hy.1.2 hy.2).symm.trans (Finsupp.sum_congr fun d _ => ?_))
      · refine Finset.prod_congr rfl fun w _ => ?_
        exact congrArg (flipAt W t i j w (depthAt G w) (Φ κ w))
          (congrArg₂ Matrix.fromCols (dif_pos (And.intro hi hj)) (congrArg Matrix.transpose (dif_pos (And.intro hi hj))))
      · exact congrArg _ (congrArg (· * _) (one_mul _).symm)

theorem oneFlip : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : ℕ) (hi : i < D.R.m) (hj : j < D.R.m) (c : ℂ), c ≠ 0 → CommutesWith W B ρ t ⟨i, hi⟩ ⟨j, hj⟩ c → ∀ (A : Path T (.grid 0 D.R.m) (.grid i (j + 1))) (Bp : Path T (.grid (i + 1) j) (.grid D.R.m 0)), GlobalTheory.FlipRun.OnGrid D.R.m t A → GlobalTheory.FlipRun.OnGrid D.R.m t Bp → ∀ (Q : GlobalTheory.FlipRun.PolE G →₀ ℂ) (τ : TotT G ((A.comp (routeSmall t i j)).comp Bp)) (Tl : ∀ w, (locGrid G t w).Args → ℂ), (∀ w ∈ locPl G t, (locGrid G t w).IsTensor (unifAt w) (depthAt G w) (GlobalTheory.FlipRun.edges ((A.comp (routeSmall t i j)).comp Bp)) (Tl w)) → (∀ w ∈ locPl G t, (locGrid G t w).IsTensor (unifAt w) (depthAt G w) (GlobalTheory.FlipRun.edges ((A.comp (routeBig t i j)).comp Bp)) ((locGrid G t w).flipTensor .one (psiAt W w) (unifAt w) (depthAt G w) i j (givenLevel G t w) (Tl w))) → GlobalTheory.FlipRun.RepFin B ρ t _ τ Tl → ∃ τ' : TotT G ((A.comp (routeBig t i j)).comp Bp), GlobalTheory.FlipRun.RepFin B ρ t _ τ' (fun w => (locGrid G t w).flipTensor .one (psiAt W w) (unifAt w) (depthAt G w) i j (givenLevel G t w) (Tl w)) ∧ ∀ M : Vol G, M.Is t → GlobalTheory.FlipRun.CuspStep W M ρ t → ∀ F : Fn G (.grid 0 D.R.m), GlobalTheory.FlipRun.IsCuspListed W.θ _ F → TotConv W M _ (GlobalTheory.FlipRun.tensE W _ Q τ) F → TotConv W M _ (GlobalTheory.FlipRun.tensE W _ (GlobalTheory.FlipRun.flipPolE ρ i j Q) τ') F ∧ liftT W M _ (GlobalTheory.FlipRun.tensE W _ Q τ) F = c⁻¹ • liftT W M _ (GlobalTheory.FlipRun.tensE W _ (GlobalTheory.FlipRun.flipPolE ρ i j Q) τ') F := by
  intro D T L sc G μ₀ hL W B ρ t i j hi hj c hc hcomm A Bp hA hBp Q τ Tl hT hTb hR
  obtain ⟨e, he, φ, hφ, hfun⟩ := hR
  obtain ⟨ι, s, α, β, σs, σb, hflip, hout, hR₂, hR'⟩ := exists_decomp hL W B ρ t i j hi hj A Bp hA hBp Tl hT hTb e he
  have hPs : OnGrid D.R.m t ((A.comp (routeSmall t i j)).comp Bp) :=
    onGrid_comp (onGrid_comp hA (onGrid_routeSmall t hi hj)) hBp
  have hPb : OnGrid D.R.m t ((A.comp (routeBig t i j)).comp Bp) :=
    onGrid_comp (onGrid_comp hA (onGrid_routeBig t hi hj)) hBp
  refine ⟨∑ κ ∈ s, sandwich (α κ) (σb κ) (β κ), ⟨e, he, hR'⟩, fun M hM hC F hF _ => ?_⟩
  obtain ⟨φ', hφ', -⟩ := hR'
  obtain ⟨φ₂, hφ₂, hfun₂⟩ := hR₂
  refine ⟨totConv_tensE M ρ t he hC _ hPb _ φ' hφ' F hF _, ?_⟩
  rw [GlobalTheory.T.totalTensorThetaLift_eq_of_schwartz_eq hL M ρ t he hC _ hPs τ _ φ φ₂ hφ hφ₂ (fun x hx => (hfun x hx).trans (hfun₂ x hx).symm) F hF Q,
    tensE_sum, liftT_sum, tensE_sum, liftT_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun κ hκ => ?_
  obtain ⟨Φ, hΦ, hF'⟩ := hflip κ hκ
  obtain ⟨⟨φA, hφA⟩, φB, hφB⟩ := hout κ hκ
  exact GlobalTheory.T.sandwichedFlip_routeThroughSmall_eq_inv_const_routeBig M B ρ t i j hi hj c hc hcomm hM hC A Bp hA hBp e he (α κ) (β κ) φA φB hφA hφB (σs κ) (σb κ) Φ hΦ hF' F hF Q

end GlobalTheory.FlipRun

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridSquareFlipSmallRouteEqInvSmulBigRouteStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridSquareFlip_smallRoute_eq_inv_smul_bigRoute : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : ℕ) (hi : i < D.R.m) (hj : j < D.R.m) (c : ℂ), c ≠ 0 → CommutesWith W B ρ t ⟨i, hi⟩ ⟨j, hj⟩ c → ∀ (A : Path T (.grid 0 D.R.m) (.grid i (j + 1))) (Bp : Path T (.grid (i + 1) j) (.grid D.R.m 0)), GlobalTheory.FlipRun.OnGrid D.R.m t A → GlobalTheory.FlipRun.OnGrid D.R.m t Bp → ∀ (Q : GlobalTheory.FlipRun.PolE G →₀ ℂ) (τ : TotT G ((A.comp (routeSmall t i j)).comp Bp)) (Tl : ∀ w, (locGrid G t w).Args → ℂ), (∀ w ∈ locPl G t, (locGrid G t w).IsTensor (unifAt w) (depthAt G w) (GlobalTheory.FlipRun.edges ((A.comp (routeSmall t i j)).comp Bp)) (Tl w)) → (∀ w ∈ locPl G t, (locGrid G t w).IsTensor (unifAt w) (depthAt G w) (GlobalTheory.FlipRun.edges ((A.comp (routeBig t i j)).comp Bp)) ((locGrid G t w).flipTensor .one (psiAt W w) (unifAt w) (depthAt G w) i j (givenLevel G t w) (Tl w))) → GlobalTheory.FlipRun.RepFin B ρ t _ τ Tl → ∃ τ' : TotT G ((A.comp (routeBig t i j)).comp Bp), GlobalTheory.FlipRun.RepFin B ρ t _ τ' (fun w => (locGrid G t w).flipTensor .one (psiAt W w) (unifAt w) (depthAt G w) i j (givenLevel G t w) (Tl w)) ∧ ∀ M : Vol G, M.Is t → GlobalTheory.FlipRun.CuspStep W M ρ t → ∀ F : Fn G (.grid 0 D.R.m), GlobalTheory.FlipRun.IsCuspListed W.θ _ F → TotConv W M _ (GlobalTheory.FlipRun.tensE W _ Q τ) F → TotConv W M _ (GlobalTheory.FlipRun.tensE W _ (GlobalTheory.FlipRun.flipPolE ρ i j Q) τ') F ∧ liftT W M _ (GlobalTheory.FlipRun.tensE W _ Q τ) F = c⁻¹ • liftT W M _ (GlobalTheory.FlipRun.tensE W _ (GlobalTheory.FlipRun.flipPolE ρ i j Q) τ') F := by
  first | exact @GlobalTheory.FlipRun.oneFlip | exact GlobalTheory.FlipRun.oneFlip | (intros; apply GlobalTheory.FlipRun.oneFlip <;> assumption)
end
