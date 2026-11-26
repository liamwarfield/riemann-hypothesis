module

public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceGoodSignature
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.InertKernelTheory.StatementIota

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowParamOfThetaLiftBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowParamOfThetaLiftBaseChange
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.RowThetaParam

section Gen

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem lpSum_zero_left {w : PlE H} (a : A.LP w) : A.lpSum (A.lpZero w) a = a := by
  rw [A.lpSum_comm, A.lpSum_zero]

theorem isoLoc_cons (p : Part A.CG) (L : List (Part A.CG)) (w : PlE H) :
    isoLoc N A (p :: L) w = A.lpSum (spehLoc N A p w) (isoLoc N A L w) := rfl

theorem isoLoc_nil (w : PlE H) : isoLoc N A [] w = A.lpZero w := rfl

theorem isoLoc_append (L L' : List (Part A.CG)) (w : PlE H) :
    isoLoc N A (L ++ L') w = A.lpSum (isoLoc N A L w) (isoLoc N A L' w) := by
  induction L with
  | nil => rw [List.nil_append, isoLoc_nil, lpSum_zero_left]
  | cons p L ih => rw [List.cons_append, isoLoc_cons, isoLoc_cons, ih, A.lpSum_assoc]

theorem isoLoc_perm {L L' : List (Part A.CG)} (h : L.Perm L') (w : PlE H) :
    isoLoc N A L w = isoLoc N A L' w := by
  induction h with
  | nil => rfl
  | cons p _ ih => rw [isoLoc_cons, isoLoc_cons, ih]
  | swap p q L =>
    rw [isoLoc_cons, isoLoc_cons, isoLoc_cons, isoLoc_cons, ← A.lpSum_assoc, ← A.lpSum_assoc,
      A.lpSum_comm (spehLoc N A q w)]
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem lpChar_zero (hLP : SumRepresentations.At.TieLP N A)
    (hC : ∀ w (a b c : A.LP w), A.lpSum a c = A.lpSum b c → a = b) {w : PlE H} (χ : A.LP w)
    (hχ : A.lpDim χ = 1) : A.lpChar (A.lpZero w) χ = A.lpZero w := by
  have h1 := (hLP w (A.lpZero w) (A.lpZero w) χ χ 0 hχ hχ).1
  rw [A.lpSum_zero] at h1
  symm
  apply hC w _ _ (A.lpChar (A.lpZero w) χ)
  rw [lpSum_zero_left, ← h1]

theorem foldr_tw (hLP : SumRepresentations.At.TieLP N A)
    (hC : ∀ w (a b c : A.LP w), A.lpSum a c = A.lpSum b c → a = b) {a : ℕ} (π : A.CG a) (χ : A.CG 1)
    (w : PlE H) {α : Type} (c : α → ℝ) (l : List α) :
    l.foldr (fun k acc => A.lpSum (A.lpTw (A.locG (A.tw π χ) w) (c k)) acc) (A.lpZero w) =
      A.lpChar (l.foldr (fun k acc => A.lpSum (A.lpTw (A.locG π w) (c k)) acc) (A.lpZero w))
        (A.locG χ w) := by
  have hd : A.lpDim (A.locG χ w) = 1 := A.locG_dim χ w
  induction l with
  | nil => exact (lpChar_zero N A hLP hC _ hd).symm
  | cons k l ih =>
    simp only [List.foldr_cons]
    rw [ih, A.locG_tw, (hLP w _ _ _ _ (c k) hd hd).1, (hLP w (A.locG π w) (A.locG π w) _ _ (c k) hd hd).2.1]

theorem spehLoc_tw (hLP : SumRepresentations.At.TieLP N A)
    (hC : ∀ w (a b c : A.LP w), A.lpSum a c = A.lpSum b c → a = b) (p : Part A.CG) (χ : A.CG 1)
    (w : PlE H) :
    spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w = A.lpChar (spehLoc N A p w) (A.locG χ w) := by
  unfold spehLoc
  exact foldr_tw N A hLP hC p.π χ w (fun k => ((p.d : ℝ) - 1) / 2 - k) _

theorem isoLoc_twistIso (hLP : SumRepresentations.At.TieLP N A)
    (hC : ∀ w (a b c : A.LP w), A.lpSum a c = A.lpSum b c → a = b) (L : List (Part A.CG)) (χ : A.CG 1)
    (w : PlE H) :
    isoLoc N A (twistIso N A L χ) w = A.lpChar (isoLoc N A L w) (A.locG χ w) := by
  have hd : A.lpDim (A.locG χ w) = 1 := A.locG_dim χ w
  induction L with
  | nil => exact (lpChar_zero N A hLP hC _ hd).symm
  | cons p L ih =>
    show A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A L χ) w) = _
    rw [ih, spehLoc_tw N A hLP hC, isoLoc_cons, (hLP w _ _ _ _ 0 hd hd).1]

theorem eta_pair (w : PlE H) :
    A.lpChar (A.locG A.etaT w) (A.locG A.etaTinv w) = A.lpUnr w {1} ∧
    A.lpChar (A.locG A.etaTinv w) (A.locG A.etaT w) = A.lpUnr w {1} := by
  have hu := A.etaT_unr w
  obtain ⟨hu', hf'⟩ := A.etaTinv_def w
  have hcard := A.frobEig_card _ hu
  rw [A.locG_dim] at hcard
  obtain ⟨b, hb⟩ := Multiset.card_eq_one.1 hcard
  have hb0 : b ≠ 0 := by
    intro h
    apply A.frobEig_ne_zero _ hu
    rw [hb, h]
    exact Multiset.mem_singleton_self 0
  rw [hb, Multiset.map_singleton] at hf'
  have d1 := A.locG_dim A.etaT w
  have d2 := A.locG_dim A.etaTinv w
  constructor
  · have hun := A.unr_char _ _ d2 hu hu'
    rw [A.unr_eq_lpUnr _ hun, A.frobEig_char _ _ b⁻¹ hu hu' d2 hf', hb, Multiset.map_singleton,
      mul_inv_cancel₀ hb0]
  · have hun := A.unr_char _ _ d1 hu' hu
    rw [A.unr_eq_lpUnr _ hun, A.frobEig_char _ _ b hu' hu d1 hb, hf', Multiset.map_singleton,
      inv_mul_cancel₀ hb0]

theorem lpChar_eta_inv (hLP : SumRepresentations.At.TieLP N A) {w : PlE H} (a : A.LP w) :
    A.lpChar (A.lpChar a (A.locG A.etaT w)) (A.locG A.etaTinv w) = a ∧
    A.lpChar (A.lpChar a (A.locG A.etaTinv w)) (A.locG A.etaT w) = a := by
  have d1 := A.locG_dim A.etaT w
  have d2 := A.locG_dim A.etaTinv w
  constructor
  · rw [(hLP w a a _ _ 0 d1 d2).2.2.2.1, (eta_pair N A w).1, (hLP w a a _ _ 0 d1 d2).2.2.2.2.1]
  · rw [(hLP w a a _ _ 0 d2 d1).2.2.2.1, (eta_pair N A w).2, (hLP w a a _ _ 0 d2 d1).2.2.2.2.1]

theorem tw_eta_inv (hLP : SumRepresentations.At.TieLP N A)
    (hC : ∀ w (a b c : A.LP w), A.lpSum a c = A.lpSum b c → a = b)
    (hAN : ∀ Pa Pa' : List (Part A.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ p.d = 1) → (∀ p ∈ Pa', 1 ≤ p.a ∧ p.d = 1) →
      (∀ᶠ w in Filter.cofinite, isoLoc N A Pa w = isoLoc N A Pa' w) → Pa.Perm Pa')
    {a : ℕ} (ha : 1 ≤ a) (π : A.CG a) : A.tw (A.tw π A.etaT) A.etaTinv = π := by
  have h := hAN [⟨a, A.tw (A.tw π A.etaT) A.etaTinv, 1⟩] [⟨a, π, 1⟩]
    (by simp [ha]) (by simp [ha]) (Filter.Eventually.of_forall fun w => by
      show isoLoc N A (twistIso N A (twistIso N A [⟨a, π, 1⟩] A.etaT) A.etaTinv) w = _
      rw [isoLoc_twistIso N A hLP hC, isoLoc_twistIso N A hLP hC, (lpChar_eta_inv N A hLP _).1])
  rw [List.singleton_perm_singleton] at h
  injection h with _ h2

theorem twistIso_eta_inv (hLP : SumRepresentations.At.TieLP N A)
    (hC : ∀ w (a b c : A.LP w), A.lpSum a c = A.lpSum b c → a = b)
    (hAN : ∀ Pa Pa' : List (Part A.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ p.d = 1) → (∀ p ∈ Pa', 1 ≤ p.a ∧ p.d = 1) →
      (∀ᶠ w in Filter.cofinite, isoLoc N A Pa w = isoLoc N A Pa' w) → Pa.Perm Pa')
    (L : List (Part A.CG)) (hL : ∀ p ∈ L, 1 ≤ p.a) :
    twistIso N A (twistIso N A L A.etaT) A.etaTinv = L := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    show (⟨p.a, A.tw (A.tw p.π A.etaT) A.etaTinv, p.d⟩ : Part A.CG) :: twistIso N A (twistIso N A L A.etaT) A.etaTinv = p :: L
    rw [ih (fun q hq => hL q (List.mem_cons_of_mem _ hq)),
      tw_eta_inv N A hLP hC hAN (hL p List.mem_cons_self)]

theorem isBCV_of_perm {i : N.Loc} {P : A.AV i} {Pa Pa' : List (Part A.CG)} (h : Pa.Perm Pa')
    (hB : IsBCV N A i P Pa) : IsBCV N A i P Pa' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hB
  refine ⟨fun p hp => h1 p (h.mem_iff.2 hp), (h.map _).nodup_iff.1 h2, ?_, fun w hw => ?_,
    fun w hw => ?_, fun τ => ?_⟩
  · unfold rankIso at h3 ⊢
    rw [← (h.map _).sum_eq]
    exact h3
  · rw [← isoLoc_perm N A h]
    exact h4 w hw
  · rw [← isoLoc_perm N A h]
    exact h5 w hw
  · rw [← h6 τ]
    unfold isoInf
    exact ((h.map _).sum_eq).symm

end Gen

theorem param_of_theta (D : D7) (h0 : SumRepresentations.tie0 D) (h3 : SumRepresentations.adm3 D) (h4 : SumRepresentations.ArchimedeanSignatureMatching D) (h5 : SumRepresentations.adm5 D)
    (i : D.nd.Loc) (σ : D.what₂.FT) (P : D.naut.AV i) (Pa : List (Part D.naut.CG))
    (hθ : thetaOf D.nd D.naut i σ P) (hB : IsBCV D.nd D.naut i P Pa)
    (hm : (⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ : Part D.naut.CG) ∈ Pa) :
    ∃ Sig, HasParamW D.nd D.naut i σ Sig ∧
      IsBCV D.nd D.naut i P (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) := by
  have hLP : SumRepresentations.At.TieLP D.nd D.naut := h0.1
  have hC := h4.2.2
  have hAN := h5.1
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hm
  set m : Part D.naut.CG := ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ with hmdef
  set L := l₁ ++ l₂ with hLdef
  have hperm : (l₁ ++ m :: l₂).Perm (L ++ [m]) :=
    List.perm_middle.trans (List.perm_append_singleton _ _).symm
  have hLmem : ∀ p ∈ L, p ∈ l₁ ++ m :: l₂ := fun p hp => by
    rcases List.mem_append.1 hp with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  have hL : ∀ p ∈ L, 1 ≤ p.a ∧ 1 ≤ p.d := fun p hp =>
    ⟨(hB.1 p (hLmem p hp)).1, (hB.1 p (hLmem p hp)).2.1⟩
  have hB' := isBCV_of_perm D.nd D.naut hperm hB
  refine ⟨twistIso D.nd D.naut L D.naut.etaT, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact hL q hq
  · have hr := hB'.2.2.1
    have e1 : rankIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) = rankIso D.nd D.naut L := by
      unfold rankIso twistIso
      rw [List.map_map]
      rfl
    rw [e1]
    unfold rankIso at hr ⊢
    rw [List.map_append, List.sum_append] at hr
    simp only [hmdef, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero] at hr
    have : D.R.nV = D.R.r + D.R.t := rfl
    omega
  · intro w hw
    have e1 := h3 i σ P hθ w hw
    rw [← hB'.2.2.2.1 w hw, isoLoc_append, (hLP w (D.naut.locW i σ w) (spehLoc D.nd D.naut (muPart D.nd D.naut i) w)
      (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaTinv w) 0 (D.naut.locG_dim _ w) (D.naut.locG_dim _ w)).1]
      at e1
    have e2 : isoLoc D.nd D.naut [m] w =
        D.naut.lpChar (spehLoc D.nd D.naut (muPart D.nd D.naut i) w) (D.naut.locG D.naut.etaTinv w) := by
      rw [isoLoc_cons, isoLoc_nil, D.naut.lpSum_zero]
      exact spehLoc_tw D.nd D.naut hLP hC (muPart D.nd D.naut i) D.naut.etaTinv w
    rw [e2] at e1
    have e3 := hC w _ _ _ e1
    rw [isoLoc_twistIso D.nd D.naut hLP hC, e3, (lpChar_eta_inv D.nd D.naut hLP _).2]
  · have e : twistIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT ++ [muPart D.nd D.naut i])
        D.naut.etaTinv = L ++ [m] := by
      rw [show twistIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT ++ [muPart D.nd D.naut i])
          D.naut.etaTinv = twistIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) D.naut.etaTinv ++
            twistIso D.nd D.naut [muPart D.nd D.naut i] D.naut.etaTinv from List.map_append ..,
        twistIso_eta_inv D.nd D.naut hLP hC hAN L (fun p hp => (hL p hp).1)]
      rfl
    rw [e]
    exact hB'

end GlobalTheory.RowThetaParam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowParamOfThetaLiftBaseChangeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_param_of_thetaLift_baseChange : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm3 D → SumRepresentations.ArchimedeanSignatureMatching D → SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (σ : D.what₂.FT) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), thetaOf D.nd D.naut i σ P → IsBCV D.nd D.naut i P Pa → (⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ : Part D.naut.CG) ∈ Pa → ∃ Sig, HasParamW D.nd D.naut i σ Sig ∧ IsBCV D.nd D.naut i P (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) := by
  first | exact @GlobalTheory.RowThetaParam.param_of_theta | exact GlobalTheory.RowThetaParam.param_of_theta | (intros; apply GlobalTheory.RowThetaParam.param_of_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedMatchOfHeckeGalois
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.NRows

theorem point_determines : ∀ D : D7, SumRepresentations.adm1 D → SumRepresentations.adm5 D → (∀ (i : D.nd.Loc) (x : D.nd.X i), ∃ ρ, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ) → (∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2) ∧ ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.locAutHodgeTateWeightsLevelZero i τ) → ∀ (i : D.nd.Loc) (P P' : D.naut.AV i), D.naut.ptV i P ≠ none → D.naut.ptV i P = D.naut.ptV i P' → (∀ Pa Pa', IsBCV D.nd D.naut i P Pa → IsBCV D.nd D.naut i P' Pa' → Pa.Perm Pa') ∧ ∀ w, w ∉ D.nd.S i → w ∉ D.nd.Q i → (IsSplitPl D.host w → D.naut.locV i P w = D.naut.locV i P' w) ∧ (¬ IsSplitPl D.host w → ubc D.R.nV (D.naut.satV i P w) = ubc D.R.nV (D.naut.satV i P' w)) := by
  intro D h1 h5 hex hcomp i P P' hP hPP'
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hP
  obtain ⟨ρ, hρ⟩ := hex i x
  have hx' : D.naut.ptV i P' = some x := hPP' ▸ hx

  have key : ∀ Pa Pa', IsBCV D.nd D.naut i P Pa → IsBCV D.nd D.naut i P' Pa' →
      ∀ w, isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pa' w := by
    intro Pa Pa' hB hB' w
    have c := hcomp i x P Pa hx hB ρ hρ
    have c' := hcomp i x P' Pa' hx' hB' ρ hρ
    have e : D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2) =
        D.naut.lpTw (isoLoc D.nd D.naut Pa' w) ((1 - (D.R.nV : ℝ)) / 2) := by
      by_cases hw : w ∈ placesOver D.host.E (D.nd.l i)
      · rw [← (c.2 w hw).2.1, ← (c'.2 w hw).2.1]
      · rw [← c.1 w hw, ← c'.1 w hw]
    have e2 := congrArg (fun a => D.naut.lpTw a (-((1 - (D.R.nV : ℝ)) / 2))) e
    simpa only [D.naut.lpTw_add, add_neg_cancel, D.naut.lpTw_zero] using e2
  refine ⟨fun Pa Pa' hB hB' => ?_, fun w _ _ => ?_⟩
  · exact h5.2.1 Pa Pa' hB.1 hB'.1 (Filter.Eventually.of_forall (key Pa Pa' hB hB'))
  · obtain ⟨Pa, hB⟩ := h1 i P
    obtain ⟨Pa', hB'⟩ := h1 i P'
    refine ⟨fun hs => ?_, fun hs => ?_⟩
    · rw [← hB.2.2.2.1 w hs, ← hB'.2.2.2.1 w hs, key Pa Pa' hB hB' w]
    · rw [← (hB.2.2.2.2.1 w hs).2, ← (hB'.2.2.2.2.1 w hs).2, key Pa Pa' hB hB' w]

end GlobalTheory.NRows
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisLocalWeights
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.NRows

open Pointwise

theorem ine_conj_of_smul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {A : ValuationSubring Ω} {g σ : G F Ω} (hσ : σ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Ine (F := F) A := by
  have m : ∀ y : Ω, y ∈ g • A ↔ (g⁻¹ : G F Ω) y ∈ A := fun y => by
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  have m' : ∀ y : Ω, (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : G F Ω) y) < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', m, m, map_inv₀,
      map_eq_zero_iff _ (g⁻¹ : G F Ω).injective]
  have c : ∀ x : Ω, (g⁻¹ : G F Ω) (g x) = x := fun x => by
    show (g⁻¹ * g) x = x
    simp
  refine ⟨?_, fun x hx => ?_⟩
  · have h : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h, inv_smul_smul]
  · have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff, m, c]
      exact (A.valuation_le_one_iff x).1 hx
    have h := (m' _).1 (hσ.2 _ hx')
    rw [map_sub, c] at h
    exact h

theorem crys_unram_of_lgc : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → (∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2) ∧ ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.locAutHodgeTateWeightsLevelZero i τ) → ∀ (i : D.nd.Loc) (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i))), (∀ x, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x (mapRep (iotaOQ D.nd D.naut i) (r x))) → (∀ w ∈ placesOver D.host.E (D.nd.l i),
      (D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → ∀ x, D.naut.IsCrysW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w ∧
        ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (r x)) τ = D.naut.locAutHodgeTateWeightsLevelZero i τ) ∧
      ((D.nd.l i = D.host.g 0 ∨ D.nd.l i = D.host.g 1) → ∀ x,
        (∀ P Pa, D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → D.naut.mono0 (isoLoc D.nd D.naut Pa w)) →
        D.naut.IsPotCrysW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w)) ∧
    ∀ x w, w ∉ placesOver D.host.E (D.nd.l i) → w ∉ D.nd.S i → w ∉ D.nd.Q i → UnramAt (F := D.host.E) (r x) w := by
  intro D htie hadm hLGC i r hr
  obtain ⟨-, -, hGal⟩ := htie
  have hl : (D.nd.l i).Prime := Fact.out
  have key : ∀ x, ∃ P Pa, D.naut.ptV i P = some x ∧ IsBCV D.nd D.naut i P Pa := fun x => by
    obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨Pa, hPa⟩ := hadm i P
    exact ⟨P, Pa, hP, hPa⟩
  have hunr : ∀ P Pa w, IsBCV D.nd D.naut i P Pa → w ∉ D.nd.Q i →
      (∀ k, w ∉ placesOver D.host.E (D.host.g k)) →
      w ∉ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde) →
      D.naut.unr (isoLoc D.nd D.naut Pa w) := by
    intro P Pa w hB hQ hg hp
    by_cases hs : IsSplitPl D.host w
    · rw [hB.2.2.2.1 w hs]
      exact D.naut.locV_unr i P w hs hQ hg hp
    · exact (hB.2.2.2.2.1 w hs).1
  refine ⟨fun w hw => ⟨fun hl0 hl1 x => ?_, fun _ x hm => ?_⟩, fun x w hwl hwS hwQ => ?_⟩
  · obtain ⟨P, Pa, hP, hB⟩ := key x
    have h := (hLGC i x P Pa hP hB _ (hr x)).2 w hw
    refine ⟨(hGal.1 i _ _ w hw (hr x).1).2 ⟨h.1, ?_⟩, fun τ hτ => h.2.2 τ hτ⟩
    rw [h.2.1, D.naut.unr_tw]
    refine hunr P Pa w hB (fun hq => D.nd.SQ_l i w (Or.inr hq) hw) (fun k => ?_) ?_
    · have hk : D.nd.l i ≠ D.host.g k := by
        fin_cases k
        · exact hl0
        · exact hl1
      exact SumRepresentations.not_over_of_ne hl (D.host.g_prime k) hk hw
    · split_ifs with hpd
      · exact SumRepresentations.not_over_of_ne hl D.host.pde'_prime (hpd ▸ D.host.pde_ne) hw
      · exact SumRepresentations.not_over_of_ne hl D.host.pde_prime hpd hw
  · obtain ⟨P, Pa, hP, hB⟩ := key x
    have h := (hLGC i x P Pa hP hB _ (hr x)).2 w hw
    refine (hGal.2.1 i _ _ w hw (hr x).1).2 ⟨h.1, ?_⟩
    rw [h.2.1, D.naut.monomial_twist_iff]
    exact hm P Pa hP hB
  · obtain ⟨P, Pa, hP, hB⟩ := key x
    have h := (hLGC i x P Pa hP hB _ (hr x)).1 w hwl
    have hS : ¬ ((w ∈ placesOver D.host.E (D.host.g 0) ∨ w ∈ placesOver D.host.E (D.host.g 1) ∨
        w ∈ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde)) ∧
        w ∉ placesOver D.host.E (D.nd.l i)) := fun hh => hwS ((D.nd.S_def i w).2 hh)
    have hu : D.naut.unr (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) := by
      rw [h, D.naut.unr_tw]
      refine hunr P Pa w hB hwQ (fun k hk => hS ⟨?_, hwl⟩) (fun hk => hS ⟨Or.inr (Or.inr hk), hwl⟩)
      fin_cases k
      · exact Or.inl hk
      · exact Or.inr (Or.inl hk)
    have h1 := (D.naut.wdOf_unr i _ w hwl (hr x).1).1 hu
    intro A hA σ hσ
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (D.nd.plOm.2 w) hA
    have hσ' : σ ∈ Ine (F := D.host.E) (g • D.nd.plOm.1 w) := by rw [hg]; exact hσ
    have h2 := h1 _ (ine_conj_of_smul hσ')
    have h3 : mapRep (iotaOQ D.nd D.naut i) (r x) σ = 1 := by
      have e : σ = g * (g⁻¹ * σ * g) * g⁻¹ := by group
      rw [e, map_mul, map_mul, h2, mul_one, ← map_mul, mul_inv_cancel, map_one]
    apply Units.ext
    have h4 := congrArg (fun u : GL (Fin D.R.nV) (Qbar (D.nd.l i)) => u.val) h3
    simp only [mapRep, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_one] at h4
    refine Matrix.map_injective (SumRepresentations.iotaOQ_injective D.nd D.naut i) ?_
    show (r x σ).val.map (iotaOQ D.nd D.naut i) = (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map (iotaOQ D.nd D.naut i)
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact h4

end GlobalTheory.NRows
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaOneGenusOne
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweDualityUpwardOfLocalThetaSplitPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweDualityUpwardOfLocalThetaSplitPlaces
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowTie

theorem howeUp_of_pairLift : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
    (i : N.Loc), GlobalTheory.RowTie.PairLift N A i → GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i →
    GlobalTheory.RowTie.RepOfLoc N A i → GlobalTheory.ThetaExh.HoweUp N A i := by
  intro R H what₂ N A i hL hB hS hR σ P P' hP hP'
  refine GlobalTheory.T.automorphicRep_eq_of_eq_at_almost_all_split_places R H what₂ N A i hB hS hR P P' (Filter.Eventually.of_forall fun w hw => ?_)
  rw [hL σ P hP w hw, hL σ P' hP' w hw]

end GlobalTheory.RowTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweDualityUpwardOfLocalThetaSplitPlacesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeDualityUpward_of_localThetaSplitPlaces : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (i : N.Loc), GlobalTheory.RowTie.PairLift N A i → GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.RowTie.RepOfLoc N A i → GlobalTheory.ThetaExh.HoweUp N A i := by
  first | exact @GlobalTheory.RowTie.howeUp_of_pairLift | exact GlobalTheory.RowTie.howeUp_of_pairLift | (intros; apply GlobalTheory.RowTie.howeUp_of_pairLift <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.Proof.ThetaOneGenusOne

theorem thetaOne_of_ties : ∀ (D : D7), (∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) → (∀ i, GlobalTheory.RowTie.PairLift D.nd D.naut i) → (∀ i, GlobalTheory.ThetaExh.TypeOrth D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.BCEx D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.SplitBC D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.RepOfLoc D.nd D.naut i) → GlobalTheory.RowCopy.ThetaOne D := by
  intro D hpos hpair horth hbc hsplit hrep
  exact GlobalTheory.Proof.HoweThetaLiftComponents.eachRowHasThetaLift_of_howe _ _ _ D.nd D.naut hpos
    (fun i => GlobalTheory.T.howeDualityUpward_of_localThetaSplitPlaces _ _ _ D.nd D.naut i (hpair i) (hbc i) (hsplit i) (hrep i)) horth

end GlobalTheory.Proof.ThetaOneGenusOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPartRecursion
namespace GlobalTheory.Proof.GoodComponentRecursion

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem goodPartRec_of_ties : ∀ (D : D7), GlobalTheory.RowTie.WDTie D.nd D.naut → GlobalTheory.RowCopy.ThetaOne D →
    (∀ i, GlobalTheory.ThetaExh.LiftParam D.nd D.naut i) → (∀ i, GlobalTheory.ThetaExh.PtLocal D.nd D.naut i) →
    (∀ i, GlobalTheory.RowTie.BCEx D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.SplitBC D.nd D.naut i) →
    ∀ i, GlobalTheory.RowCopy.GoodPartRec D.nd D.naut i := by
  intro D hW h1 hlift hpt hbc hsp i
  exact GlobalTheory.Proof.SplitPlaceGoodSignature.goodPart_of_lifts D.nd D.naut i h1
    (GlobalTheory.T.localParameterLaws_of_weilDeligneIdentification _ _ _ D.nd D.naut hW).1 (hlift i) (hpt i)
    (GlobalTheory.T.splitComponentsDeterminedByPoint_of_baseChange _ _ _ D.nd D.naut i (hbc i) (hsp i))

end GlobalTheory.Proof.GoodComponentRecursion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParUpRecOfTies
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointDeterminedBySplitComponentsOfBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointDeterminedBySplitComponentsOfBaseChange
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.PtOfLocSplit

theorem eventually_splitOut {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) :
    ∀ᶠ w in Filter.cofinite, IsSplitPl H w → SplitOut N i w := by
  have hl : (N.l i).Prime := Fact.out
  have hfin : (placesOver H.E (N.l i)).Finite := by
    have h0 : Ideal.span {((N.l i : ℕ) : 𝓞 H.E)} ≠ 0 := by simpa using hl.ne_zero
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  filter_upwards [hfin.eventually_cofinite_notMem, (N.S i).eventually_cofinite_notMem,
    (N.Q i).eventually_cofinite_notMem] with w h1 h2 h3 hw using ⟨hw, h1, h2, h3⟩

theorem main : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (i : N.Loc), GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.RowTie.RepOfLoc N A i → GlobalTheory.ThetaExh.PtOfLoc N A i := by
  intro R H what₂ N A i hBC hSp hRep P P' x hx hloc
  have hPP : P = P' := GlobalTheory.T.automorphicRep_eq_of_eq_at_almost_all_split_places R H what₂ N A i hBC hSp hRep P P' <| by
    filter_upwards [eventually_splitOut N i] with w hw hs using hloc w (hw hs)
  rw [hPP]; exact hx

end GlobalTheory.PtOfLocSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointDeterminedBySplitComponentsOfBaseChangeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointDeterminedBySplitComponents_of_baseChange : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (i : N.Loc), GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.RowTie.RepOfLoc N A i → GlobalTheory.ThetaExh.PtOfLoc N A i := by
  first | exact @GlobalTheory.PtOfLocSplit.main | exact GlobalTheory.PtOfLocSplit.main | (intros; apply GlobalTheory.PtOfLocSplit.main <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowTie

theorem parUpRec_of_ties : ∀ (D : D7), GlobalTheory.RowTie.WDTie D.nd D.naut → GlobalTheory.RowCopy.ThetaOne D →
    (∀ i, GlobalTheory.RowTie.PairLift D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.BCEx D.nd D.naut i) →
    (∀ i, GlobalTheory.RowTie.SplitBC D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.RepOfLoc D.nd D.naut i) →
    ∀ i, GlobalTheory.RowCopy.ParUpRec D.nd D.naut i := by
  intro D T hθ hpair hbc hsplit hrep i x hx Sig hSig
  have h := GlobalTheory.ParUpRoad.main _ _ _ D.nd D.naut hθ (GlobalTheory.T.localParameterLaws_of_weilDeligneIdentification _ _ _ D.nd D.naut T).1
    (fun i => splitLift_of_pairLift _ _ _ D.nd D.naut i (hpair i))
    (fun i => GlobalTheory.T.pointDeterminedBySplitComponents_of_baseChange _ _ _ D.nd D.naut i (hbc i) (hsplit i) (hrep i))
  exact (GlobalTheory.IndefiniteRowSideFullHecke.ThetaEigenspaceImage.thetaTMapsIntoEig_iff_map_le D.nd D.naut).1 h i x Sig hx hSig

end GlobalTheory.RowTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DownMemRecOfTies
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemBiSupOfOrthogonal
noncomputable section

namespace GlobalTheory.DownMemRoad

open Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.ThetaExh
  GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftOfEachComponent

theorem mem_biSup_of_orthogonal {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (U : ι → Submodule ℂ V) (S : Set ι) (htop : ⨆ k, U k = ⊤) (horth : ∀ k k', k ≠ k' → U k ⟂ U k')
    {v : V} (hv : ∀ k ∉ S, v ∈ (U k)ᗮ) : v ∈ ⨆ k ∈ S, U k := by
  have hsup : (⨆ k ∈ S, U k) ⊔ (⨆ k ∈ Sᶜ, U k) = ⊤ := by
    rw [← htop]
    exact (iSup_split U (· ∈ S)).symm
  have ho : (⨆ k ∈ S, U k) ⟂ (⨆ k ∈ Sᶜ, U k) := by
    simp only [Submodule.isOrtho_iSup_left, Submodule.isOrtho_iSup_right]
    intro k hk k' hk'
    refine horth _ _ ?_
    rintro rfl
    exact absurd hk' hk
  have hv' : v ∈ (⨆ k ∈ Sᶜ, U k)ᗮ := by
    have h1 : (ℂ ∙ v) ⟂ (⨆ k ∈ Sᶜ, U k) := by
      simp only [Submodule.isOrtho_iSup_right]
      intro k hk
      exact (Submodule.span_singleton_le_iff_mem _ _).2 (hv k hk)
    exact h1 (Submodule.mem_span_singleton_self v)
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hsup.ge (Submodule.mem_top (x := v)))
  have hb' : b ∈ (⨆ k ∈ Sᶜ, U k)ᗮ := by
    have := Submodule.sub_mem _ hv' (ho ha)
    rwa [add_sub_cancel_left] at this
  have hb0 : b = 0 := inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 hb' b hb)
  rw [hb0, add_zero]
  exact ha

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem hasParamW_of_thetaOf (hL : ParamLaws N A) {i : N.Loc} (hS : SplitLift N A i)
    (hloc : LocOfPt N A i) {x : N.X i} {Sig : List (Part A.CG)} (hx : HasParamX N A i x Sig)
    {σ : what₂.FT} {P : A.AV i} (hθ : thetaOf N A i σ P) (hP : A.ptV i P = some x) :
    HasParamW N A i σ Sig := by
  obtain ⟨P', hP', h1, -, h3, h4, -⟩ := hx
  refine ⟨fun p hp => ?_, ?_, fun w hw => ?_⟩
  · have := h1 ⟨p.a, A.tw p.π A.etaTinv, p.d⟩
      (List.mem_map.mpr ⟨p, List.mem_append_left _ hp, rfl⟩)
    exact ⟨this.1, this.2.1⟩
  · have e : rankIso N A Sig + R.t = R.nV := by
      rw [← h3]
      simp [rankIso, twistIso, muPart, Function.comp_def]
    have e' : R.nV = R.r + R.t := rfl
    omega
  · have e := hloc P' P x hP' hP w hw
    rw [← h4 w hw, ParUpRoad.isoLoc_lift N A hL, hS σ P hθ w hw] at e
    exact (hL w).2.2.2.2 _ _ _ ((hL w).2.2.2.1 _ _ _ (A.locG_dim _ w) e)

theorem typeV_isOrtho_eigC {i : N.Loc} (hT : TypeOrth N A i) {x : N.X i} {P : A.AV i}
    (hP : A.ptV i P ≠ some x) : A.typeV i P ⟂ eigC N A i x := by
  unfold eigC
  simp only [Submodule.isOrtho_iSup_right]
  intro P' hP'
  refine hT P P' ?_
  rintro rfl
  exact hP hP'

theorem thetaP_mem (hθ : EachRowHasThetaLift N A) (hL : ParamLaws N A) {i : N.Loc}
    (htop : ⨆ σ, what₂.isot (N.j i) σ = ⊤) (hO : PartOrth N i) (hT : TypeOrth N A i)
    (hS : SplitLift N A i) (hloc : LocOfPt N A i) {x : N.X i} {Sig : List (Part A.CG)}
    (hx : HasParamX N A i x Sig) {F : what₂.Mt (N.mu i) (N.j i)} (hF : F ∈ eigC N A i x) :
    what₂.thetaP (N.mu i) (N.j i) F ∈ MjSig N A i Sig := by
  refine mem_biSup_of_orthogonal (what₂.isot (N.j i)) {σ | HasParamW N A i σ Sig} htop hO
    fun σ hσ => ?_
  by_cases h0 : what₂.isot (N.j i) σ = ⊥
  · rw [h0, Submodule.bot_orthogonal_eq_top]
    exact Submodule.mem_top
  obtain ⟨P, hP⟩ := hθ i σ h0
  have hne : A.ptV i P ≠ some x := fun h => hσ (hasParamW_of_thetaOf N A hL hS hloc hx hP h)
  rw [Submodule.mem_orthogonal]
  intro f hf
  rw [← LinearMap.adjoint_inner_left]
  exact (typeV_isOrtho_eigC N A hT hne).inner_eq (hP.2 ⟨f, hf, rfl⟩) hF

theorem downMem : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
    (i : N.Loc), ThetaOne N A → Rows.IsotInternal what₂ → PartOrth N i → TypeOrth N A i → ParamLaws N A →
      SplitLift N A i → LocOfPt N A i → DownMem N A i := by
  rintro R H what₂ N A i hθ hI hO hT hL hS hloc x - Sig hx _ ⟨F, hF, rfl⟩
  exact thetaP_mem N A hθ hL (hI _ (N.j_range i).1 (N.j_range i).2).submodule_iSup_eq_top hO hT hS hloc hx hF

end GlobalTheory.DownMemRoad
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowTie

theorem downMemRec_of_ties : ∀ (D : D7), GlobalTheory.RowTie.WDTie D.nd D.naut → GlobalTheory.RowCopy.ThetaOne D → Rows.IsotInternal D.what₂ → (∀ i, GlobalTheory.ThetaExh.PartOrth D.nd i) → (∀ i, GlobalTheory.ThetaExh.TypeOrth D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.PairLift D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.BCEx D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.SplitBC D.nd D.naut i) → ∀ i, GlobalTheory.RowCopy.DownMemRec D.nd D.naut i :=
  fun D T hθ hI hO hT hP hB hS i =>
    GlobalTheory.DownMemRoad.downMem _ _ _ D.nd D.naut i hθ hI (hO i) (hT i) (GlobalTheory.T.localParameterLaws_of_weilDeligneIdentification _ _ _ D.nd D.naut T).1
      (splitLift_of_pairLift _ _ _ D.nd D.naut i (hP i)) (GlobalTheory.T.splitComponentsDeterminedByPoint_of_baseChange _ _ _ D.nd D.naut i (hB i) (hS i))

end GlobalTheory.RowTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EmbeddingMapsIntoGoodExtension
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory

theorem good_conjugates_mem : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (s : ℕ),
    Loc.Good K s LL → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Loc.Om l) (x : ↥K.1), τ x ∈ LL.1 := by
  intro l _ K LL s h τ x
  unfold Loc.Good at h
  obtain ⟨-, -, hle, hall⟩ := h

  let σ := τ.liftNormal (Loc.Om l)
  have hσ : σ (algebraMap K.1 (Loc.Om l) x) = τ x := by
    rw [AlgHom.liftNormal_commutes]
    rfl
  have hx := hall ((σ : Loc.Om l →ₐ[ℚ_[l]] Loc.Om l).comp (Loc.Ks K s).val) ⟨x, hle x.2⟩
  rw [← hσ]
  exact hx

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsOfConjugatesMem
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory

theorem splits_of_conjugates_mem :
    ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l),
      (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Loc.Om l) (x : ↥K.1), τ x ∈ LL.1) →
      ∀ _ft : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1),
        Formalism.WeaklyAdmissibleFiltrations.Splits (Qp := ℚ_[l]) (K := ↥K.1) ↥LL.1 := by
  intro l _ K LL h ft
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  refine ⟨LL.2, ?_⟩
  rw [← AlgHom.card ℚ_[l] ↥K.1 (Loc.Om l), ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun σ => LL.1.val.comp σ
      invFun := fun τ => τ.codRestrict LL.1.toSubalgebra (h τ)
      left_inv := fun σ => ?_
      right_inv := fun τ => ?_ }
  · ext x; rfl
  · ext x; rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceOverPrimeOfPadicAlgClEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceOverPrimeOfPadicAlgClEmbedding
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

noncomputable section
namespace GlobalTheory.LocPlace

theorem norm_le_one_of_isIntegral' {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : @IsIntegral ℤ C _ _ (Ring.toIntAlgebra C) x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_int_le_one (l : ℕ) [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) (x : 𝓞 E) : ‖c (x : E)‖ ≤ 1 :=
  norm_le_one_of_isIntegral' (map_isIntegral_int c x.isIntegral_coe)

theorem norm_natCast_prime_lt_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
  have h : ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  rw [h, PadicAlgCl.norm_extends, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

def ballIdeal (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) : Ideal (𝓞 E) where
  carrier := {x | ‖c (x : E)‖ < 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    have e : ((a + b : 𝓞 E) : E) = (a : E) + (b : E) := by simp
    rw [e, map_add (f := _)]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  smul_mem' := by
    intro a b hb
    simp only [Set.mem_setOf_eq, smul_eq_mul] at *
    push_cast
    rw [map_mul, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (norm_int_le_one l c a)) hb

theorem mem_ballIdeal (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) (x : 𝓞 E) : x ∈ ballIdeal l E c ↔ ‖c (x : E)‖ < 1 := Iff.rfl

theorem ballIdeal_isPrime (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) : (ballIdeal l E c).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : (1 : 𝓞 E) ∈ ballIdeal l E c := h ▸ Submodule.mem_top
    rw [mem_ballIdeal] at h1
    simp at h1
  · intro a b hab
    rw [mem_ballIdeal, mem_ballIdeal] at *
    push_cast at hab
    rw [map_mul, norm_mul] at hab
    by_contra hcon
    push_neg at hcon
    have ha := le_antisymm (norm_int_le_one l c a) hcon.1
    have hb := le_antisymm (norm_int_le_one l c b) hcon.2
    rw [ha, hb] at hab
    norm_num at hab

theorem natCast_mem_ballIdeal (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) : ((l : ℕ) : 𝓞 E) ∈ ballIdeal l E c := by
  rw [mem_ballIdeal]
  push_cast
  rw [map_natCast]
  exact norm_natCast_prime_lt_one l

theorem ballIdeal_ne_bot (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) : ballIdeal l E c ≠ ⊥ := by
  intro h
  have h1 := natCast_mem_ballIdeal l E c
  rw [h, Ideal.mem_bot] at h1
  have h2 : ((l : ℕ) : E) = 0 := by exact_mod_cast congrArg (fun y : 𝓞 E => (y : E)) h1
  exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h2)

theorem exists_place_of_emb : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l), ∃ v : HeightOneSpectrum (𝓞 E), v ∈ placesOver E l ∧
      ∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c (x : E)‖ < 1 := by
  intro l _ E _ _ c
  refine ⟨⟨ballIdeal l E c, ballIdeal_isPrime l E c, ballIdeal_ne_bot l E c⟩, ?_, fun x => Iff.rfl⟩
  exact natCast_mem_ballIdeal l E c

end GlobalTheory.LocPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceOverPrimeOfPadicAlgClEmbeddingStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_place_over_prime_of_padicAlgCl_embedding : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (c : E →+* PadicAlgCl l), ∃ v : HeightOneSpectrum (𝓞 E), v ∈ placesOver E l ∧ ∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c (x : E)‖ < 1 := by
  first | exact @GlobalTheory.LocPlace.exists_place_of_emb | exact GlobalTheory.LocPlace.exists_place_of_emb | (intros; apply GlobalTheory.LocPlace.exists_place_of_emb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceExtendsToIso
namespace GlobalTheory.ThLoc

theorem place_extends_to_iso : Formalism.L2.KerInert.LamExt :=
  fun p _ lam => GlobalTheory.PadicComplexIso.exists_ringEquiv_extending p lam

end GlobalTheory.ThLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicAlgClFiniteDenseEqAdjoin
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

theorem GlobalTheory.padicAlgCl_finite_dense_eq_adjoin : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (c : E →+* PadicAlgCl l) (K : IntermediateField ℚ_[l] (PadicAlgCl l)), (∀ x, c x ∈ K) → FiniteDimensional ℚ_[l] K → (K : Set (PadicAlgCl l)) ⊆ closure (Set.range c) → K = IntermediateField.adjoin ℚ_[l] (Set.range c) := by
  intro l _ E _ _ c K hc hfin hdense
  have hle : IntermediateField.adjoin ℚ_[l] (Set.range c) ≤ K := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩; exact hc x
  have hKfin : FiniteDimensional ℚ_[l] K.toSubalgebra.toSubmodule := hfin
  have hAfin : FiniteDimensional ℚ_[l]
      (IntermediateField.adjoin ℚ_[l] (Set.range c)).toSubalgebra.toSubmodule :=
    Submodule.finiteDimensional_of_le (S₂ := K.toSubalgebra.toSubmodule) hle
  have hclosed : IsClosed ((IntermediateField.adjoin ℚ_[l] (Set.range c)).toSubalgebra.toSubmodule
      : Set (PadicAlgCl l)) :=
    Submodule.closed_of_finiteDimensional _
  apply le_antisymm _ hle
  intro y hy
  have h1 : closure (Set.range c) ⊆
      ((IntermediateField.adjoin ℚ_[l] (Set.range c)).toSubalgebra.toSubmodule : Set (PadicAlgCl l)) := by
    apply closure_minimal _ hclosed
    rintro _ ⟨x, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
  exact h1 (hdense hy)
end
