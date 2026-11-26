module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridMeasureDomainDownwardEqSender
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridMeasureDomainDownwardEqSender
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.GridMeasDown

open GlobalTheory.GridJoin GlobalTheory.Grid

variable {D : D7}

theorem exch {V₁ V₂ : HSp D} (hV : SameSp V₂ V₁) (e : GA D V₁ = GA D V₂)
    {μ₁ : Measure (GA D V₁)} {F₁ : Set (GA D V₁)} {μ₂ : Measure (GA D V₂)} {F₂ : Set (GA D V₂)}
    (hμ : HEq μ₁ μ₂) (hH₂ : μ₂.IsHaarMeasure) (h1 : IsFundamentalDomain (GQ V₁) F₁ μ₁)
    (h2 : IsFundamentalDomain (GQ V₂) F₂ μ₂) (H : GA D V₂ → ℂ) (hH : ∀ γ ∈ GQ V₂, ∀ g, H (γ * g) = H g) :
    (IntegrableOn (fun g => H (cast e g)) F₁ μ₁ ↔ IntegrableOn H F₂ μ₂) ∧
      ∫ g in F₁, H (cast e g) ∂μ₁ = ∫ g in F₂, H g ∂μ₂ := by
  obtain ⟨L, hl1, hl2, rfl⟩ := hV
  obtain rfl : μ₁ = μ₂ := eq_of_heq hμ
  exact GlobalTheory.FlipStart.Col.fund_exch (V := V₂) (μ := μ₁) h1 h2 H hH

theorem measFD_heq {V V₀ : HSp D} (hV : SameSp V₀ V) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))}
    {K₀ : Subgroup (GL (Fin V₀.rank) (Lev.EAf D))} (hK : HEq K K₀) {μ : Measure (GA D V)} {μ₀ : Measure (GA D V₀)}
    {F : Set (GA D V)} {F₀ : Set (GA D V₀)} (h : Lev.IsMeasFD V K μ F) (h₀ : Lev.IsMeasFD V₀ K₀ μ₀ F₀) : HEq μ μ₀ := by
  obtain ⟨L, hl1, hl2, rfl⟩ := hV
  obtain rfl := eq_of_heq hK
  exact heq_of_eq (GlobalTheory.FunObjModel.isMeasLevW_unique (V := V₀) (fun _ _ e => e.1) h.1 h₀.1)

theorem measDef_heq {V V₀ : HSp D} (hV : SameSp V₀ V) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))}
    {K₀ : Subgroup (GL (Fin V₀.rank) (Lev.EAf D))} (hK : HEq K K₀) {μ : Measure (GA D V)} {μ₀ : Measure (GA D V₀)}
    {F : Set (GA D V)} {F₀ : Set (GA D V₀)} (h : IsMeasDef V K μ F) (h₀ : IsMeasDef V₀ K₀ μ₀ F₀) : HEq μ μ₀ := by
  obtain ⟨L, hl1, hl2, rfl⟩ := hV
  obtain rfl := eq_of_heq hK
  have h1 : Lev.IsMeasLevDef V₀ K μ := h.1
  exact heq_of_eq (GlobalTheory.FunObjModel.isMeasLevW_unique (V := V₀) (fun _ _ e => e.1) h1 h₀.1)

theorem lev_heq {V V' : HSp D} (hsp : SameSp V V') {β : GL (Fin V'.rank) (Lev.EAf D)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hl : HEq Λ' Λ) (hf : Formalism.L2.DIV.IsFrame β Λ') :
    HEq (UA D.sp.cm V'.gram ⊓ St β) (GlobalTheory.ChiGrid.congLev D.sp.cm V.gram Λ ⊤) := by
  obtain ⟨L, hl1, hl2, rfl⟩ := hsp
  obtain rfl := eq_of_heq hl
  have hs := Formalism.L2.DIV.stabilizer_eq_stabilizer_lattice _ _ _ _ _ hf
  have h2 := GlobalTheory.ChiGrid.congLev_top (hc := D.sp.cm) (J := V.gram) (Λ := Λ')
  apply heq_of_eq
  rw [h2, hs]
  rfl

theorem cast_heq {S S' : GlobalTheory.Grid.Node D} (h : S = S') (m : S.MeasDat) :
    HEq (Node.MeasDat.cast h m).ν m.ν ∧ HEq (Node.MeasDat.cast h m).fd m.fd := by
  subst h; exact ⟨HEq.rfl, HEq.rfl⟩

theorem cast_fd {S S' : GlobalTheory.Grid.Node D} (h : S = S') (m : S.MeasDat) (hf : IsFundamentalDomain (GQ S.V) m.fd m.ν) :
    IsFundamentalDomain (GQ S'.V) (Node.MeasDat.cast h m).fd (Node.MeasDat.cast h m).ν := by
  subst h; exact hf

theorem meas_down : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} {large₂ : SizeData₂ D}
    {F : Face D A}, GlobalTheory.RowClaim.HidaSetting large₂ R F → sc.cGap = 1 →
    ∀ {G' : GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.Is → GlobalTheory.GridJoin.Match G W →
    ∀ (M : Vol G') (t : T), M.Is t → ∀ (i j : ℕ), i ≤ D.R.m → j < D.R.m →
    ∀ (e : GA D (G.V i (j + 1)).V = GA D (G'.V (.grid i (j + 1)))) (H : GA D (G'.V (.grid i (j + 1))) → ℂ),
    (∀ γ ∈ GQ (G'.V (.grid i (j + 1))), ∀ g, H (γ * g) = H g) →
    (IntegrableOn (fun g => H (cast e g)) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν ↔
      IntegrableOn H (M.fd (.grid i (j + 1))) (M.ν (.grid i (j + 1)))) ∧
    ∫ g in (G.meas t i (j + 1)).fd, H (cast e g) ∂(G.meas t i (j + 1)).ν =
      ∫ g in M.fd (.grid i (j + 1)), H g ∂(M.ν (.grid i (j + 1))) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc large₂ F hS hc G' W hW G hG hJ M t hM i j hi hj e H hH
  have hAt := hM.vtx (.grid i (j + 1)) ⟨hi, by omega⟩
  obtain ⟨hHaar, hfd⟩ := hAt.haar_fund
  have hsp : SameSp (G'.V (.grid i (j + 1))) (G.V i (j + 1)).V := (hJ.1.vert i (j + 1) hi (by omega)).sp
  suffices key : HEq (G.meas t i (j + 1)).ν (M.ν (.grid i (j + 1))) ∧
      IsFundamentalDomain (GQ (G.V i (j + 1)).V) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν from
    exch hsp e key.1 hHaar key.2 hfd H hH
  unfold Vol.IsAt at hAt
  rcases i with _ | i
  · have hmod := hS.core.models
    by_cases h : j + 1 < D.R.m
    · have hT : G'.V (.grid 0 (j + 1)) = Yc D (j + 1) := congrArg LSp.sp (colY_lt R.toLevCh h)
      have hK : HEq (levJ G' t (.grid 0 (j + 1)))
          (lev D.sp.cm (Yc D (j + 1)).gram (R.βY (j + 1)) (R.datYt t (j + 1) R.triv)) := levCol_lt R.toLevCh t h
      have e0 : G.meas t 0 (j + 1) = Node.MeasDat.cast (nodeY_eq_chainVertexAtRowZero_of_lt R h) ⟨R.νY t (j + 1), R.fdY t (j + 1)⟩ := by
        show meas0 R t j = _
        rw [meas0, dite_eq_left h]
      rw [e0]
      rcases Nat.lt_or_ge (j + 1 + 1) D.R.m with h' | h'
      · have hc := hmod.νY t (j + 1) h'
        rw [if_neg (show ¬ (GlobalTheory.ChiGrid.Node.grid 0 (j + 1)).neg D.R.m = 0 by simp only [GlobalTheory.ChiGrid.Node.neg]; omega)] at hAt
        exact ⟨(cast_heq _ _).1.trans (GlobalTheory.FlipStart.Col.measFD_heq hT hK hAt hc).symm, cast_fd _ _ hc.2⟩
      · have e1 : j + 1 = D.R.m - 1 := by omega
        have hc := hmod.νY' t
        rw [← e1] at hc
        rw [if_pos (show (GlobalTheory.ChiGrid.Node.grid 0 (j + 1)).neg D.R.m = 0 by simp only [GlobalTheory.ChiGrid.Node.neg]; omega)] at hAt
        exact ⟨(cast_heq _ _).1.trans (GlobalTheory.FlipStart.Col.measDef_heq hT hK hAt hc).symm, cast_fd _ _ hc.2⟩
    · have hj' : j + 1 = D.R.m := by omega
      have hT : G'.V (.grid 0 (j + 1)) = D.sp.X' := by
        show (columnBlock R.toLevCh (j + 1)).sp = _
        rw [hj', colY_m]
      have hK : HEq (levJ G' t (.grid 0 (j + 1))) (lev D.sp.cm D.sp.X'.gram R.βX (R.datXt t)) := levCol_top R.toLevCh t h
      have e0 : G.meas t 0 (j + 1) = Node.MeasDat.cast (nodeX_eq_chainVertexAtRowZero_of_ge R h) ⟨R.νX t, R.fdX t⟩ := by
        show meas0 R t j = _
        rw [meas0, dite_eq_right h]
      rw [e0]
      have hc := hmod.νX t
      rw [if_pos (show (GlobalTheory.ChiGrid.Node.grid 0 (j + 1)).neg D.R.m = 0 by simp only [GlobalTheory.ChiGrid.Node.neg]; omega)] at hAt
      exact ⟨(cast_heq _ _).1.trans (GlobalTheory.FlipStart.Col.measDef_heq hT hK hAt hc).symm, cast_fd _ _ hc.2⟩
  · have hN := hJ.1.vert (i + 1) (j + 1) hi (by omega)
    have hm := hG.meas.vert i j hi (by omega)
    obtain ⟨c, hfr⟩ := (hG.spaces.vert i (j + 1) hi (by omega)).frame
    have hK : HEq ((G.nV i (j + 1)).princ ⊤) (levJ G' t (.grid (i + 1) (j + 1))) := by
      rw [GlobalTheory.Grid.Node.princ_top]
      exact lev_heq hN.sp hN.lat hfr.1
    show HEq (G.mV i (j + 1)).ν _ ∧ IsFundamentalDomain (GQ (G.nV i (j + 1)).V) (G.mV i (j + 1)).fd (G.mV i (j + 1)).ν
    by_cases hd : D.R.m - 1 ≤ j + 1
    · have h1 := hm.1 hd
      rw [if_pos (show (GlobalTheory.ChiGrid.Node.grid (i + 1) (j + 1)).neg D.R.m = 0 by simp only [GlobalTheory.ChiGrid.Node.neg]; omega)] at hAt
      exact ⟨measDef_heq hN.sp hK h1 hAt, h1.2⟩
    · have h1 := hm.2 hd
      rw [if_neg (show ¬ (GlobalTheory.ChiGrid.Node.grid (i + 1) (j + 1)).neg D.R.m = 0 by simp only [GlobalTheory.ChiGrid.Node.neg]; omega)] at hAt
      exact ⟨measFD_heq hN.sp hK h1 hAt, h1.2⟩

end GlobalTheory.GridMeasDown
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridMeasureDomainDownwardEqSenderStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.testGrid_measure_domain_downward_eq_sender : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} {large₂ : SizeData₂ D}
    {F : Face D A}, GlobalTheory.RowClaim.HidaSetting large₂ R F → sc.cGap = 1 →
    ∀ {G' : GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.Is → GlobalTheory.GridJoin.Match G W →
    ∀ (M : Vol G') (t : T), M.Is t → ∀ (i j : ℕ), i ≤ D.R.m → j < D.R.m →
    ∀ (e : GA D (G.V i (j + 1)).V = GA D (G'.V (.grid i (j + 1)))) (H : GA D (G'.V (.grid i (j + 1))) → ℂ),
    (∀ γ ∈ GQ (G'.V (.grid i (j + 1))), ∀ g, H (γ * g) = H g) →
    (IntegrableOn (fun g => H (cast e g)) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν ↔
      IntegrableOn H (M.fd (.grid i (j + 1))) (M.ν (.grid i (j + 1)))) ∧
    ∫ g in (G.meas t i (j + 1)).fd, H (cast e g) ∂(G.meas t i (j + 1)).ν =
      ∫ g in M.fd (.grid i (j + 1)), H g ∂(M.ν (.grid i (j + 1))) := by
  first | exact @GlobalTheory.GridMeasDown.meas_down | exact GlobalTheory.GridMeasDown.meas_down | (intros; apply GlobalTheory.GridMeasDown.meas_down <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspTypedTestGridIffSenderGridConj
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspTypedTestGridIffSenderGridConj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ListedTypeConj

open Matrix GlobalTheory.ConjDS GlobalTheory.ConjMult Formalism.IndefR.Mult

variable {D : D7}

theorem isUnit_det_gramAt (V : HSp D) (τ : D.what₂.Tau) : IsUnit (gramAt D V τ).det := by
  refine isUnit_iff_ne_zero.2 ?_
  rw [gramAt, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V)

theorem isTypeAt_star {θ : InfFam D} {V : HSp D} {τ : D.what₂.Tau} {S : SPar} {φ : GA D V → ℂ}
    (h : IsTypeAt θ V τ S φ) : IsTypeAt θ V τ (dualPar S) fun g => star (φ g) := by
  obtain ⟨H, i1, i2, σ, lam, ε, P, hE, hD, hP, hG, hx⟩ := h
  have hJ := isUnit_det_gramAt V τ
  have key : ∀ g, rv (P.submatrix Fin.revPerm (Equiv.refl _) * g * (P.submatrix Fin.revPerm (Equiv.refl _))⁻¹) =
      P * g * P⁻¹ := fun g => by
    rw [inv_submatrix_equiv]
    have : P.submatrix Fin.revPerm (Equiv.refl _) * g * P⁻¹.submatrix (Equiv.refl _) Fin.revPerm = rv (P * g * P⁻¹) := by
      ext i j
      simp [rv, Matrix.mul_apply]
    rw [this, rv_rv]
  refine ⟨Cj H, inferInstance, inferInstance, fun g => cjOp (σ (rv g)), nr lam, fun a => ε a.rev,
    P.submatrix Fin.revPerm (Equiv.refl _), isEnum_dual hE, isDS_transfer (fun _ => rfl) (cj H) (fun _ _ => rfl) hD,
    (Matrix.isUnit_submatrix_equiv _ _).2 hP, ?_, ?_⟩
  · rw [← hG, ← rv_Jm (ε := fun a => ε a.rev) (ε' := ε) (fun a => by simp), rv, conjTranspose_submatrix,
      submatrix_mul_equiv, submatrix_mul_equiv]
    rfl
  simp only [key]
  intro x
  obtain ⟨v, hv, ℓ, hℓ, ⟨S0, C, hS0, hC, hsum, B, hB, hBb⟩, hhas⟩ := hx x
  have hc1 : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, (cj H) (cjOp (σ (P * g * P⁻¹)) w) = σ (P * g * P⁻¹) ((cj H) w) :=
    fun _ _ _ => rfl
  have hc2 : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w,
      (cj H).symm (σ (P * g * P⁻¹) w) = cjOp (σ (P * g * P⁻¹)) ((cj H).symm w) := fun _ _ _ => rfl
  have hfold : ∀ l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ X ∈ l, X ∈ lieAt V τ) → ∀ w,
      l.foldr (dRep fun g => σ (P * g * P⁻¹)) (cj H w) = cj H (l.foldr (dRep fun g => cjOp (σ (P * g * P⁻¹))) w) := by
    intro l
    induction l with
    | nil => intro _ _; rfl
    | cons X l ih =>
      intro hl w
      rw [List.foldr_cons, ih (fun Y hY => hl Y (List.mem_cons_of_mem _ hY)),
        dRep_conj hJ (cj H) hc1 (hl X List.mem_cons_self), List.foldr_cons]
  have hnorm : ∀ l : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ)), (∀ m ∈ l, ∀ X ∈ m, X ∈ lieAt V τ) → ∀ w,
      (l.map fun m => ‖m.foldr (dRep fun g => cjOp (σ (P * g * P⁻¹))) w‖) =
        l.map fun m => ‖m.foldr (dRep fun g => σ (P * g * P⁻¹)) (cj H w)‖ :=
    fun l hl w => List.map_congr_left fun m hm => by rw [hfold m (hl m hm), (cj H).norm_map]
  choose ℓ' hℓ' hℓv using fun i => sobCont_conj hJ (cj H) hc1 (hℓ i)
  refine ⟨fun i => (cj H).symm (v i), fun i => smoothVec_conj hJ (cj H).symm hc2 (hv i), ℓ', hℓ',
    ⟨S0, C, hS0, fun i w hw => ?_, fun S' hS' => ?_, B, hB, fun g hg w hw => ?_⟩, fun g hg => ?_⟩
  · rw [hℓv, norm_star, hnorm S0 hS0]
    exact hC i _ (smoothVec_conj hJ (cj H) hc1 hw)
  · convert hsum S' hS' using 3 with i
    rw [hnorm S' hS']
    rfl
  · rw [hnorm S0 hS0, hnorm S0 hS0]
    exact hBb g hg _ (smoothVec_conj hJ (cj H) hc1 hw)
  · simp only [hℓv]
    exact (hhas g hg).star

end GlobalTheory.ListedTypeConj

noncomputable section

namespace GlobalTheory.ListedTypeConj

open Matrix Formalism.IndefR.Mult

variable {D : D7}

theorem isTypeAt_star_iff {θ : InfFam D} {V : HSp D} {τ : D.what₂.Tau} {S : SPar} {φ : GA D V → ℂ} :
    IsTypeAt θ V τ S (fun g => star (φ g)) ↔ IsTypeAt θ V τ (dualPar S) φ := by
  constructor
  · intro h
    simpa using isTypeAt_star h
  · intro h
    simpa [dualPar_dualPar] using isTypeAt_star h

theorem listed_iff_of_sameSp {θ : InfFam D} {V V' : HSp D} (h : GlobalTheory.GridJoin.SameSp V V') (e : GA D V' = GA D V)
    (P : D.what₂.Tau → SPar) (φ : GA D V → ℂ) :
    (IsAutFunSm θ V φ ∧ IsCuspFun V φ ∧ ∀ τ, IsTypeAt θ V τ (P τ) fun g => star (φ g)) ↔
      (IsAutFunSm θ V' (fun g => φ (cast e g)) ∧ IsCuspFun V' (fun g => φ (cast e g)) ∧
        ∀ τ, IsTypeAt θ V' τ (dualPar (P τ)) fun g => φ (cast e g)) := by
  obtain ⟨L, h1, h2, rfl⟩ := h
  have hφ : (fun g => φ (cast e g)) = φ := funext fun g => rfl
  rw [hφ]
  simp only [isTypeAt_star_iff]
  refine and_congr ⟨fun h => ⟨⟨h.left, h.level, h.cont⟩, h.smooth, h.zfin, h.growth⟩,
    fun h => ⟨⟨h.left, h.level, h.cont⟩, h.smooth, h.zfin, h.growth⟩⟩ (and_congr Iff.rfl Iff.rfl)

theorem grid_eq_num (D : D7) (τ : D.what₂.Tau) : GlobalTheory.Grid.grid D τ = GlobalTheory.ChiGrid.num D 1 τ := by
  have hg := GlobalTheory.GridJoin.gap_eq_chiGap D
  have hc : GlobalTheory.Grid.cen D τ = GlobalTheory.ChiGrid.cen D 1 τ := by
    funext i
    unfold GlobalTheory.Grid.cen GlobalTheory.ChiGrid.cen GlobalTheory.Grid.gridOf
    rw [hg]
    rfl
  unfold GlobalTheory.Grid.grid GlobalTheory.Grid.gridOf GlobalTheory.ChiGrid.num
  rw [hc, hg]
  rfl

theorem parV_eq (D : D7) (i j : ℕ) (τ : D.what₂.Tau) :
    GlobalTheory.Grid.parV D i j τ = dualPar (GlobalTheory.ChiGrid.parV D 1 i j τ) := by
  rw [GlobalTheory.Grid.parV, GlobalTheory.ChiGrid.parV, grid_eq_num]

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem nodeS_eq {R : RealDat D A Ks} {G : GlobalTheory.Grid.GridPre R} (hG : G.Is) {i j : ℕ} (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) :
    (G.V i j).S = GlobalTheory.Grid.parV D i j := by
  cases i with
  | zero =>
    rw [GlobalTheory.Grid.parV_zero D hj]
    cases j with
    | zero => simp [GlobalTheory.Grid.GridPre.V, GlobalTheory.Grid.row0, GlobalTheory.Grid.nodeY]
    | succ j =>
      by_cases h : j + 1 < D.R.m
      · simp [GlobalTheory.Grid.GridPre.V, GlobalTheory.Grid.row0, GlobalTheory.Grid.nodeY, h, min_eq_left h.le]
      · have e : j + 1 = D.R.m := by omega
        simp only [GlobalTheory.Grid.GridPre.V, GlobalTheory.Grid.GridSp.vert, GlobalTheory.Grid.row0, if_neg h]
        rw [e]
  | succ i => exact (hG.spaces.vert i j (by omega) hj).par

end GlobalTheory.ListedTypeConj

namespace GlobalTheory.ListedTypeConj

open Formalism.IndefR.Mult

theorem isCuspListed_grid_iff : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} {large₂ : SizeData₂ D}
    {F : Face D A}, GlobalTheory.RowClaim.HidaSetting large₂ R F → sc.cGap = 1 →
    ∀ {G' : GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.Is → GlobalTheory.GridJoin.Match G W →
    ∀ (i j : ℕ), i ≤ D.R.m → j ≤ D.R.m → ∀ (e : GA D (G.V i j).V = GA D (G'.V (.grid i j))) (φ : GA D (G'.V (.grid i j)) → ℂ),
      IsCuspListed W.θ (.grid i j) φ ↔ GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) (fun g => φ (cast e g)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc large₂ F _ hc G' W hW G hG hM i j hi hj e φ
  have hθ : W.θ = R.θ := hW.θ
  have hS : (G.V i j).S = fun τ => dualPar (GlobalTheory.ChiGrid.Node.par D sc.cGap (.grid i j) τ) := by
    rw [nodeS_eq hG hi hj, hc]
    funext τ
    exact parV_eq D i j τ
  have hsp := (hM.1.vert i j hi hj).sp
  unfold IsCuspListed GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType
  simp only [GridData.IsListed]
  rw [hθ, hS]
  revert e
  generalize (G.V i j).V = V' at hsp ⊢
  intro e
  exact listed_iff_of_sameSp hsp e _ φ

end GlobalTheory.ListedTypeConj
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspTypedTestGridIffSenderGridConjStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspTyped_testGrid_iff_sender_grid_conj : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} {large₂ : SizeData₂ D}
    {F : Face D A}, GlobalTheory.RowClaim.HidaSetting large₂ R F → sc.cGap = 1 →
    ∀ {G' : GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.Is → GlobalTheory.GridJoin.Match G W →
    ∀ (i j : ℕ), i ≤ D.R.m → j ≤ D.R.m → ∀ (e : GA D (G.V i j).V = GA D (G'.V (.grid i j))) (φ : GA D (G'.V (.grid i j)) → ℂ),
      IsCuspListed W.θ (.grid i j) φ ↔ GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) (fun g => φ (cast e g)) := by
  first | exact @GlobalTheory.ListedTypeConj.isCuspListed_grid_iff | exact GlobalTheory.ListedTypeConj.isCuspListed_grid_iff | (intros; apply GlobalTheory.ListedTypeConj.isCuspListed_grid_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelDownwardTestGridEqSenderGrid
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelDownwardTestGridEqSenderGrid
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipDown

theorem kernel_down : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}
    {G' : GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.Is → GlobalTheory.GridJoin.Match G W →
    ∀ (t : T) (i j : ℕ), i ≤ D.R.m → j < D.R.m →
    ∀ (eA : GA D (G.V i (j + 1)).V = GA D (G'.V (.grid i (j + 1)))) (eB : GA D (G.V i j).V = GA D (G'.V (.grid i j)))
    (Ψ : WO (G'.pS (.mu t i j)) (G'.pT (.mu t i j)) → ℂ), IsThetaFunO W.ψ (G'.pS (.mu t i j)) (G'.pT (.mu t i j)) Ψ →
    ∃ Φ : WO (G.V i j).V (G.V i (j + 1)).V → ℂ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ ∧
      ∀ h g, thetaKO (G.th t i j).ω h g Φ = W.kerA (.down t i j) Ψ (cast eA g) (cast eB h) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc G' W hW G hG hM t i j hi hj eA eB Ψ hΨ
  obtain ⟨L1, a1, b1, e1⟩ := (hM.1.vert i j hi (by omega)).sp
  obtain ⟨L2, a2, b2, e2⟩ := (hM.1.vert i (j + 1) hi (by omega)).sp
  have hω := hM.2.omT t i j hi hj
  revert eA eB hω
  generalize (G.th t i j).ω = ω
  revert ω
  generalize (G.V i j).V = S at e1 ⊢
  generalize (G.V i (j + 1)).V = U at e2 ⊢
  subst e1 e2
  intro ω eA eB hω
  have hω' : ω = W.om (.mu t i j) := eq_of_heq hω
  subst hω'
  refine ⟨Ψ, ?_, fun h g => rfl⟩
  rw [← hW.ψ]
  exact ⟨hΨ.1, hΨ.2, hΨ.3, hΨ.4⟩

end GlobalTheory.FlipDown
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelDownwardTestGridEqSenderGridStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_downward_testGrid_eq_sender_grid : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}
    {G' : GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.Is → GlobalTheory.GridJoin.Match G W →
    ∀ (t : T) (i j : ℕ), i ≤ D.R.m → j < D.R.m →
    ∀ (eA : GA D (G.V i (j + 1)).V = GA D (G'.V (.grid i (j + 1)))) (eB : GA D (G.V i j).V = GA D (G'.V (.grid i j)))
    (Ψ : WO (G'.pS (.mu t i j)) (G'.pT (.mu t i j)) → ℂ), IsThetaFunO W.ψ (G'.pS (.mu t i j)) (G'.pT (.mu t i j)) Ψ →
    ∃ Φ : WO (G.V i j).V (G.V i (j + 1)).V → ℂ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ ∧
      ∀ h g, thetaKO (G.th t i j).ω h g Φ = W.kerA (.down t i j) Ψ (cast eA g) (cast eB h) := by
  first | exact @GlobalTheory.FlipDown.kernel_down | exact GlobalTheory.FlipDown.kernel_down | (intros; apply GlobalTheory.FlipDown.kernel_down <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelDownwardArrowLeftInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelDownwardArrowLeftInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.DownKer

theorem kerA_down_left_inv : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T) (i j : ℕ),
    i ≤ D.R.m → j < D.R.m → ∀ Ψ : WO (G.pS (.mu t i j)) (G.pT (.mu t i j)) → ℂ,
    IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) Ψ → ∀ h : GA D (G.V (.grid i j)),
    ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g, W.kerA (.down t i j) Ψ (γ * g) h = W.kerA (.down t i j) Ψ g h := by
  intro D T L sc G W t i j hi hj Ψ hΨ h γ hγ g
  have hR : (Pair.mu t i j : Pair T).InRange D.R.m := ⟨hi, hj⟩
  have hw := W.om_is (.mu t i j) hR
  show (W.om (.mu t i j)) (h, γ * g) Ψ 0 = (W.om (.mu t i j)) (h, g) Ψ 0
  have e : ((h, γ * g) : GA D (G.pS (.mu t i j)) × GA D (G.pT (.mu t i j))) = (1, γ) * (h, g) := by
    simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hw.om_aut 1 (one_mem _) γ hγ _ (hw.om_pres _ _ hΨ)

end GlobalTheory.DownKer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelDownwardArrowLeftInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_downward_arrow_left_invariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T) (i j : ℕ),
    i ≤ D.R.m → j < D.R.m → ∀ Ψ : WO (G.pS (.mu t i j)) (G.pT (.mu t i j)) → ℂ,
    IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) Ψ → ∀ h : GA D (G.V (.grid i j)),
    ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g, W.kerA (.down t i j) Ψ (γ * g) h = W.kerA (.down t i j) Ψ g h := by
  first | exact @GlobalTheory.DownKer.kerA_down_left_inv | exact GlobalTheory.DownKer.kerA_down_left_inv | (intros; apply GlobalTheory.DownKer.kerA_down_left_inv <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipRun

theorem ga_eq_of_match {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}
    {G' : GridData R.toLevCh sc} {W : G'.Weil} {G : GlobalTheory.Grid.GridPre R} (hM : GlobalTheory.GridJoin.Match G W) {i j : ℕ}
    (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) : GA D (G.V i j).V = GA D (G'.V (.grid i j)) := by
  obtain ⟨L, h1, h2, e⟩ := (hM.1.vert i j hi hj).sp
  rw [e]; rfl

end GlobalTheory.FlipRun
