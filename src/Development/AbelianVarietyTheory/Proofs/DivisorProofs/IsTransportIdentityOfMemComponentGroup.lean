module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransporterMovesFrameReadsInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniqueUpToTargetGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormClearDenominatorsAwayFromPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportIdentityOfMemComponentGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportIdentityOfMemComponentGroup
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShareOn.OneFrame

section Geo

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD _root_.Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open scoped Matrix CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l}
variable {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r}

theorem exists_marking_match_at (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hr : 1 ≤ r)
    (hxi : ∀ k k' (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = ‖τ (U.X k').ξ0‖) :
    ∃ T : ∀ k, Dw.La →ₗ[𝓞 E] (U.X k).Λ, (∀ k, BijMod l.Mb (T k)) ∧
      ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (gM gA : Dw.La →ₗ[𝓞 E] Dw.La), IsLevMove ρ ν gM gA →
      ∀ (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ),
      FrMove ρ ν (U.un k x) y' → FrBor t (U.un k' x') y' →
      ∃ (a : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k') a) (gam : (U.X k).Λ ≃ₗ[𝓞 E] (U.X k').Λ),
        (∀ v : (U.X k).Λ, (a : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E) = (gam v : Fin r → E)) ∧
        (∀ u, gam (T k (gM u)) - T k' u ∈ l.Mb • (⊤ : Submodule (𝓞 E) (U.X k').Λ)) ∧
        ∃ b ∈ Bor (U.X k').Ψ r, x'.1 = rmul (lact a (castFr h.psi x.1)) b := by
  obtain ⟨T, hT, hmv⟩ := exists_marking_tri hU
  refine ⟨T, hT, fun ρ ν gM gA hν k k' x x' y' t hm hb => ?_⟩
  obtain ⟨gam, A, htr, hA0, hA, hmk⟩ := hmv ρ ν gM gA hν k k' x x' y' t hm hb
  obtain ⟨a, ε, hε, hξ, hav, hlat, hiso⟩ :=
    GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry E r (U.X k) (U.X k') (hxi k k') gam htr
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hrr, hty, -, -, -⟩ := hU
  have hΨ : (U.X k).Ψ = (U.X k').Ψ := Finset.ext fun τ => ((hty k).2 τ).trans ((hty k').2 τ).symm
  have hp : (U.X k).p0 = (U.X k').p0 := (hty k).1.trans (hty k').1.symm
  let e := Equiv.ofBijective _ hbij
  have he : ∀ τ, Formalism.L2.PjFree.relab c σ (e.symm τ) = τ := e.apply_symm_apply
  have m1 : ∀ τ ∈ (U.X k).Ψ, Dw.mult (e.symm τ) = r - (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_pos ((hrt _).1 (by rw [he]; exact ((hty k).2 τ).1 hτ)), (hty k).1]
    omega
  have m2 : ∀ τ ∉ (U.X k).Ψ, Dw.mult (e.symm τ) = (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_neg (fun h => hτ (((hty k).2 τ).2 (by rw [← he τ]; exact (hrt _).2 h))), (hty k).1]
  have hrel : ∀ τ, ∀ i < Dw.mult (e.symm τ), ∀ v ∈ (U.X k).Λ,
      Formalism.L2.PjFree.perFr (U.X k') x'.1 ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i =
        ∑ j ∈ Finset.range (Dw.mult (e.symm τ)), A (e.symm τ) i j * Formalism.L2.PjFree.perFr (U.X k) x.1 v τ j :=
    fun τ i hi v hv => by
      have := hA (e.symm τ) i hi ⟨v, hv⟩
      rwa [he, ← hav] at this
  rcases hε with rfl | rfl
  · have h : IsMatch (U.X k) (U.X k') a :=
      ⟨hΨ, hp, by rw [hξ, _root_.one_mul], fun u v => by rw [hiso, _root_.one_mul], hlat⟩
    obtain ⟨b, hbB, hxb, -⟩ := GlobalTheory.PeriodBorel.borel_of_periods E r _ _ a h (fun τ => Dw.mult (e.symm τ)) m1 m2
      x.1 x.2 x'.1 x'.2 (fun τ => A (e.symm τ)) (fun τ => hA0 _) hrel
    exact ⟨a, h, gam, hav, hmk, b, hbB, hxb⟩
  · exact (GlobalTheory.AntiIsom.not_antiIsometry E r _ _ hΨ hp hr a hiso (fun τ => Dw.mult (e.symm τ)) m1 m2 x.1 x.2
      x'.1 x'.2 (fun τ => A (e.symm τ)) (fun τ => hA0 _) hrel).elim

end Geo

section Frames

open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem unit_mem_Bor (Ψ : Finset (E →+* ℂ)) :
    ((fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) : Frame Ψ r) ∈ Bor Ψ r := fun τ =>
  ⟨by
    show (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
    simp, fun a c hac => by
    show (1 : Matrix (Fin r) (Fin r) ℂ) a c = 0
    exact Matrix.one_apply_ne hac.ne'⟩

theorem rmul_unit {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) :
    rmul x ((fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) : Frame Ψ r) = x := by
  funext τ
  exact Matrix.mul_one (mat x τ)

theorem eq_of_lact_eq_rmul (X : Data E r) {g a : GL (Fin r) E} (hg : g ∈ X.Γ) (ha : a ∈ X.Γ) {x b : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) (e : lact g x = rmul (lact a x) b) : g = a := by
  have h1 := X.Γ_free (a⁻¹ * g) (X.Γ.mul_mem (X.Γ.inv_mem ha) hg) x hx b hb (by
    funext τ
    have e1 : (g : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
        (a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ * mat b τ := congrFun e τ
    show ((a⁻¹ * g : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = mat x τ * mat b τ
    rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc, e1, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul])
  exact (inv_mul_eq_one.1 h1).symm

end Frames

end GlobalTheory.ShareOn.OneFrame

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_Γ_of_cong_half {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
    {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
    {Csz : ℝ} (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (i : Fin D.R.m)
    (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (k : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E)
    (ha : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k) a)
    (hcong : ∀ w ∈ lattice₂ D ((uAt r v i).X k).Λ,
      (a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ w - w ∈ p.T.Q.l.Mb • lattice₂ D ((uAt r v i).X k).Λ) :
    a ∈ ((uAt r v i).X k).Γ := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  obtain ⟨Xx, ⟨e1, e2, e3⟩, -⟩ := GlobalTheory.ModelLatticeCheck.holds_by_value D (r.used v).full.toCore
    (h.laws v).p.toLawsCore ((i : ℕ) + 1) hj (r.used v).full.σ₀ (r.used v).full.toCore.good_σ₀ k
  have eL : Xx.L' = lattice₂ D ((uAt r v i).X k).Λ := by
    rw [GlobalTheory.ModelLatExamples.eq_latP D Xx.Λ Xx.L' e3]
    show lattice₂ D Xx.toData.Λ = _
    rw [e1]
  have hGm : Xx.Gm = ((uAt r v i).X k).Gm := congrArg Data.Gm e1
  have hΛ : Xx.Λ = ((uAt r v i).X k).Λ := congrArg Data.Λ e1
  have hΓ : Xx.Γ = ((uAt r v i).X k).Γ := congrArg Data.Γ e1
  have hlatL := mem_localLattice_iff_mulVec D _ ha.lat
  have hM := sub_mem_natSMul_of_unitary Xx.Gm Xx.L' Xx.L'_int Xx.L'_dual p.T.Q.H.bar (fun a => p.T.Q.H.bar_eq a)
    p.T.Q.l.Mb p.T.Q.l.M (by have := p.T.Q.l.three_le; omega) p.T.Q.l.prod p.T.Q.l.coprime a
    (by rw [hGm]; exact ha.iso) (by rw [eL]; exact hlatL) (by rw [eL]; exact hcong)
  have hMΛ := sub_mem_natSMul_span D.host.AA Xx.L' Xx.Λ e3 _ p.T.Q.l.M hM
  have hin := Xx.cong a ⟨by rw [hGm]; exact ha.iso, by rw [hΛ]; exact ha.lat⟩ (by rw [e2]; exact hMΛ)
  rw [← hΓ]
  exact hin


open GlobalTheory.ShareOn.OneFrame in
set_option maxHeartbeats 1000000 in
theorem isTransp_one_of_mem_Γ : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (k : (uAt r v i).Comp) (γ₀ : GL (Fin D.R.r) D.host.E), γ₀ ∈ ((uAt r v i).X k).Γ → IsTransp p r i v ψ 1 k k γ₀ := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ r h _ i v ψ k γ₀ hγ₀
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hp := (h.laws v).p
  have hpin := hp.pins
  have hσ := (r.used v).full.toCore.good_σ₀
  have hpq : 1 ≤ ((r.used v).full.Q.Dw ((i : ℕ) + 1)).p + ((r.used v).full.Q.Dw ((i : ℕ) + 1)).q := by
    rw [(hpin.2.2.2 _ hj).1, (hpin.2.2.2 _ hj).2.1]
    have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
    simp only [Ranks.sigW]; omega
  have hL := GlobalTheory.FullLevelAction.actLev_levFull D (r.used v).full.Q _ hpq hpin.2.1.2
  have hU : IsUnf (uAt r v i) := hp.unf _ hj _ hσ
  have hm₀ := GlobalTheory.LevelCusp.isMatch_of_isUStab _ (((uAt r v i).X k).Γ_stab γ₀ hγ₀)
  obtain ⟨-, -, hsy, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid D.host.E _ _ _
    ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (CAt (r.used v).full.σ₀)

  have hfr : ∀ (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom),
      ∃ (hy : lact γ₀ x ∈ ((uAt r v i).X k).dom) (t : _),
        FrBor t ((uAt r v i).un k ⟨lact γ₀ x, hy⟩)
          (mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c 1 ((uAt r v i).un k ⟨x, hx⟩)) := by
    intro x hx
    have hy : lact γ₀ x ∈ ((uAt r v i).X k).dom := hm₀.mem_dom hx
    obtain ⟨t, ht⟩ := (hU.2.2.2.1 k k ⟨x, hx⟩ ⟨lact γ₀ x, hy⟩).2
      ⟨γ₀, hγ₀, _, unit_mem_Bor _, by rw [rmul_unit]⟩
    have hf := hL.func 1 _ ((uAt r v i).un k ⟨x, hx⟩) ((uAt r v i).un k ⟨x, hx⟩)
      (mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c 1 ((uAt r v i).un k ⟨x, hx⟩))
      (hL.one _ _) (Formalism.L2.Pj.mvPt_spec hL.total 1 _)
    have he : (uAt r v i).un k ⟨x, hx⟩ =
        mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c 1 ((uAt r v i).un k ⟨x, hx⟩) :=
      (GlobalTheory.LevelLawsCompare.frMap_id_iff _ _).1 hf
    exact ⟨hy, _, (congrArg (FrBor _ ((uAt r v i).un k ⟨lact γ₀ x, hy⟩)) he).mp (hsy _ _ _ ht)⟩
  refine ⟨hm₀, hfr, ?_⟩

  obtain ⟨T, hTb, hmv⟩ := exists_marking_match_at (U := Formalism.L2.PjFree.Unf.ofPj (uAt r v i)) hσ hU (hU.1 ▸ hpq)
    (fun k k' τ => (hp.xiAbs _ hj _ hσ k τ).trans (hp.xiAbs _ hj _ hσ k' τ).symm)
  have hI : p.T.Q.l.Mb ≠ ⊥ := fun e => by
    have h1 := natCast_M_mem p.T.Q.l
    rw [e, Ideal.mem_bot, Nat.cast_eq_zero] at h1
    have := p.T.Q.l.three_le
    omega
  obtain ⟨s, f, hf, hfs⟩ := exists_scale D hI D.R.r
  have hb : BijMod p.T.Q.l.Mb (f ((uAt r v i).X k).Λ ∘ₗ T k) := (hTb k).comp (hf _)
  obtain ⟨x, hx⟩ := (GlobalTheory.frames_isConnected _ _ ((uAt r v i).X k)).nonempty
  obtain ⟨hy, t, ht⟩ := hfr x hx
  obtain ⟨ρ, ν, -, hν, hm⟩ := mvPt_spec hL.total 1 ((uAt r v i).un k ⟨x, hx⟩)
  obtain ⟨a, ha, gam, hav, hmk, b, hbB, hxb⟩ := hmv ρ ν _ _ hν k k ⟨x, hx⟩ ⟨lact γ₀ x, hy⟩ _ t hm ht
  have hrd : ∀ w : lattice₂ D ((uAt r v i).X k).Λ,
      Submodule.Quotient.mk (p := p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (lattice₂ D ((uAt r v i).X k).Λ)))
        (latPMap D _ ha.lat w) = Submodule.Quotient.mk w := fun w => by
    refine (hb.reads hb 1 (liftLa 1) (liftLa_spec 1) (latPMap D _ ha.lat) (fun u => ?_) w).trans
      (hb.equiv.apply_symm_apply _)
    have h1 := map_mem_smul_top _ (f ((uAt r v i).X k).Λ) (hmk u)
    have h2 : latPMap D _ ha.lat (f ((uAt r v i).X k).Λ (T k (liftLa (l := p.T.Q.l) 1 u))) =
        f ((uAt r v i).X k).Λ (gam (T k (liftLa (l := p.T.Q.l) 1 u))) := by
      refine Subtype.ext ?_
      refine (congrArg (Matrix.mulVec _) (hfs _ _)).trans (Eq.trans ?_ (hfs _ _).symm)
      rw [Matrix.mulVec_smul]
      exact congrArg _ (hav _)
    have h3 := (f ((uAt r v i).X k).Λ).map_sub (gam (T k (liftLa (l := p.T.Q.l) 1 u))) (T k u)
    rw [← h2] at h3
    exact h3 ▸ h1
  have haΓ : a ∈ ((uAt r v i).X k).Γ := mem_Γ_of_cong_half p r h i v k a ha fun w hw => by
    have hq := (Submodule.Quotient.eq _).1 (hrd ⟨w, hw⟩)
    have hmem := Submodule.mem_map_of_mem (f := (lattice₂ D ((uAt r v i).X k).Λ).subtype) hq
    rw [Submodule.map_smul'', Submodule.map_subtype_top] at hmem
    exact hmem
  have hga : γ₀ = a := eq_of_lact_eq_rmul _ hγ₀ haΓ hx hbB hxb
  subst hga
  intro w
  exact ⟨(mem_localLattice_iff_mulVec D _ ha.lat _).1 w.2, (hrd w).trans ((ψ k).apply_symm_apply _).symm⟩

end GlobalTheory.ShareOn

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportIdentityOfMemComponentGroupStatement
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTransport_identity_of_mem_componentGroup : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (k : (uAt r v i).Comp) (γ₀ : GL (Fin D.R.r) D.host.E), γ₀ ∈ ((uAt r v i).X k).Γ → IsTransp p r i v ψ 1 k k γ₀ := by
  first | exact @GlobalTheory.ShareOn.isTransp_one_of_mem_Γ | exact GlobalTheory.ShareOn.isTransp_one_of_mem_Γ | (intros; apply GlobalTheory.ShareOn.isTransp_one_of_mem_Γ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitEqPositiveSquaresTimesSelfAdjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitEqPositiveSquaresTimesSelfAdjoint
open Matrix Polynomial

namespace GlobalTheory.Desc.SqLin

section Alg
variable {A : Type} [CommRing A] [Algebra ℚ A] [Module.Finite ℚ A]

theorem exists_casimir (τ : A →ₗ[ℚ] ℚ) (y : A) (hy : ∀ a, a ≠ 0 → 0 < τ (y * a ^ 2)) :
    ∃ (r : ℕ) (c : Fin r → ℚ) (e : Fin r → A), (∀ i, 0 < c i) ∧
      (∀ a, (∀ i, e i * a = 0) → a = 0) ∧
      ∀ a, τ (y * (∑ i, c i • e i ^ 2) * a) = LinearMap.trace ℚ A (LinearMap.mulLeft ℚ a) := by
  classical
  let β : LinearMap.BilinForm ℚ A := ((LinearMap.mul ℚ A).compr₂ (τ ∘ₗ LinearMap.mulLeft ℚ y))
  have hβ : ∀ a b, β a b = τ (y * (a * b)) := fun a b => rfl
  have hs : β.IsSymm := ⟨fun a b => by simp only [hβ, mul_comm a b, RingHom.id_apply]⟩
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (K := ℚ) (V := A) (B := β) ⟨hs.eq⟩
  have hpos : ∀ i, 0 < β (v i) (v i) := fun i => by
    rw [hβ, ← sq]; exact hy _ (v.ne_zero i)
  have hco : ∀ a i, β a (v i) = v.repr a i * β (v i) (v i) := by
    intro a i
    conv_lhs => rw [← v.sum_repr a]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      have : β (v j) (v i) = 0 := hv hj
      simp [this]
    · simp
  refine ⟨_, fun i => (β (v i) (v i))⁻¹, v, fun i => inv_pos.2 (hpos i), ?_, ?_⟩
  · intro a ha
    have : (1 : A) * a = 0 := by
      rw [← v.sum_repr 1, Finset.sum_mul]
      simp [ha]
    simpa using this
  · intro a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.trace_eq_matrix_trace ℚ v, Matrix.trace, Finset.mul_sum, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := hco (a * v i) i
    rw [hβ] at h1
    have h2 : y * (β (v i) (v i))⁻¹ • v i ^ 2 * a = (β (v i) (v i))⁻¹ • (y * (a * v i * v i)) := by
      rw [mul_smul_comm, smul_mul_assoc]; congr 1; ring
    rw [h2, map_smul, h1, smul_eq_mul, Matrix.diag_apply, LinearMap.toMatrix_apply]
    have := (hpos i).ne'
    simp only [LinearMap.mulLeft_apply]
    field_simp

theorem exists_inv (y : A) (hy : ∀ a, y * a = 0 → a = 0) : ∃ u, y * u = 1 := by
  have hinj : Function.Injective (LinearMap.mulLeft ℚ y) := by
    rw [injective_iff_map_eq_zero]; exact hy
  exact (LinearMap.injective_iff_surjective.1 hinj) 1

theorem exists_sum_sq (τ : A →ₗ[ℚ] ℚ) (h1 : ∀ a, a ≠ 0 → 0 < τ (a ^ 2)) (y : A)
    (hy : ∀ a, a ≠ 0 → 0 < τ (y * a ^ 2)) :
    ∃ (r : ℕ) (c : Fin r → ℚ) (e : Fin r → A), (∀ i, 0 < c i) ∧ y = ∑ i, c i • e i ^ 2 := by
  classical
  obtain ⟨r, c, e, hc, he, hK⟩ := exists_casimir τ y hy
  obtain ⟨s, d, f, hd, -, hL⟩ := exists_casimir τ 1 (by simpa using h1)
  have hnn : ∀ a, 0 ≤ τ (a ^ 2) := fun a => by
    by_cases h : a = 0
    · simp [h]
    · exact (h1 a h).le
  have hz : ∀ a, τ (a ^ 2) = 0 → a = 0 := fun a h => by
    by_contra h'
    exact (h1 a h').ne' h
  set K := ∑ i, c i • e i ^ 2 with hKd
  set L := ∑ i, d i • f i ^ 2 with hLd
  have hKL : y * K = L := by
    have := hK (y * K - L)
    rw [← hL, one_mul] at this
    refine sub_eq_zero.1 (hz _ ?_)
    rw [sq, sub_mul, map_sub, this, sub_self]
  obtain ⟨u, hu⟩ := exists_inv K (by
    intro a ha
    refine he a fun i => hz _ ?_
    have h0 : ∑ i, c i * τ ((e i * a) ^ 2) = 0 := by
      have : τ (K * a * a) = 0 := by rw [ha]; simp
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← this, hKd, Finset.sum_mul, Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_mul_assoc, smul_mul_assoc, map_smul, smul_eq_mul]
      congr 2; ring
    rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hc i).le (hnn _)] at h0
    exact (mul_eq_zero.1 (h0 i (Finset.mem_univ _))).resolve_left (hc i).ne')
  refine ⟨r * s, fun k => c (finProdFinEquiv.symm k).1 * d (finProdFinEquiv.symm k).2,
    fun k => e (finProdFinEquiv.symm k).1 * f (finProdFinEquiv.symm k).2 * u,
    fun k => mul_pos (hc _) (hd _), ?_⟩
  rw [Equiv.sum_comp finProdFinEquiv.symm
    (fun k : Fin r × Fin s => (c k.1 * d k.2) • (e k.1 * f k.2 * u) ^ 2), Fintype.sum_prod_type]
  have : y = K * L * u ^ 2 := by
    rw [← hKL]; linear_combination (-y * (K * u + 1)) * hu
  rw [this, hKd, hLd, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Algebra.smul_def, map_mul]
  ring

end Alg


open scoped MatrixOrder in
theorem exists_diag {n : ℕ} (T B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosDef)
    (hT : (B * T).PosDef) :
    ∃ (P Q : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ), P * Q = 1 ∧ Q * P = 1 ∧ (∀ i, 0 < d i) ∧
      T = P * diagonal d * Q := by
  obtain ⟨C, hC, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hB.isStrictlyPositive
  obtain ⟨C, rfl⟩ := hC
  have hH : (star (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ) * (star (C : Matrix (Fin n) (Fin n) ℝ) * C * T) *
      (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ)).PosDef :=
    (Matrix.IsUnit.posDef_star_left_conjugate_iff (Units.isUnit _)).2 hT
  have e : star (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ) * (star (C : Matrix (Fin n) (Fin n) ℝ) * C * T) *
      (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ) = C * T * (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ) := by
    rw [mul_assoc (star (C : Matrix (Fin n) (Fin n) ℝ)), ← mul_assoc (star _), ← star_mul,
      Units.mul_inv, star_one, one_mul]
  rw [e] at hH
  have hs := hH.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  set U := hH.1.eigenvectorUnitary
  have h1 : (U : Matrix (Fin n) (Fin n) ℝ) * star (U : Matrix (Fin n) (Fin n) ℝ) = 1 := U.2.2
  have h2 : star (U : Matrix (Fin n) (Fin n) ℝ) * (U : Matrix (Fin n) (Fin n) ℝ) = 1 := U.2.1
  refine ⟨(↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ) * U, star (U : Matrix (Fin n) (Fin n) ℝ) * C,
    hH.1.eigenvalues, ?_, ?_, hH.eigenvalues_pos, ?_⟩
  · rw [mul_assoc, ← mul_assoc (U : Matrix (Fin n) (Fin n) ℝ), h1, one_mul, Units.inv_mul]
  · rw [mul_assoc, ← mul_assoc (C : Matrix (Fin n) (Fin n) ℝ), Units.mul_inv, one_mul, h2]
  · have : T = (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ) * (C * T * (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ)) * C := by
      simp [mul_assoc]
    refine this.trans ?_
    conv_lhs => rw [hs]
    simp [mul_assoc]

theorem aeval_map_eq {n : ℕ} (T : Matrix (Fin n) (Fin n) ℚ) (P Q : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (h1 : P * Q = 1) (h2 : Q * P = 1)
    (hT : T.map (Rat.cast : ℚ → ℝ) = P * diagonal d * Q) (p : ℚ[X]) :
    (aeval T p).map (Rat.cast : ℚ → ℝ) = P * diagonal (fun k => aeval (d k) p) * Q := by
  have hm : ∀ M : Matrix (Fin n) (Fin n) ℚ,
      M.map (Rat.cast : ℚ → ℝ) = (Rat.castHom ℝ).mapMatrix M := fun M => rfl
  induction p using Polynomial.induction_on with
  | C a =>
    have : (diagonal fun _ : Fin n => (a : ℝ)) = (a : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j; by_cases h : i = j <;> simp [h, one_apply]
    simp only [aeval_C, eq_ratCast, this, Matrix.mul_smul, Matrix.smul_mul, mul_one, h1]
    ext i j; by_cases h : i = j <;> simp [h, one_apply, Matrix.algebraMap_matrix_apply]
  | add p q hp hq =>
    simp only [map_add (f := _)]
    rw [hm, map_add (f := _), ← hm, ← hm, hp, hq, ← diagonal_add, mul_add, add_mul]
  | monomial m a h =>
    rw [pow_succ, ← mul_assoc, map_mul, hm, map_mul, ← hm, ← hm, h, aeval_X, hT]
    have : ∀ D E : Matrix (Fin n) (Fin n) ℝ, P * D * Q * (P * E * Q) = P * (D * E) * Q := by
      intro D E
      calc P * D * Q * (P * E * Q) = P * D * (Q * P) * E * Q := by simp only [mul_assoc]
        _ = _ := by rw [h2]; simp only [mul_assoc, one_mul]
    rw [this, diagonal_mul_diagonal]
    simp [mul_assoc]

theorem main (n : ℕ) (Tm : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.PosDef) (hT : (B * Tm.map (Rat.cast : ℚ → ℝ)).PosDef) :
    ∃ (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ), 0 < c₀ ∧ (∀ i, 0 < c i) ∧
      (1 : Matrix (Fin n) (Fin n) ℚ) =
        c₀ • Tm + ∑ i, c i • ((Polynomial.aeval Tm (p i)) ^ 2 * Tm) := by
  classical
  obtain ⟨P, Q, d, h1, h2, hd, hD⟩ := exists_diag _ B hB hT
  have key := aeval_map_eq Tm P Q d h1 h2 hD
  let f : ℚ[X] →ₐ[ℚ] Matrix (Fin n) (Fin n) ℚ := aeval Tm
  let ι := Ideal.kerLiftAlg f
  have hι : Function.Injective ι := Ideal.kerLiftAlg_injective f
  have hιm : ∀ p, ι (Ideal.Quotient.mk _ p) = aeval Tm p := Ideal.kerLiftAlg_mk f
  haveI : Module.Finite ℚ (ℚ[X] ⧸ RingHom.ker f) := Module.Finite.of_injective ι.toLinearMap hι
  let τ : (ℚ[X] ⧸ RingHom.ker f) →ₗ[ℚ] ℚ := Matrix.traceLinearMap (Fin n) ℚ ℚ ∘ₗ ι.toLinearMap
  have hτ : ∀ p, ((τ (Ideal.Quotient.mk _ p) : ℚ) : ℝ) = ∑ k, aeval (d k) p := by
    intro p
    have : τ (Ideal.Quotient.mk _ p) = (aeval Tm p).trace := by rw [← hιm]; rfl
    have h3 : (((aeval Tm p).trace : ℚ) : ℝ) = ((aeval Tm p).map (Rat.cast : ℚ → ℝ)).trace := by
      simp [Matrix.trace]
    rw [this, h3, key, trace_mul_comm, ← mul_assoc, h2, one_mul, trace_diagonal]
  have hpos : ∀ q : ℚ[X], (∀ k, 0 < aeval (d k) q) → ∀ a : ℚ[X] ⧸ RingHom.ker f, a ≠ 0 →
      0 < τ (Ideal.Quotient.mk _ q * a ^ 2) := by
    intro q hq a ha
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [← map_pow, ← map_mul, ← Rat.cast_pos (K := ℝ), hτ]
    have : ∃ k, aeval (d k) p ≠ 0 := by
      by_contra h
      push Not at h
      apply ha
      apply hι
      rw [hιm, map_zero]
      have := key p
      simp only [h, diagonal_zero, mul_zero, zero_mul] at this
      ext i j
      simpa using congrFun (congrFun this i) j
    obtain ⟨k, hk⟩ := this
    refine Finset.sum_pos' (fun i _ => ?_) ⟨k, Finset.mem_univ _, ?_⟩
    · rw [map_mul, map_pow]; exact mul_nonneg (hq i).le (sq_nonneg _)
    · rw [map_mul, map_pow]; exact mul_pos (hq k) (by positivity)
  obtain ⟨N, hN⟩ := exists_rat_gt (∑ k, d k)
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (Finset.sum_nonneg fun i _ => (hd i).le) hN
  have hN0' : 0 < N := by exact_mod_cast hN0
  have hNk : ∀ k, d k < N := fun k =>
    lt_of_le_of_lt (Finset.single_le_sum (fun i _ => (hd i).le) (Finset.mem_univ k)) hN
  set x : ℚ[X] ⧸ RingHom.ker f := Ideal.Quotient.mk _ X with hx
  obtain ⟨u, hu⟩ := exists_inv x (by
    intro a ha
    by_contra h
    have := hpos X (by simpa using hd) a h
    rw [sq, ← mul_assoc, ← hx, ha] at this
    simp at this)
  obtain ⟨r, c, e, hc, he⟩ := exists_sum_sq τ (by simpa using hpos 1 (by simp)) _
    (hpos ((C N - X) * X) (fun k => by
      simpa using mul_pos (sub_pos.2 (hNk k)) (hd k)))
  choose p hp using fun i => Ideal.Quotient.mk_surjective (e i * u)
  refine ⟨N⁻¹, r, fun i => N⁻¹ * c i, p, inv_pos.2 hN0', fun i => mul_pos (inv_pos.2 hN0') (hc i), ?_⟩
  have hmain : (1 : ℚ[X] ⧸ RingHom.ker f) =
      N⁻¹ • x + ∑ i, (N⁻¹ * c i) • ((Ideal.Quotient.mk _ (p i)) ^ 2 * x) := by
    have e1 : ∑ i, (N⁻¹ * c i) • ((Ideal.Quotient.mk (RingHom.ker f) (p i)) ^ 2 * x) =
        N⁻¹ • ((∑ i, c i • e i ^ 2) * (u ^ 2 * x)) := by
      rw [Finset.sum_mul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hp, mul_smul, smul_mul_assoc, mul_pow, mul_assoc]
    have e2 : Ideal.Quotient.mk (RingHom.ker f) (C N) = algebraMap ℚ _ N := rfl
    rw [e1, ← he, map_mul, map_sub, e2, ← hx, ← smul_add]
    have e3 : x + (algebraMap ℚ _ N - x) * x * (u ^ 2 * x) = algebraMap ℚ _ N := by
      linear_combination ((algebraMap ℚ _ N - x) * (x * u + 1)) * hu
    rw [e3, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hN0'.ne', map_one]
  have := congrArg ι hmain
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_one, map_add (f := _), map_smul, map_sum, map_mul, map_pow, hx, hιm, aeval_X] using this

end GlobalTheory.Desc.SqLin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitEqPositiveSquaresTimesSelfAdjointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_eq_positive_squares_times_selfAdjoint : ∀ (n : ℕ) (Tm : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin n) (Fin n) ℝ), B.PosDef → (B * Tm.map (Rat.cast : ℚ → ℝ)).PosDef → ∃ (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ), 0 < c₀ ∧ (∀ i, 0 < c i) ∧ (1 : Matrix (Fin n) (Fin n) ℚ) = c₀ • Tm + ∑ i, c i • ((Polynomial.aeval Tm (p i)) ^ 2 * Tm) := by
  first | exact @GlobalTheory.Desc.SqLin.main | exact GlobalTheory.Desc.SqLin.main | (intros; apply GlobalTheory.Desc.SqLin.main <;> assumption)
end
end
