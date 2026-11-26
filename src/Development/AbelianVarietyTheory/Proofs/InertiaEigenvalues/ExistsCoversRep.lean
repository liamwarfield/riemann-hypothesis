module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFirstOfSecond
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceAdjointMatrixIsCoordinateEquivariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceThetaLatticeHalvesSelfDualFrames

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoversRep
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneCover

open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV GlobalTheory.TupleCover

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem exists_fun_cover {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {n r : ℕ} (d : DeltaDat Xo c n) (V : HSp D) (hr : V.rank = r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hio : IotaOK Dw V ι) (hpos : 1 ≤ Dw.p + Dw.q)
    (hx₀ : ∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 →
      gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) =
        Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ))
    (hA : d.l₂.A = 1) :
    ∃ (U₂ : Unf d.Xo₂ d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) r) (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r),
      IsUnf U₂ ∧ (∀ k, ModelW V hr (U₂.X k)) ∧
      ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
        (F : FamilyUnif d.Xo₂ (((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)).comp
            (IntermediateField.inclusion d.c₂.le).toRingHom)
          (fun j => relab d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) (e j).1))
        (ik : U₂.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U₂.X k).Λ)
        (th : ∀ k, (U₂.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
        (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictLat U₂ V hr dict₂ ι e F ik φ th x₀ ∧
        ∀ (_ : d.IsLev) (_ : FnAlgClosed (Xo := d.Xo₂) (c := d.c₂)) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
          (_ : ∀ g : GA D V, (∃ w ∈ intAE D, ((Matrix.GeneralLinearGroup.det (finHom V g) :
            (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = d.l₂.M • w) →
            xi (Matrix.GeneralLinearGroup.det (finHom V g)) = 1)
          (_ : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1)
          (m : ℕ) (_ : 0 < m) (_ : ∀ g : GA D V, xi (Matrix.GeneralLinearGroup.det (finHom V g)) ^ m = 1)
          (_ : zeta m ∈ c.F),
          ∃ f : Rul d.Xo₂ d.c₂, ({ d with cδ := f } : DeltaDat Xo c n).IsLev ∧ f ^ m = 1 ∧
            ∀ h γ : GA D V, MarkBy U₂ V hr dict₂ ι F ik φ h γ →
              rdU U₂ f (dict₂ h).1 (dict₂ h).2 =
                1 * ((xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) : ℂ) := by
  have hσ : d.c₂.F.val.toRingHom = (inC c).comp (d.eF.symm : d.c₂.F →+* c.F) := RingHom.ext fun _ => rfl
  have hg₂ : GoodEmb d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) := by
    rw [← hσ]; rfl
  obtain ⟨C, hC, hCι, hCx⟩ := (exists_ctx D H Dw d.l₂ d.Xo₂ d.c₂ _ V r hr ι hio hpos hA hg₂).2.2 x₀ hx₀
  obtain ⟨Kf, hKf⟩ := (PrincLevel.exists_levelK_and_nhds D V d.l₂.M).1
  obtain ⟨un, dict, mu, -, -, hP⟩ := exists_pkgLaws D _ _ _ _ _ _ _ _ C hC Kf hKf 1 ⟨continuous_const, fun _ => rfl⟩
    (fun _ => rfl)
  obtain ⟨g, e, F, ik, φ, th, hth, hdu, hdl⟩ := hP.dictLaws
  refine ⟨C.unf un, dict, hP.unf, hP.modelW, g, e, F, ik, φ, th, hth, ?_, ?_⟩
  · rw [← hCι, ← hCx]
    exact hdl
  intro hlev hcl xi h1 h2 m hm h3 hz
  obtain ⟨f, hf, hfm, -, hfx⟩ := GlobalTheory.XiFun.exists_sec_char_val D _ _ _ _ _ _ _ _ C.hr (C.unf un) dict C.ι g e F ik φ th C.x₀
    hC.iota hpos hA hg₂ hP.modelW hdl hdu.2.2.2.1 hcl xi
    (fun u _ hu => h1 u (by rw [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]; exact hu)) h2
    (fun h => ⟨⟨_, d.hF.symm ▸ GlobalTheory.NormOneChar.mem_of_pow_eq_one hm hz (by
      rw [← Units.val_pow_eq_pow_val, h3 h, Units.val_one])⟩, rfl⟩)
  have hfm' : f ^ m = 1 := hfm m h3
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, -, l9⟩ := hlev
  refine ⟨f, ⟨l1, l2, l3, l4, l5, l6, l7, hf, fun k _ _ _ y => ?_⟩, hfm', fun h γ hmk => ?_⟩
  · exact GlobalTheory.XiFun.evR_ne_zero_of_pow _ _ f d.cδ m hm hfm' k y (l9 k y)
  · rw [one_mul]
    rw [← hCι] at hmk
    exact hfx h γ hmk

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem halfIs_of_eq {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {t t' : T0}
    (e : R.Q t' = R.Q t) {Mb I : Ideal (𝓞 D.host.E)} (h : HalfIs R t' Mb I) : HalfIs R t Mb I := by
  unfold HalfIs at h ⊢
  rwa [e] at h

theorem xi_pow_eq_one (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (h : ChrEq c χ) (n : ℕ)
    (ho : χ.OrderDvd n) (x : (AE D)ˣ) : c x ^ n = 1 :=
  GlobalTheory.T.heckeChar_eq_one_of_trivial_finitePartOne D (c ^ n) ⟨h.1.1.pow n, fun x => by
    rw [MonoidHom.pow_apply, h.1.2, one_pow]⟩ (GlobalTheory.T.idelicCharacter_pow_eq_one_finiteIdeles_of_orderDvd D c χ h n ho) x

def CoversRep (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (n : ℕ)
    (pd : T0 → ℕ) (I : T0 → Ideal (𝓞 D.host.E)) (l₂ : T0 → Level T.Q.H) (rep : T0 → T0) (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F) : Prop :=
  ∃ (d : T0 → DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n)
    (U : ∀ t, Unf (d t).Xo₂ (d t).c₂ ((inC c').comp ((d t).eF.symm : (d t).c₂.F →+* c'.F)) D.R.r)
    (dict : ∀ t, GA D (Wc D i) → Σ k, Frame ((U t).X k).Ψ D.R.r)
    (f : ∀ t, Rul (d (rep t)).Xo₂ (d (rep t)).c₂)
    (xi : T0 → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ),
    (∀ t, (d t).pd = pd t ∧ (d t).I = I t ∧ (d t).l₂ = l₂ t) ∧
    CovPin (T.Q.Xo ((i : ℕ) + 1)) c' (fun t => ({ d (rep t) with cδ := f t } : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n)) ∧
    (∀ t, HalfIs R t T.Q.l.Mb (d (rep t)).I) ∧
    (∀ t, XiIs R i t (xi t)) ∧
    CXiVal (Wc D i) (rank_Wc i) (inC c') (fun t => ({ d (rep t) with cδ := f t } : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n))
      (fun t => U (rep t)) (fun t => dict (rep t)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) (sOv T.toCore c' hle)) xi ∧
    (∀ t k, ModelW (Wc D i) (rank_Wc i) ((U (rep t)).X k))


set_option maxHeartbeats 2000000 in
theorem exists_covers_rep (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) {μ0 : T0} [Finite T0]
    (hT : LawsJ T) (hL : R.toLevCh.Is μ0) (i : Fin D.R.m) (n : ℕ)
    (pd : T0 → ℕ) (I : T0 → Ideal (𝓞 D.host.E)) (l₂ : T0 → Level T.Q.H)
    (hl : ∀ t, IsCoverLevel T.Q.l (pd t) (I t) (l₂ t)) (hH : ∀ t, HalfIs R t T.Q.l.Mb (I t))
    (rep : T0 → T0) (hrep : ∀ t, R.Q (rep t) = R.Q t) :
    ∃ c₁ : Coeff T.Q.l, T.Q.c.F ≤ c₁.F ∧ D.what₂.embLL.toRatAlgHom.fieldRange ≤ c₁.F ∧
      (∀ t x, ((R.xi t x : Circle) : ℂ) ∈ c₁.F) ∧
      ∀ (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F), c₁.F ≤ c'.F → CoversRep T R i n pd I l₂ rep c' hle := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hpq := (exists_iotaOK D T.Q hT.pins _ hj).2
  have hpos : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by omega
  have hX : ∀ t, ∃ (Xo₂ : Moduli (T.Q.Dw ((i : ℕ) + 1)) (l₂ t)) (c₀ : Coeff (l₂ t)),
      ∀ c'' : Coeff (l₂ t), c₀.F ≤ c''.F → FnAlgClosed (Xo := Xo₂) (c := c'') := fun t => by
    obtain ⟨Xo₂⟩ := GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.1 _ _ (T.Q.Dw ((i : ℕ) + 1)) (l₂ t) hpos
    obtain ⟨c₀, -⟩ := exists_coeff_ge (l₂ t) ⊥
    obtain ⟨c₁, -, h⟩ := (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ _ _ Xo₂ c₀ hpos).2
    exact ⟨Xo₂, c₁, h⟩
  choose Xo₂ c₀ hc₀ using hX
  choose m hm ho using hL.xi_fin
  choose xi hx1 hx2 hx3 hx4 using fun t =>
    exists_xi D (Wc D i) (R.xi t) (R.xiH t) (hL.xi t) (m t) (hm t) (ho t) (hL.xi_triv t) (hL.xi_tame t)
  have := T.Q.c.fin
  have : ∀ t, FiniteDimensional ℚ (c₀ t).F := fun t => (c₀ t).fin
  have : ∀ t, FiniteDimensional ℚ (IntermediateField.adjoin ℚ {zeta (m t)}) := fun t =>
    IntermediateField.adjoin.finiteDimensional
      ((Complex.isPrimitiveRoot_exp (m t) (hm t).ne').isIntegral (hm t)).tower_top
  have : FiniteDimensional ℚ D.what₂.embLL.toRatAlgHom.fieldRange :=
    LinearEquiv.finiteDimensional (D.what₂.embLL.toRatAlgHom.equivFieldRange).toLinearEquiv
  obtain ⟨c₁, hc₁⟩ := exists_coeff_ge T.Q.l ((T.Q.c.F ⊔ D.what₂.embLL.toRatAlgHom.fieldRange) ⊔
    ⨆ t, ((c₀ t).F ⊔ IntermediateField.adjoin ℚ {zeta (m t)}))
  have hsup₁ : ∀ t, (c₀ t).F ⊔ IntermediateField.adjoin ℚ {zeta (m t)} ≤ c₁.F := fun t =>
    ((le_iSup (fun t => (c₀ t).F ⊔ IntermediateField.adjoin ℚ {zeta (m t)}) t).trans le_sup_right).trans hc₁
  refine ⟨c₁, (le_sup_left.trans le_sup_left).trans hc₁, (le_sup_right.trans le_sup_left).trans hc₁, fun t x => ?_, fun c' hle hc' => ?_⟩
  · refine GlobalTheory.NormOneChar.mem_of_pow_eq_one (hm t) (hsup₁ t (le_sup_right (a := (c₀ t).F) (IntermediateField.mem_adjoin_simple_self ℚ _))) ?_
    rw [← Circle.coe_pow, xi_pow_eq_one D (R.xi t) (R.xiH t) (hL.xi t) (m t) (ho t) x]
    rfl
  have hsup : ∀ t, (c₀ t).F ⊔ IntermediateField.adjoin ℚ {zeta (m t)} ≤ c'.F := fun t => (hsup₁ t).trans hc'
  have hσ : GoodEmb T.Q.c (sOv T.toCore c' hle) := rfl
  obtain ⟨hio, hx₀⟩ := iotaOK_and_frame T hT _ hj _ hσ (Wc D i) (hT.spaceW _ hj _ hσ) (rank_Wc i)
  have key := fun t => by
    obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hl t
    have h0 : (c₀ t).F ≤ c'.F := le_sup_left.trans (hsup t)
    let c₂ : Coeff (l₂ t) := ⟨c'.F, c'.fin, c'.conj, h0 (c₀ t).zeta_mem, (c₀ t).le.trans h0⟩
    have hd := GlobalTheory.LevelCover.exists_deltaDat_isLev _ _ _ _ (T.Q.Xo ((i : ℕ) + 1)) c' hpos n (pd t) (I t) (l₂ t) (Xo₂ t) c₂ rfl
      l1 l2 l3 l4 l5
    have hd' : ∃ d : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n, d.pd = pd t ∧ d.I = I t ∧ d.l₂ = l₂ t ∧ d.IsLev ∧ d.l₂.A = 1 ∧
        FnAlgClosed (Xo := d.Xo₂) (c := d.c₂) ∧ ∃ _ : StarRing (𝓞 D.host.E), IsNab d.Xo₂ d.c₂ d.nab₂ := by
      obtain ⟨⟨pd', I', l₂', Xo₂', c₂', hF, r, mm, nab, cδ, φ₀⟩, a1, a2, a3, e₁, e₂, -, a4, a5⟩ := hd
      refine ⟨_, a1, a2, a3, a4, a3 ▸ l6, ?_, a5⟩
      dsimp only at a3 e₁ e₂ ⊢
      subst a3
      obtain rfl := eq_of_heq e₁
      obtain rfl := eq_of_heq e₂
      exact hc₀ t c₂ h0
    exact hd'
  choose d a1 a2 a3 a4 a5 a6 a7 using key
  have hM : ∀ t, ∀ PP ∈ R.Q t, (((d (rep t)).l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun t PP hPP => by
    refine (hH (rep t)).2.1 PP (by rw [hrep]; exact hPP) ?_
    have h1 : (((d (rep t)).l₂.M : ℕ) : 𝓞 D.host.E) ∈ (d (rep t)).l₂.Mb :=
      Ideal.mul_le_left ((d (rep t)).l₂.prod.ge (Ideal.mem_span_singleton_self _))
    rw [(a4 (rep t)).2.2.2.1, a2] at h1
    exact Ideal.mul_le_right h1
  choose U dict b3 using fun t => exists_fun_cover (d t) (Wc D i) (rank_Wc i) (iotaW T i) _ hio hpos hx₀ (a5 t)
  have b4 : ∀ t, ∃ f : Rul (d (rep t)).Xo₂ (d (rep t)).c₂,
      ({ d (rep t) with cδ := f } : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n).IsLev ∧ f ^ m t = 1 ∧
      IsUnf (U (rep t)) ∧ (∀ k, ModelW (Wc D i) (rank_Wc i) ((U (rep t)).X k)) ∧
      ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw ((i : ℕ) + 1)).mult τ))
        (F : FamilyUnif (d (rep t)).Xo₂ (((inC c').comp ((d (rep t)).eF.symm : (d (rep t)).c₂.F →+* c'.F)).comp
            (IntermediateField.inclusion (d (rep t)).c₂.le).toRingHom)
          (fun j => relab (d (rep t)).c₂ ((inC c').comp ((d (rep t)).eF.symm : (d (rep t)).c₂.F →+* c'.F)) (e j).1))
        (ik : (U (rep t)).Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] ((U (rep t)).X k).Λ)
        (th : ∀ k, ((U (rep t)).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
        (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
        DictLat (U (rep t)) (Wc D i) (rank_Wc i) (dict (rep t)) (iotaW T i) e F ik φ th (T.x₀ ((i : ℕ) + 1) (sOv T.toCore c' hle)) ∧
        ∀ h γ : GA D (Wc D i), MarkBy (U (rep t)) (Wc D i) (rank_Wc i) (dict (rep t)) (iotaW T i) F ik φ h γ →
          rdU (U (rep t)) f (dict (rep t) h).1 (dict (rep t) h).2 =
            1 * ((xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) (γ * h))) : ℂˣ) : ℂ) := fun t => by
    obtain ⟨u1, u2, g, e, F, ik, φ, th, v1, v2, v3⟩ := b3 (rep t)
    obtain ⟨f, f1, f2, f3⟩ := v3 (a4 (rep t)) (a6 (rep t)) (xi t)
      (hx2 t _ (d (rep t)).l₂.odd (unrAt_of_not_mem R hL t _ (hM t))) (hx3 t) (m t) (hm t) (hx4 t)
      (hsup t (le_sup_right (a := (c₀ t).F) (IntermediateField.mem_adjoin_simple_self ℚ _)))
    exact ⟨f, f1, f2, u1, u2, g, e, F, ik, φ, th, v1, v2, f3⟩
  choose f b1 b2 b5 using b4
  refine ⟨d, U, dict, f, xi, fun t => ⟨a1 t, a2 t, a3 t⟩, fun t => ⟨b1 t, a5 (rep t), a7 (rep t)⟩,
    fun t => ?_, hx1, ⟨1, ⟨1, one_pos, one_pow 1⟩, b5⟩, fun t => (b5 t).2.1⟩
  rw [a2]
  exact halfIs_of_eq R (hrep t) (hH (rep t))

end GlobalTheory.OneCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLevelAndSchrodingerBoundedSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLevelAndSchrodingerBoundedSupport
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit.SupportBound

open GlobalTheory.SplitScalar

variable {D : D7}

theorem exists_pow_le {v : FinPl D} {ϖ : OI v} (hϖ : Irreducible ϖ) {c d : Fv D.host.F v} (hc : c ≠ 0) (hd : d ≠ 0) :
    ∃ N : ℕ, Valued.v (algebraMap (OI v) (Fv D.host.F v) (ϖ ^ N)) ≤ Valued.v c ∧
      Valued.v (algebraMap (OI v) (Fv D.host.F v) (ϖ ^ N)) ≤ Valued.v d := by
  have h1 : Valued.v (algebraMap (OI v) (Fv D.host.F v) ϖ) < 1 := by
    refine lt_of_le_of_ne ϖ.2 fun h => hϖ.not_isUnit ?_
    exact HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 h
  have h2 : min (Valued.v c) (Valued.v d) ≠ 0 := by
    rcases min_choice (Valued.v c) (Valued.v d) with h | h <;> rw [h]
    · exact (Valuation.ne_zero_iff _).2 hc
    · exact (Valuation.ne_zero_iff _).2 hd
  obtain ⟨N, hN⟩ := exists_pow_lt₀ h1 (Units.mk0 _ h2)
  refine ⟨N, ?_, ?_⟩ <;> rw [map_pow, map_pow]
  · exact hN.le.trans (min_le_left _ _)
  · exact hN.le.trans (min_le_right _ _)

theorem rdQ_ne_zero {v : FinPl D} (φ : SplitProj D v) {x : D.host.E} (hx : x ≠ 0) : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ x ≠ 0 := by
  have h : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ x * GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ x⁻¹ = 1 := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hx]
    exact map_one φ
  exact left_ne_zero_of_mul_eq_one h

theorem map_nsmul_of_add {A B : Type} [AddGroup A] [AddGroup B] {κ : A → B} (h : ∀ x y, κ (x + y) = κ x + κ y) (k : ℕ)
    (x : A) : κ (k • x) = k • κ x :=
  map_nsmul (AddMonoidHom.mk' κ h) k x

theorem symplO_nsmul (S T : HSp D) (k : ℕ) (x y : WO S T) : symplO S T (k • x) y = symplO S T x (k • y) := by
  rw [← Nat.cast_smul_eq_nsmul (AE D), symplO_smul, map_natCast, Nat.cast_smul_eq_nsmul]

theorem level_and_support : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (ϖ : OI v), Irreducible ϖ → ∀ f, IsThetaFunO ψ S T f → ∃ N : ℕ, (∀ z ∈ halfPow φ S T (frCo φ βS) (frCo φ βT) e ϖ N, heisO ψ S T z f = f) ∧ ∀ ℓ, InvForm ψ S T e ℓ → ∀ x, IsHalf (cA D e) x → ℓ (heisO ψ S T x f) ≠ 0 → Bdd ϖ N (adjCo φ S T (frCo φ βS) (frCo φ βT) x) := by
  intro D ψ hψ S T ΛS ΛT βS βT hS hT hfS hfT v φ e he ϖ hϖ f hf
  obtain ⟨U, hU, hUf⟩ := hf.level
  obtain ⟨k, hk, hkU⟩ := (GlobalTheory.LatLevel.level_of_generators D S T _ _ hS hT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T _ _ hS hT)).1 U hU
  obtain ⟨hd, -, -⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  obtain ⟨-, a, -, ha0, -, himg⟩ := GlobalTheory.SplitLatticeHalves.splitLattice D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he
  obtain ⟨⟨hadd, hbij, -⟩, -⟩ := GlobalTheory.PlaceTensor.adjCo_isCoord D S T ΛS ΛT hS hT v φ e he (frCo φ βS) (frCo φ βT)
  have hst := @idem_smul_mem D S T ΛS ΛT _ he.1.1
  have he' := isSplitIdem_conj he.1
  have hb := rdQ_ne_zero φ (star_ne_zero.2 ha0)
  generalize GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a) = b at hb himg
  generalize (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) = Λ at *
  haveI : CharZero (Fv D.host.F v) := algebraRat.charZero _
  have hk0 : (k : Fv D.host.F v) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hkv : Valued.v (k : Fv D.host.F v) ≠ 0 := (Valuation.ne_zero_iff _).2 hk0
  obtain ⟨N, hN1, hN2⟩ := exists_pow_le hϖ (mul_ne_zero hk0 hb) (mul_ne_zero hk0 (inv_ne_zero hb))
  refine ⟨N, fun z hz => ?_, fun ℓ hℓ x hx hne i j => ?_⟩
  · have hy : (k : Fv D.host.F v)⁻¹ • adjCo φ S T (frCo φ βS) (frCo φ βT) z ∈
        {y : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) | ∀ i j, Valued.v (y i j) ≤ Valued.v b} := by
      intro i j
      obtain ⟨o, ho⟩ := hz.2 i j
      rw [Matrix.smul_apply, ho, smul_eq_mul, map_mul, map_mul, map_mul, map_inv₀, inv_mul_le_iff₀ (zero_lt_iff.2 hkv),
        ← Valuation.map_mul _ (k : Fv D.host.F v)]
      exact (mul_le_of_le_one_right' o.2).trans hN1
    rw [← himg] at hy
    obtain ⟨t, ⟨ht, hth⟩, hty⟩ := hy
    have : z = k • t := by
      refine hbij.injOn hz.1 (isHalf_nsmul hth k) ?_
      rw [map_nsmul_of_add hadd, hty, ← Nat.cast_smul_eq_nsmul (Fv D.host.F v), smul_smul, mul_inv_cancel₀ hk0, one_smul]
    exact hUf z (this ▸ hkU t ht) (half_fin he' hz.1)
  · have hkx : k • x ∈ Λ := by
      by_contra hn
      obtain ⟨l, hl, hlh, hl1⟩ := exists_dual_half he' hd (by rw [GlobalTheory.DualPairCheck.cA_cA]; exact hst)
        (isHalf_nsmul hx k) hn
      rw [GlobalTheory.DualPairCheck.cA_cA] at hlh
      have hlk := isHalf_nsmul hlh k
      have h2 := hℓ _ hlk _ (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (half_fin he' hx) hf)
      rw [heisO_comm, hUf _ (hkU l hl) (half_fin he.1 hlk), map_smul, smul_eq_mul, symplO_nsmul] at h2
      exact hl1 (mul_right_cancel₀ hne (h2.trans (one_mul _).symm))
    have hy : adjCo φ S T (frCo φ βS) (frCo φ βT) (k • x) ∈
        {y : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) | ∀ i j, Valued.v (y i j) ≤ Valued.v b} := by
      rw [← himg]
      exact ⟨_, ⟨hkx, isHalf_nsmul hx k⟩, rfl⟩
    have h3 := hy i j
    rw [map_nsmul_of_add hadd, Matrix.smul_apply, nsmul_eq_mul] at h3
    refine ⟨⟨algebraMap (OI v) (Fv D.host.F v) (ϖ ^ N) * adjCo φ S T (frCo φ βS) (frCo φ βT) x i j, ?_⟩, rfl⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul]
    refine (mul_le_mul_left hN2 _).trans ?_
    rw [← Valuation.map_mul, mul_right_comm, Valuation.map_mul, map_inv₀]
    exact mul_inv_le_one_of_le₀ h3 zero_le'

end GlobalTheory.DownLift.GenSplit.SupportBound

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLevelAndSchrodingerBoundedSupportStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_level_and_schrodinger_bounded_support : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (ϖ : OI v), Irreducible ϖ → ∀ f, IsThetaFunO ψ S T f → ∃ N : ℕ, (∀ z ∈ halfPow φ S T (frCo φ βS) (frCo φ βT) e ϖ N, heisO ψ S T z f = f) ∧ ∀ ℓ, InvForm ψ S T e ℓ → ∀ x, IsHalf (cA D e) x → ℓ (heisO ψ S T x f) ≠ 0 → Bdd ϖ N (adjCo φ S T (frCo φ βS) (frCo φ βT) x) := by
  first | exact @GlobalTheory.DownLift.GenSplit.SupportBound.level_and_support | exact GlobalTheory.DownLift.GenSplit.SupportBound.level_and_support | (intros; apply GlobalTheory.DownLift.GenSplit.SupportBound.level_and_support <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeparatingCharacterConjugateHalfSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeparatingCharacterConjugateHalfSplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit.DualSep

variable {D : D7}

theorem algebraMap_OI {v : FinPl D} (o : OI v) : algebraMap (OI v) (Fv D.host.F v) o = (o : Fv D.host.F v) := rfl

theorem mem_pow_iff {v : FinPl D} (ϖ : OI v) (hϖ : (ϖ : Fv D.host.F v) ≠ 0) (N : ℕ) (x : Fv D.host.F v) :
    (∃ o : OI v, x = algebraMap (OI v) (Fv D.host.F v) (ϖ ^ N * o)) ↔
      Valued.v x ≤ Valued.v (ϖ : Fv D.host.F v) ^ N := by
  constructor
  · rintro ⟨o, rfl⟩
    rw [algebraMap_OI, Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow]
    have ho : Valued.v (o : Fv D.host.F v) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 o.2
    calc Valued.v (ϖ : Fv D.host.F v) ^ N * Valued.v (o : Fv D.host.F v)
        ≤ Valued.v (ϖ : Fv D.host.F v) ^ N * 1 := by gcongr
      _ = _ := mul_one _
  · intro h
    have hp : (ϖ : Fv D.host.F v) ^ N ≠ 0 := pow_ne_zero _ hϖ
    have hv : 0 < Valued.v ((ϖ : Fv D.host.F v) ^ N) := by
      rw [zero_lt_iff]; exact (map_ne_zero _).2 hp
    have hmem : x / (ϖ : Fv D.host.F v) ^ N ∈ v.adicCompletionIntegers D.host.F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, div_le_one₀ hv, map_pow]
      exact h
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [algebraMap_OI, Subring.coe_mul, SubmonoidClass.coe_pow]
    show x = (ϖ : Fv D.host.F v) ^ N * (x / (ϖ : Fv D.host.F v) ^ N)
    rw [mul_div_cancel₀ _ hp]

theorem adjCo_smul {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) (s : AE D) (z : WO S T) :
    adjCo φ S T BS BT (cA D s • z) = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ s • adjCo φ S T BS BT z := by
  have h1 : ((cA D s • z : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D) =
      s • (z : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D) := by
    ext i j
    simp [GlobalTheory.DualPairCheck.cA_cA]
  have h2 : ∀ (M : Matrix (Fin S.rank) (Fin T.rank) (AE D)),
      (s • M).map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ s • M.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) := by
    intro M; ext i j; simp
  unfold adjCo
  rw [h1, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, h2, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.DownLift.GenSplit.DualSep

namespace GlobalTheory.DownLift.GenSplit


open DualSep in
theorem exists_sep_char : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (ϖ : OI v), Irreducible ϖ → ∀ (N : ℕ) (x : WO S T), IsHalf (cA D e) x → ¬ InPow ϖ N (adjCo φ S T (frCo φ βS) (frCo φ βT) x) → ∃ y, IsHalf e y ∧ (∀ z ∈ halfPow φ S T (frCo φ βS) (frCo φ βT) e ϖ N, ψ (symplO S T z y) = 1) ∧ ψ (symplO S T x y) ≠ 1 := by
  intro D ψ hψ S T ΛS ΛT βS βT hS hT hfS hfT v φ e he ϖ hϖ N x hx hxN
  obtain ⟨a, -, ha0, -, himg⟩ := (GlobalTheory.SplitLatticeHalves.splitLattice D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he).2
  have hα : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a) ≠ 0 := by
    rw [← GlobalTheory.SplitProjChart.emb_apply]
    exact (map_ne_zero _).2 (star_ne_zero.2 ha0)
  have hϖ0 : (ϖ : Fv D.host.F v) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hp : (ϖ : Fv D.host.F v) ^ N ≠ 0 := pow_ne_zero _ hϖ0
  set c : Fv D.host.F v := GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a) / (ϖ : Fv D.host.F v) ^ N with hcdef
  have hc : c ≠ 0 := div_ne_zero hα hp
  obtain ⟨s, hs⟩ := (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1.1 c
  have hcoef : ∀ z : WO S T, adjCo φ S T (frCo φ βS) (frCo φ βT) (cA D s • z) =
      c • adjCo φ S T (frCo φ βS) (frCo φ βT) z := fun z => by rw [adjCo_smul, hs]
  have hval : ∀ m : Fv D.host.F v, Valued.v (c * m) ≤ Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a)) ↔
      Valued.v m ≤ Valued.v (ϖ : Fv D.host.F v) ^ N := by
    intro m
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a) = c * (ϖ : Fv D.host.F v) ^ N := by
      rw [hcdef, div_mul_cancel₀ _ hp]
    rw [e1, map_mul, map_mul, map_pow, mul_le_mul_iff_right₀ (zero_lt_iff.2 ((map_ne_zero _).2 hc))]
  have hinPow : ∀ z : WO S T, InPow ϖ N (adjCo φ S T (frCo φ βS) (frCo φ βT) z) ↔
      ∀ i j, Valued.v ((c • adjCo φ S T (frCo φ βS) (frCo φ βT) z) i j) ≤
        Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a)) := by
    intro z
    unfold InPow
    simp only [Matrix.smul_apply, smul_eq_mul, hval, mem_pow_iff ϖ hϖ0 N]
  have hhalf : ∀ z : WO S T, IsHalf (cA D e) z → IsHalf (cA D e) (cA D s • z) := by
    intro z hz
    rw [GlobalTheory.SplitScalar.isHalf_iff] at *
    rw [smul_comm, hz]
  have hcoord := (GlobalTheory.PlaceTensor.adjCo_isCoord D S T ΛS ΛT hS hT v φ e he (frCo φ βS) (frCo φ βT)).1
  have hmem : ∀ z : WO S T, IsHalf (cA D e) z → InPow ϖ N (adjCo φ S T (frCo φ βS) (frCo φ βT) z) →
      cA D s • z ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    intro z hz hzN
    have h1 : adjCo φ S T (frCo φ βS) (frCo φ βT) (cA D s • z) ∈ adjCo φ S T (frCo φ βS) (frCo φ βT) ''
        {t | t ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ∧
          IsHalf (cA D e) t} := by
      rw [himg, hcoef]
      exact (hinPow z).1 hzN
    obtain ⟨t, ⟨htΛ, htH⟩, hteq⟩ := h1
    have h2 : t = cA D s • z := hcoord.2.1.injOn htH (hhalf z hz) hteq
    rw [← h2]
    exact htΛ
  have hnot : cA D s • x ∉
      latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    intro hmx
    apply hxN
    rw [hinPow]
    have h1 : adjCo φ S T (frCo φ βS) (frCo φ βT) (cA D s • x) ∈
        {y : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) | ∀ i j, Valued.v (y i j) ≤
          Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a))} := by
      rw [← himg]
      exact ⟨_, ⟨hmx, hhalf x hx⟩, rfl⟩
    rw [hcoef] at h1
    exact h1
  have hsd := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1
  have hse := GlobalTheory.SplitScalar.isSplitIdem_conj he.1
  obtain ⟨l, hlΛ, hlH, hne⟩ := GlobalTheory.SplitScalar.exists_dual_half hse hsd
    (fun u hu => by rw [GlobalTheory.DualPairCheck.cA_cA]; exact GlobalTheory.SplitScalar.idem_smul_mem he.1.1 u hu) (hhalf x hx) hnot
  rw [GlobalTheory.DualPairCheck.cA_cA] at hlH
  refine ⟨s • l, ?_, fun z hz => ?_, ?_⟩
  · rw [GlobalTheory.SplitScalar.isHalf_iff] at *
    rw [smul_comm, hlH]
  · obtain ⟨hz1, hz2⟩ := hz
    have h1 := (hsd _ (GlobalTheory.SplitScalar.half_fin hse (hhalf z hz1))).1 (hmem z hz1 hz2) l hlΛ
    rwa [GlobalTheory.SplitScalar.symplO_smul, GlobalTheory.DualPairCheck.cA_cA] at h1
  · have h1 := GlobalTheory.SplitScalar.psi_skew_ne hne
    rwa [GlobalTheory.SplitScalar.symplO_smul, GlobalTheory.DualPairCheck.cA_cA] at h1

end GlobalTheory.DownLift.GenSplit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeparatingCharacterConjugateHalfSplitStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_separating_character_conjugate_half_split : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (ϖ : OI v), Irreducible ϖ → ∀ (N : ℕ) (x : WO S T), IsHalf (cA D e) x → ¬ InPow ϖ N (adjCo φ S T (frCo φ βS) (frCo φ βT) x) → ∃ y, IsHalf e y ∧ (∀ z ∈ halfPow φ S T (frCo φ βS) (frCo φ βT) e ϖ N, ψ (symplO S T z y) = 1) ∧ ψ (symplO S T x y) ≠ 1 := by
  first | exact @GlobalTheory.DownLift.GenSplit.exists_sep_char | exact GlobalTheory.DownLift.GenSplit.exists_sep_char | (intros; apply GlobalTheory.DownLift.GenSplit.exists_sep_char <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchrodingerFunctionInvariantTypePrime
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchrodingerFunctionInvariantTypePrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

namespace GlobalTheory.DownLift.GenSplit

theorem actO_sigma_of_grpCo : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (σ : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v) → WO (Vc D i) (Wc D i)), (∀ X, IsHalf (cA D e) (σ X) ∧ coR R i φ (σ X) = X) → ∀ (κ : GA D (Vc D i)) (h : GL (Fin D.R.r ⊕ Fin D.R.t) (OI v)) (h' : GL (Fin (Vc D i).rank) (OI v)), (∀ a b, (h' : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (OI v)) (rowIx (rank_V i) a) (rowIx (rank_V i) b) = (h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)) a b) → grpCo φ (Vc D i) (frCo φ (R.βV i)) κ = Matrix.GeneralLinearGroup.map (algebraMap (OI v) (Fv D.host.F v)) h' → ∀ X : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v), actO (Vc D i) (Wc D i) κ 1 (σ X) = σ ((h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)).map (algebraMap (OI v) (Fv D.host.F v)) * X) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL i v φ e he σ hσ κ h h' hh' hgrp X
  have sdV := GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βV i)
  have sdW := GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βW i)
  have hco := (GlobalTheory.PlaceTensor.adjCo_isCoord D (Vc D i) (Wc D i) _ _ sdV sdW v φ e he
    (frCo φ (R.βV i)) (frCo φ (R.βW i))).1
  have hinj := hco.2.1.injOn
  have h1 : IsHalf (cA D e) (actO (Vc D i) (Wc D i) κ 1 (σ X)) := GlobalTheory.SplitHecke.isHalf_actO κ 1 (hσ X).1
  have h2 : IsHalf (cA D e) (σ ((h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)).map (algebraMap (OI v) (Fv D.host.F v)) * X)) := (hσ _).1
  refine hinj h1 h2 ?_
  have ha : adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) (actO (Vc D i) (Wc D i) κ 1 (σ X)) =
      (grpCo φ (Vc D i) (frCo φ (R.βV i)) κ).val * adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) (σ X) := by
    have := GlobalTheory.PlaceTensor.AdjCoord.adjCo_actO φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) κ⁻¹ 1 (σ X)
    rw [inv_inv, inv_one, GlobalTheory.PlaceTensor.AdjCoord.grpCo_inv, inv_inv] at this
    rw [this]
    have g1 : grpCo φ (Wc D i) (frCo φ (R.βW i)) 1 = 1 := by
      unfold grpCo; rw [map_one, map_one, mul_one, inv_mul_cancel]
    rw [g1, Units.val_one, Matrix.mul_one]
  have hc : ∀ x, coR R i φ x = (adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) x).submatrix (rowIx (rank_V i)) (finCongr (rank_weight_component_eq i)) := fun x => rfl
  have hX : coR R i φ (actO (Vc D i) (Wc D i) κ 1 (σ X)) = coR R i φ (σ ((h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)).map (algebraMap (OI v) (Fv D.host.F v)) * X)) := by
    rw [(hσ _).2, hc, ha, hgrp, ← Matrix.submatrix_mul_equiv _ _ _ (rowIx (rank_V i)), ← hc, (hσ X).2]
    congr 1
    ext a b
    simp [Matrix.GeneralLinearGroup.map, hh']
  refine Matrix.ext fun a b => ?_
  have e1 := congrFun (congrFun hX ((rowIx (rank_V i)).symm a)) ((finCongr (rank_weight_component_eq i)).symm b)
  simpa [hc] using e1

theorem levG_levChi_of_red : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (t : T) (PP : Pl D.host.E), PP ∈ R.Pg → ∀ (κ : GA D (Vc D i)), κ ∈ GfC (Vc D i) → finE (Vc D i) κ ∈ St (R.βV i) → ∀ (g : GL (Fin (Vc D i).rank) (kP PP)), redFn (R.βV i) PP (finE (Vc D i) κ) = g → (∀ PP', PP' ∈ R.Pg ∨ PP' ∈ R.Q t → PP' ≠ PP → redFn (R.βV i) PP' (finE (Vc D i) κ) = 1) → (∀ a b : Fin D.R.r, (g : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (kP PP)) (rowIx (rank_V i) (Sum.inl a)) (rowIx (rank_V i) (Sum.inl b)) = (1 : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)) a b) → (∀ (a : Fin D.R.t) (b : Fin D.R.r), (g : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (kP PP)) (rowIx (rank_V i) (Sum.inr a)) (rowIx (rank_V i) (Sum.inl b)) = 0) → κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t) ∧ levChi (Vc D i) (R.βV i) (R.datVt i t) κ = ((R.chi ((i : ℕ) + 1) PP (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL i t PP hPP κ hGf hSt g hg hoth hg1 hg2
  have rV : (Vc D i).rank = D.R.r + D.R.t := (rank_V i).symm
  have hdisj : PP ∉ R.Q t := Finset.disjoint_left.1 (Formalism.IndefR.Fin.disjoint_Pg_Q R.toLevCh hL t) hPP
  have hlo : ∀ a : Fin (Vc D i).rank, (ha : a.val < D.R.r) → a = rowIx (rank_V i) (Sum.inl ⟨a.val, ha⟩) := by
    intro a ha; ext; simp [rowIx]
  have hhi : ∀ a : Fin (Vc D i).rank, (ha : D.R.r ≤ a.val) →
      a = rowIx (rank_V i) (Sum.inr ⟨a.val - D.R.r, by have := a.2; omega⟩) := by
    intro a ha; ext; simp [rowIx]; omega
  have htri : g ∈ blockTri (blkOf D.R.r D.R.t) := by
    intro a b hab
    have ha : D.R.r ≤ a.val := by
      by_contra h; push_neg at h
      simp [blkOf, h] at hab
    have hb : b.val < D.R.r := by
      by_contra h; push_neg at h
      have h1 := a.2; have h2 := b.2
      have e1 : (a.val - D.R.r) / D.R.t = 0 := Nat.div_eq_of_lt (by omega)
      have e2 : (b.val - D.R.r) / D.R.t = 0 := Nat.div_eq_of_lt (by omega)
      simp [blkOf, not_lt.2 ha, not_lt.2 h, e1, e2] at hab
    rw [hhi a ha, hlo b hb]
    exact hg2 _ _
  have hr1 : upperLeftBlock (r_le_V i) g = 1 := by
    apply Units.ext
    rw [upper_block_val_submatrix _ (blockTri_blkOf_le _ _ htri), Units.val_one]
    refine Matrix.ext fun a b => ?_
    simp only [Matrix.submatrix_apply]
    have ea : Fin.castLE (r_le_V i) a = rowIx (rank_V i) (Sum.inl a) := by ext; simp [rowIx]
    have eb : Fin.castLE (r_le_V i) b = rowIx (rank_V i) (Sum.inl b) := by ext; simp [rowIx]
    rw [ea, eb, hg1]
  have hred : ∀ PP', PP' ∈ R.Pg ∨ PP' ∈ R.Q t → redFn (R.βV i) PP' (finE (Vc D i) κ) = 1 ∨ PP' = PP := by
    intro PP' h
    by_cases e : PP' = PP
    · exact Or.inr e
    · exact Or.inl (hoth PP' h e)
  have hrT : rTup (R.βV i) (R.datVt i t) (finE (Vc D i) κ) = 1 := by
    funext PP'
    show upperLeftBlock (r_le_V i) (redFn (R.βV i) PP'.1 (finE (Vc D i) κ)) = 1
    rcases hred PP'.1 (Or.inl PP'.2) with h | h
    · rw [h]; exact blockDiagonalExtendByOnePrimeField_one _ _
    · rw [h, hg, hr1]
  have hpar : finE (Vc D i) κ ∈ parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := by
    refine mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hSt, fun PP' hP' => ?_, fun PP' hP' => ?_⟩
    · rcases hred PP' (Or.inl hP') with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h, hg]; exact htri
    · rcases hred PP' (Or.inr hP') with h | h
      · rw [h]; exact Subgroup.one_mem _
      · exact absurd (h ▸ hP') hdisj
  refine ⟨⟨hGf, hpar, ?_⟩, ?_⟩
  · show rTup (R.βV i) (R.datVt i t) (finE (Vc D i) κ) ∈ (R.datVt i t).P.H
    rw [hrT]; exact Subgroup.one_mem _
  · have hQ : ∏ PP' ∈ (R.datVt i t).Q, (R.datVt i t).xq PP' (dBlk (blk2 (R.datVt i t).r) 1 (redFn (R.βV i) PP' (finE (Vc D i) κ))) = 1 := by
      refine Finset.prod_eq_one fun PP' hP' => ?_
      rcases hred PP' (Or.inr hP') with h | h
      · rw [h, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
      · exact absurd (h ▸ hP') hdisj
    have hdet : Matrix.GeneralLinearGroup.det g = dBlk (blkOf D.R.r D.R.t) 1 g := by
      rw [(GlobalTheory.T.det_twoDiagBlocks_properties _ _ _ D.R.t (r_le_V i) g).1 (blockTri_blkOf_le _ _ htri), hr1, map_one, one_mul,
        (GlobalTheory.T.det_twoDiagBlocks_properties _ _ _ D.R.t (r_le_V i) g).2.1 rV htri]
    have hG : ∏ PP' ∈ (R.datVt i t).Pg, ∏ c ∈ Finset.range (R.datVt i t).s, (R.datVt i t).cg (c + 1) PP'
        (dBlk (blkOf (R.datVt i t).r (R.datVt i t).t) (c + 1) (redFn (R.βV i) PP' (finE (Vc D i) κ))) =
        (R.chi ((i : ℕ) + 1) PP (Matrix.GeneralLinearGroup.det g))⁻¹ := by
      rw [Finset.prod_eq_single PP]
      · show ∏ c ∈ Finset.range 1, _ = _
        rw [Finset.prod_range_one, hg, hdet]
        rfl
      · intro PP' hP' hne
        rcases hred PP' (Or.inl hP') with h | h
        · refine Finset.prod_eq_one fun c _ => ?_
          rw [h, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
        · exact absurd h hne
      · intro h; exact absurd hPP h
    unfold levChi levFn
    rw [hrT, blockDiagonalExtendByOnePrimeField_one, hQ, hG, one_mul, mul_one, Units.val_inv_eq_inv_val]

theorem heisO_smul_fun {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (w : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (c • f) = c • heisO ψ S T w f := by
  funext x; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

theorem schrodinger_type_inv : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.thP_ωP → ∀ (i : Fin D.R.m) (t : T) (PP : Pl D.host.E), PP ∈ R.Pg → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsProjAt φ PP → IsIdemOf φ e → ∀ (red : OI v →+* kP PP), Function.Surjective red → (∀ a : OI v, red a = 0 ↔ Valued.v (a : Fv D.host.F v) < 1) → ActAt R i t PP φ e red → ∀ (Sb : Finset (FinPl D)), v ∈ Sb → ∀ (σ : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v) → WO (Vc D i) (Wc D i)), (∀ X, IsHalf (cA D e) (σ X) ∧ coR R i φ (σ X) = X) → ∀ (ℓ : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] ℂ), InvForm R.ψ (Vc D i) (Wc D i) e ℓ → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), TypeIn R i t Sb f → ∀ (ϖ : OI v), Irreducible ϖ → ∀ h : GL (Fin D.R.r ⊕ Fin D.R.t) (OI v), (∀ a b, (h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)) (Sum.inl a) (Sum.inl b) - (1 : Matrix (Fin D.R.r) (Fin D.R.r) (OI v)) a b ∈ Ideal.span {ϖ}) → (∀ a b, (h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)) (Sum.inr a) (Sum.inl b) ∈ Ideal.span {ϖ}) → ∀ X : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v), ℓ (heisO R.ψ (Vc D i) (Wc D i) (σ ((h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)).map (algebraMap (OI v) (Fv D.host.F v)) * X)) f) = ℓ (heisO R.ψ (Vc D i) (Wc D i) (σ X) f) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hω i t PP hPP v φ e hφ he red hsur hker hAct Sb hv σ hσ ℓ hℓ f hf ϖ hϖ h hh1 hh2 X
  let e' := rowIx (rank_V i)
  let h' : GL (Fin (Vc D i).rank) (OI v) := Units.map (Matrix.reindexAlgEquiv (OI v) (OI v) e').toMonoidHom h
  have hh' : ∀ a b, (h' : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (OI v)) (e' a) (e' b) =
      (h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)) a b := by
    intro a b
    simp [h', Matrix.reindexAlgEquiv_apply]
  obtain ⟨κ, hsupp, hGf, hSt, hgrp, hred', hoth, hact⟩ := hAct h'
  have hϖ0 : red ϖ = 0 := by
    haveI : PP.asIdeal.IsMaximal := PP.isMaximal
    letI : Field (kP PP) := Ideal.Quotient.field _
    have hmax : RingHom.ker red = IsLocalRing.maximalIdeal (OI v) :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective red hsur)
    have : ϖ ∈ RingHom.ker red := by
      rw [hmax]; exact (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
    exact this
  have hspan : ∀ x ∈ Ideal.span {ϖ}, red x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [map_mul, hϖ0, mul_zero]
  have hg1 : ∀ a b : Fin D.R.r, ((Matrix.GeneralLinearGroup.map red h' : GL (Fin (Vc D i).rank) (kP PP)) :
      Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (kP PP)) (e' (Sum.inl a)) (e' (Sum.inl b)) =
      (1 : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)) a b := by
    intro a b
    have h0 := hspan _ (hh1 a b)
    rw [map_sub, sub_eq_zero] at h0
    rw [Matrix.GeneralLinearGroup.map_apply, hh', h0]
    by_cases hab : a = b
    · subst hab; simp
    · simp [Matrix.one_apply_ne hab]
  have hg2 : ∀ (a : Fin D.R.t) (b : Fin D.R.r), ((Matrix.GeneralLinearGroup.map red h' : GL (Fin (Vc D i).rank) (kP PP)) :
      Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (kP PP)) (e' (Sum.inr a)) (e' (Sum.inl b)) = 0 := by
    intro a b
    rw [Matrix.GeneralLinearGroup.map_apply, hh']
    exact hspan _ (hh2 a b)
  obtain ⟨hmem, hchi⟩ := levG_levChi_of_red D G Pl0 T A Ks R hL i t PP hPP κ hGf hSt _ hred' hoth hg1 hg2
  have hSIn : SuppIn Sb (Vc D i) κ := suppIn_of_suppAt he hv hsupp
  have hW := hω i t
  have hTy := hf.2 κ hmem hSIn
  rw [hchi, inv_inv] at hTy
  have hx := actO_sigma_of_grpCo D G Pl0 T A Ks R hL i v φ e he σ hσ κ h h' hh' hgrp X
  have e1 := hW.om_heis κ 1 (σ X) f hf.1
  rw [hx, hTy, heisO_smul_fun] at e1
  have e2 := hact ℓ hℓ (heisO R.ψ (Vc D i) (Wc D i) (σ X) f)
    (GlobalTheory.TwistFactorCompare.isTheta_heisO hW.std hf.1 _)
  rw [e1, map_smul, smul_eq_mul] at e2
  exact mul_left_cancel₀ (Units.ne_zero _) e2

end GlobalTheory.DownLift.GenSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchrodingerFunctionInvariantTypePrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodingerFunction_invariant_typePrime : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.thP_ωP → ∀ (i : Fin D.R.m) (t : T) (PP : Pl D.host.E), PP ∈ R.Pg → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsProjAt φ PP → IsIdemOf φ e → ∀ (red : OI v →+* kP PP), Function.Surjective red → (∀ a : OI v, red a = 0 ↔ Valued.v (a : Fv D.host.F v) < 1) → ActAt R i t PP φ e red → ∀ (Sb : Finset (FinPl D)), v ∈ Sb → ∀ (σ : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v) → WO (Vc D i) (Wc D i)), (∀ X, IsHalf (cA D e) (σ X) ∧ coR R i φ (σ X) = X) → ∀ (ℓ : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] ℂ), InvForm R.ψ (Vc D i) (Wc D i) e ℓ → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), TypeIn R i t Sb f → ∀ (ϖ : OI v), Irreducible ϖ → ∀ h : GL (Fin D.R.r ⊕ Fin D.R.t) (OI v), (∀ a b, (h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)) (Sum.inl a) (Sum.inl b) - (1 : Matrix (Fin D.R.r) (Fin D.R.r) (OI v)) a b ∈ Ideal.span {ϖ}) → (∀ a b, (h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)) (Sum.inr a) (Sum.inl b) ∈ Ideal.span {ϖ}) → ∀ X : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v), ℓ (heisO R.ψ (Vc D i) (Wc D i) (σ ((h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)).map (algebraMap (OI v) (Fv D.host.F v)) * X)) f) = ℓ (heisO R.ψ (Vc D i) (Wc D i) (σ X) f) := by
  first | exact @GlobalTheory.DownLift.GenSplit.schrodinger_type_inv | exact GlobalTheory.DownLift.GenSplit.schrodinger_type_inv | (intros; apply GlobalTheory.DownLift.GenSplit.schrodinger_type_inv <;> assumption)
end
end
