module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOmegaField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoversAtOverField
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoverOverField

open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV GlobalTheory.TupleCover GlobalTheory.TwistField

section Roots

theorem prim_mul {L : Type} [Field L] {a b : ℕ} (hab : Nat.Coprime a b) (ha : ∃ z : L, IsPrimitiveRoot z a)
    (hb : ∃ z : L, IsPrimitiveRoot z b) : ∃ z : L, IsPrimitiveRoot z (a * b) := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  refine ⟨x * y, ?_⟩
  have h := (Commute.all x y).orderOf_mul_eq_mul_orderOf_of_coprime (by rw [← hx.eq_orderOf, ← hy.eq_orderOf]; exact hab)
  rw [← hx.eq_orderOf, ← hy.eq_orderOf] at h
  rw [← h]
  exact IsPrimitiveRoot.orderOf _

theorem prim_prod {L : Type} [Field L] (s : Finset ℕ) (hp : ∀ q ∈ s, q.Prime) (hz : ∀ q ∈ s, ∃ z : L, IsPrimitiveRoot z q) :
    ∃ z : L, IsPrimitiveRoot z (∏ q ∈ s, q) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    refine prim_mul ?_ (hz a (Finset.mem_insert_self _ _))
      (ih (fun q hq => hp q (Finset.mem_insert_of_mem hq)) (fun q hq => hz q (Finset.mem_insert_of_mem hq)))
    refine Nat.Coprime.prod_right fun q hq => ?_
    exact (Nat.coprime_primes (hp a (Finset.mem_insert_self _ _)) (hp q (Finset.mem_insert_of_mem hq))).2
      (fun h => ha (h ▸ hq))

theorem mem_range_of_pow {L : Type} [Field L] (σ : L →+* ℂ) {n : ℕ} (hn : 0 < n) (hz : ∃ z : L, IsPrimitiveRoot z n)
    {w : ℂ} (hw : w ^ n = 1) : w ∈ σ.fieldRange := by
  obtain ⟨z, hz⟩ := hz
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨i, -, hi⟩ := (hz.map_of_injective σ.injective).eq_pow_of_pow_eq_one hw
  exact ⟨z ^ i, by rw [map_pow]; exact hi⟩

end Roots

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem exists_fun_of_val {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {n r : ℕ} (d : DeltaDat Xo c n) (V : HSp D) (hr : V.rank = r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hio : IotaOK Dw V ι) (hpos : 1 ≤ Dw.p + Dw.q)
    (hx₀ : ∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 →
      gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) =
        Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ))
    (hlev : d.IsLev) (hA : d.l₂.A = 1) (hcl : FnAlgClosed (Xo := d.Xo₂) (c := d.c₂))
    (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
    (h1 : ∀ g : GA D V, (∃ w ∈ intAE D, ((Matrix.GeneralLinearGroup.det (finHom V g) :
      (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = d.l₂.M • w) →
      xi (Matrix.GeneralLinearGroup.det (finHom V g)) = 1)
    (h2 : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1)
    (m : ℕ) (hm : 0 < m) (h3 : ∀ g : GA D V, xi (Matrix.GeneralLinearGroup.det (finHom V g)) ^ m = 1)
    (hz : ∀ g : GA D V, ((xi (Matrix.GeneralLinearGroup.det (finHom V g)) : ℂˣ) : ℂ) ∈ c.F) :
    ∃ f : Rul d.Xo₂ d.c₂, ({ d with cδ := f } : DeltaDat Xo c n).IsLev ∧ f ^ m = 1 ∧
      ∃ (U₂ : Unf d.Xo₂ d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) r) (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r),
        IsUnf U₂ ∧ (∀ k, ModelW V hr (U₂.X k)) ∧
        ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
          (F : FamilyUnif d.Xo₂ (((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)).comp
              (IntermediateField.inclusion d.c₂.le).toRingHom)
            (fun j => relab d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) (e j).1))
          (ik : U₂.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U₂.X k).Λ)
          (th : ∀ k, (U₂.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
          (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictLat U₂ V hr dict₂ ι e F ik φ th x₀ ∧
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
  obtain ⟨f, hf, hfm, -, hfx⟩ := GlobalTheory.XiFun.exists_sec_char_val D _ _ _ _ _ _ _ _ C.hr (C.unf un) dict C.ι g e F ik φ th C.x₀
    hC.iota hpos hA hg₂ hP.modelW hdl hdu.2.2.2.1 hcl xi
    (fun u _ hu => h1 u (by rw [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]; exact hu)) h2
    (fun h => ⟨⟨_, d.hF.symm ▸ hz h⟩, rfl⟩)
  have hfm' : f ^ m = 1 := hfm m h3
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, -, l9⟩ := hlev
  refine ⟨f, ⟨l1, l2, l3, l4, l5, l6, l7, hf, fun k _ _ _ y => ?_⟩, hfm', C.unf un, dict, hP.unf, hP.modelW,
      g, e, F, ik, φ, th, hth, ?_, fun h γ hmk => ?_⟩
  · exact GlobalTheory.XiFun.evR_ne_zero_of_pow _ _ f d.cδ m hm hfm' k y (l9 k y)
  · rw [← hCι, ← hCx]
    exact hdl
  · rw [one_mul]
    rw [← hCι] at hmk
    exact hfx h γ hmk

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Real

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem prim_tupPrime (t : T0) (h : Lev.IsTwistPlaces D.host.g (R.Q t)) (hr : R.fam_roots) :
    ∃ z : D.what₂.LL, IsPrimitiveRoot z (tupPrime R t) := by
  refine prim_prod _ (fun q hq => ?_) fun q hq => ?_
  · obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hq
    obtain ⟨⟨q, hq, he, -⟩, -⟩ := h PP hPP
    exact he ▸ hq
  · obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hq
    exact hr t PP (Or.inr hPP)

end Real

section Cover

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)

theorem exists_coeff_cover (t : T0) (h : Lev.IsTwistPlaces D.host.g (R.Q t)) (hr : R.fam_roots) (c' : Coeff T.Q.l)
    (hc : c'.F = D.what₂.embLL.toRatAlgHom.fieldRange) (l₂ : Level T.Q.H) (hM : l₂.M = T.Q.l.M * tupPrime R t) (hA : l₂.A = 1)
    (hcop : Nat.Coprime T.Q.l.M (tupPrime R t)) :
    ∃ c₂ : Coeff l₂, c₂.F = D.what₂.embLL.toRatAlgHom.fieldRange := by
  have hM0 : 0 < T.Q.l.M := lt_of_lt_of_le (by norm_num) T.Q.l.three_le
  have hM' : T.Q.l.M' ≠ 0 := Nat.lcm_ne_zero hM0.ne' T.Q.l.A_pos.ne'
  have h1 : ∃ z : D.what₂.LL, IsPrimitiveRoot z T.Q.l.M := by
    have hz := c'.zeta_mem
    rw [hc] at hz
    obtain ⟨y, hy⟩ := hz
    have hp : IsPrimitiveRoot y T.Q.l.M' :=
      IsPrimitiveRoot.of_map_of_injective (f := D.what₂.embLL) (by
        have : D.what₂.embLL y = zeta T.Q.l.M' := hy
        rw [this]; exact Complex.isPrimitiveRoot_exp _ hM') D.what₂.embLL.injective
    obtain ⟨k, hk⟩ : T.Q.l.M ∣ T.Q.l.M' := Nat.dvd_lcm_left _ _
    exact ⟨y ^ k, hp.pow (Nat.pos_of_ne_zero hM') (by rw [hk, mul_comm])⟩
  have h2 := prim_mul hcop h1 (prim_tupPrime R t h hr)
  have hM2 : l₂.M' = T.Q.l.M * tupPrime R t := by simp [Level.M', hA, hM]
  have hpos : 0 < T.Q.l.M * tupPrime R t := hM ▸ lt_of_lt_of_le (by norm_num) l₂.three_le
  refine ⟨⟨c'.F, c'.fin, c'.conj, ?_, ?_⟩, hc⟩
  · rw [hc, hM2]
    exact mem_range_of_pow D.what₂.embLL hpos h2 (Complex.isPrimitiveRoot_exp _ hpos.ne').pow_eq_one
  · refine IntermediateField.adjoin_le_iff.2 ?_
    intro z hz
    rcases hz with rfl | rfl
    · exact c'.le (IntermediateField.subset_adjoin _ _ (by simp))
    · rw [hA]
      have : zeta 1 = 1 := (pow_one _).symm.trans (Complex.isPrimitiveRoot_exp 1 one_ne_zero).pow_eq_one
      rw [this]; exact c'.F.one_mem

end Cover


set_option maxHeartbeats 1000000 in
theorem coversAt_over_field (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (hT : LawsJ T) (hL : R.toLevCh.Is A.μ0) (hr : R.fam_roots) (hV : XiVal R) (hC : CoverField T R) (i : Fin D.R.m) (n : ℕ)
    (I : T0 → Ideal (𝓞 D.host.E)) (l₂ : T0 → Level T.Q.H)
    (hl : ∀ t, IsCoverLevel T.Q.l (tupPrime R t) (I t) (l₂ t)) (hH : ∀ t, HalfIs R t T.Q.l.Mb (I t))
    (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F) (hc' : c'.F = D.what₂.embLL.toRatAlgHom.fieldRange) :
    CoversAt T R i n (tupPrime R) I l₂ c' hle := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hpq := (exists_iotaOK D T.Q hT.pins _ hj).2
  have hpos : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by omega
  choose m hm ho using hL.xi_fin
  choose xi hx1 hx2 hx3 hx4 using fun t =>
    exists_xi D (Wc D i) (R.xi t) (R.xiH t) (hL.xi t) (m t) (hm t) (ho t) (hL.xi_triv t) (hL.xi_tame t)
  have hσ : GoodEmb T.Q.c (sOv T.toCore c' hle) := rfl
  obtain ⟨hio, hx₀⟩ := iotaOK_and_frame T hT _ hj _ hσ (Wc D i) (hT.spaceW _ hj _ hσ) (rank_Wc i)
  have key : ∀ t, ∃ d : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n, d.pd = tupPrime R t ∧ d.I = I t ∧ d.l₂ = l₂ t ∧ d.IsLev ∧
      d.l₂.A = 1 ∧ FnAlgClosed (Xo := d.Xo₂) (c := d.c₂) ∧ ∃ _ : StarRing (𝓞 D.host.E), IsNab d.Xo₂ d.c₂ d.nab₂ := fun t => by
    obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hl t
    obtain ⟨Xo₂⟩ := GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.1 _ _ (T.Q.Dw ((i : ℕ) + 1)) (l₂ t) hpos
    obtain ⟨c₂, hc₂⟩ := exists_coeff_cover T R t (hL.Q_pl t) hr c' hc' (l₂ t) l2 l6 l3.symm
    obtain ⟨d, a1, a2, a3, -, -, -, a4, a5⟩ := GlobalTheory.LevelCover.exists_deltaDat_isLev _ _ _ _ (T.Q.Xo ((i : ℕ) + 1)) c' hpos n
      (tupPrime R t) (I t) (l₂ t) Xo₂ c₂ (hc₂.trans hc'.symm) l1 l2 l3 l4 l5
    exact ⟨d, a1, a2, a3, a4, a3 ▸ l6, hC i t d.l₂ (a3 ▸ l1) (a3 ▸ l2) (a3 ▸ l6) _ _ (d.hF.trans hc'), a5⟩
  choose d a1 a2 a3 a4 a5 a6 a7 using key
  have hM : ∀ t, ∀ PP ∈ R.Q t, (((d t).l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun t PP hPP => by
    refine (hH t).2.1 PP hPP ?_
    have h1 : (((d t).l₂.M : ℕ) : 𝓞 D.host.E) ∈ (d t).l₂.Mb :=
      Ideal.mul_le_left ((d t).l₂.prod.ge (Ideal.mem_span_singleton_self _))
    rw [(a4 t).2.2.2.1, a2] at h1
    exact Ideal.mul_le_right h1
  have hval : ∀ t (g : GA D (Wc D i)),
      ((xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) : ℂˣ) : ℂ) ∈ c'.F := fun t g => by
    obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws D (Wc D i)).1 g
    rw [hx1 t g x hx, hc']
    exact hV t x
  choose f b1 b2 U₂ dict₂ b3 using fun t =>
    exists_fun_of_val (d t) (Wc D i) (rank_Wc i) (iotaW T i) _ hio hpos hx₀ (a4 t) (a5 t) (a6 t) (xi t)
      (hx2 t _ (d t).l₂.odd (unrAt_of_not_mem R hL t _ (hM t))) (hx3 t) (m t) (hm t) (hx4 t) (hval t)
  refine ⟨fun t => { d t with cδ := f t }, U₂, dict₂, xi, fun t => ⟨a1 t, a2 t, a3 t⟩, fun t => ⟨b1 t, a5 t, a7 t⟩,
    fun t => ?_, hx1, ⟨1, ⟨1, one_pos, one_pow 1⟩, b3⟩, fun t => (b3 t).2.1, fun t => ⟨m t, hm t, b2 t⟩⟩
  change HalfIs R t T.Q.l.Mb (d t).I
  rw [a2]
  exact hH t

end GlobalTheory.CoverOverField

section Target
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.CoverOverField.coversAt : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), LawsJ T → R.toLevCh.Is A.μ0 → R.fam_roots → GlobalTheory.TwistField.XiVal R → GlobalTheory.TwistField.CoverField T R → ∀ (i : Fin D.R.m) (n : ℕ) (I : T0 → Ideal (𝓞 D.host.E)) (l₂ : T0 → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level T.Q.H), (∀ t, GlobalTheory.CoverHalf.IsCoverLevel T.Q.l (GlobalTheory.TwistField.tupPrime R t) (I t) (l₂ t)) → (∀ t, HalfIs R t T.Q.l.Mb (I t)) → ∀ (c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F), c'.F = D.what₂.embLL.toRatAlgHom.fieldRange → GlobalTheory.TupleCover.CoversAt T R i n (GlobalTheory.TwistField.tupPrime R) I l₂ c' hle :=
  fun _ _ _ _ _ _ _ T _ R hT hL hr hV hC i n I l₂ hl hH c' hle hc' =>
    GlobalTheory.CoverOverField.coversAt_over_field T R hT hL hr hV hC i n I l₂ hl hH c' hle hc'

end Target
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PbEqOfTie
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelPrimes

theorem pb_eq_of_tie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), R.Char F → Nonempty (FWTie T R κ v₀) → OMPins T R κ v₀ O i → T.pb = R.C.P.pb := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O i hC hW hO
  obtain ⟨w⟩ := hW
  exact GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R w.laws.toLawsM hC.lev (hO.2.tuple ()).half

end GlobalTheory.LevelPrimes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNormalisedTupleDataOverCoefficientField
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PinsOverField

open GlobalTheory.CoverHalf GlobalTheory.TwistField GlobalTheory.PinnedData
open scoped nonZeroDivisors

theorem prod_image_congr {α β γ M : Type} [DecidableEq β] [DecidableEq γ] [CommMonoid M] (s : Finset α) (f : α → β) (g : α → γ)
    (P : β → M) (Q : γ → M) (h : ∀ a ∈ s, ∀ b ∈ s, f a = f b ↔ g a = g b) (hv : ∀ a ∈ s, P (f a) = Q (g a)) :
    ∏ b ∈ s.image f, P b = ∏ c ∈ s.image g, Q c := by
  have key : ∀ b ∈ s.image f, ∃ a ∈ s, f a = b := fun b hb => Finset.mem_image.1 hb
  choose u hu1 hu2 using key
  refine Finset.prod_bij (fun b hb => g (u b hb)) (fun b hb => Finset.mem_image_of_mem _ (hu1 b hb)) ?_ ?_ ?_
  · intro b hb b' hb' e
    rw [← hu2 b hb, ← hu2 b' hb']
    exact (h _ (hu1 b hb) _ (hu1 b' hb')).2 e
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hc
    have hb := Finset.mem_image_of_mem f ha
    exact ⟨f a, hb, (h _ (hu1 _ hb) _ ha).1 (hu2 _ hb)⟩
  · intro b hb
    rw [← hv _ (hu1 b hb), hu2]

variable {D : D7}


open Formalism.L2.Pj.LPb in
theorem coverHalf_mul {Q : Finset (Pl D.host.E)} (hQ : Lev.IsTwistPlaces D.host.g Q)
    (h2 : ∀ PP ∈ Q, (2 : 𝓞 D.host.E) ∉ PP.asIdeal)
    (h1 : ∀ PP ∈ Q, ∀ PP' ∈ Q, (∃ p : ℕ, p.Prime ∧ (p : 𝓞 D.host.E) ∈ PP.asIdeal ∧ (p : 𝓞 D.host.E) ∈ PP'.asIdeal) →
      PP.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = PP'.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) :
    coverHalf D Q * (coverHalf D Q).map (bH D) =
      Ideal.span {((∏ q ∈ Q.image (fun PP => Nat.card (kP PP)), q : ℕ) : 𝓞 D.host.E)} := by
  classical
  have key : ∀ PP ∈ Q, (Nat.card (kP PP)).Prime ∧ ((Nat.card (kP PP) : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal ∧
      SplitOK D (Nat.card (kP PP)) := fun PP hPP => by
    obtain ⟨⟨q, hq, hc, hu, -⟩, -⟩ := hQ PP hPP
    rw [hc]
    exact ⟨hq, splitOK_of_place PP hq hc hu (h2 PP hPP)⟩
  have hun : ∀ (PP : Pl D.host.E) (q : ℕ), (q : 𝓞 D.host.K) ∈ (PP.under (𝓞 D.host.K)).asIdeal ↔
      (q : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP q => by
    show algebraMap (𝓞 D.host.K) (𝓞 D.host.E) q ∈ PP.asIdeal ↔ _
    rw [map_natCast]
  unfold coverHalf
  rw [← Ideal.mapHom_apply, map_prod, ← Finset.prod_mul_distrib, Nat.cast_prod, ← Ideal.prod_span_singleton]
  convert prod_image_congr Q (fun PP => PP.under (𝓞 D.host.K)) (fun PP => Nat.card (kP PP))
    (fun 𝔭 => 𝔭.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) *
      Ideal.mapHom (bH D) (𝔭.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))))
    (fun q => Ideal.span {(q : 𝓞 D.host.E)}) (fun a ha b hb => ⟨fun e => ?_, fun e => ?_⟩) fun a ha => ?_
  · by_contra hne
    have h3 := (hun b _).1 (e ▸ (hun a _).2 (key a ha).2.1)
    exact not_mem_of_coprime b.isPrime.ne_top ((Nat.coprime_primes (key a ha).1 (key b hb).1).2 hne) h3 (key b hb).2.1
  · exact HeightOneSpectrum.ext (h1 a ha b hb ⟨_, (key a ha).1, (key a ha).2.1, by
      rw [show Nat.card (kP a) = Nat.card (kP b) from e]; exact (key b hb).2.1⟩)
  · obtain ⟨e, he1, he2, he3⟩ := pb_eq_JK D (key a ha).2.2 _ ((hun a _).2 (key a ha).2.1)
    simp only [Ideal.mapHom_apply]
    rw [he3, map_JK, QE_map_bar]
    exact QE_mul D _ _ he1 he2

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_half_tupPrime (T : Core D) (R : RealDat D A Ks) {μ0 : T0} (hT : LawsM T) (hL : R.toLevCh.Is μ0)
    (hO : T.pb = R.C.P.pb) (hG : QGuard R) (t : T0) :
    ∃ l₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level T.Q.H, IsCoverLevel T.Q.l (tupPrime R t) (coverHalf D (R.Q t)) l₂ ∧
      HalfIs R t T.Q.l.Mb (coverHalf D (R.Q t)) := by
  obtain ⟨pd, l₂, h1, h2⟩ := exists_half_of_laws T R hT hL hO hG t
  have hb : (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = bH D :=
    RingHom.ext fun a => RingOfIntegers.ext (T.Q.H.bar_eq a)
  have h3 : ∀ PP ∈ R.Q t, (2 : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP h => hG.2 t PP hPP (by
    rw [Nat.cast_mul, Nat.cast_mul, mul_assoc]
    obtain ⟨c, hc⟩ := D.host.two_dvd_QS
    refine Ideal.mul_mem_right _ _ ?_
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (by exact_mod_cast h))
  have h4 := coverHalf_mul (hL.Q_pl t) h3 (hG.1 t)
  have h5 := l₂.prod
  rw [h1.2.2.2.1, Ideal.map_mul, mul_mul_mul_comm, T.Q.l.prod, hb, h4, h1.2.1, Ideal.span_singleton_mul_span_singleton,
    ← Nat.cast_mul] at h5
  have h6 := congrArg Ideal.absNorm h5
  rw [Ideal.absNorm_span_natCast, Ideal.absNorm_span_natCast] at h6
  have h7 := Nat.pow_left_injective Module.finrank_pos.ne' h6
  have h8 : tupPrime R t = pd := Nat.eq_of_mul_eq_mul_left (by have := T.Q.l.three_le; omega) h7
  exact ⟨l₂, h8 ▸ h1, h2⟩

variable (R : RealDat D A Ks) (i : Fin D.R.m)

theorem locK_mem (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam) (t : T0) (PP : Pl D.host.E) (k : D.host.Eˣ) :
    (((R.xiH t).locK PP k : ℂˣ) : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange := by
  obtain ⟨_, _, _, hT⟩ := hF.tie
  exact GlobalTheory.TwistValues.xiH_locK_mem R hL hF.pl_onto hF.muVal hT.ok ⟨0, lt_of_lt_of_le two_pos D.R.two_le_m⟩ t PP k

theorem xiR_mem (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam) (t : T0) (P : Pl D.host.E) (hP : P ∈ R.Q t) (u : (kP P)ˣ) :
    ((R.xiR t P u : ℂˣ) : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := P.asIdeal) (u : kP P)
  have hnt : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have ha0 : (a : D.host.E) ≠ 0 := by
    intro h
    have h0 : a = 0 := RingOfIntegers.ext h
    rw [h0, map_zero] at ha
    exact u.ne_zero ha.symm
  rw [hL.xiR t P hP a (Units.mk0 _ ha0) u rfl ha.symm]
  exact locK_mem R hL hF t P _

theorem exists_BIs (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam) (M : IntermediateField ℚ ℂ)
    (hM : M = D.what₂.embLL.toRatAlgHom.fieldRange) {b : ℕ} {B₀ : Ideal (𝓞 D.host.E) → M}
    (h₀ : BIs R i M.val.toRingHom A.μ0 b B₀) (t : T0) {bad : ℕ} (hb : b ∣ bad) :
    ∃ B : Ideal (𝓞 D.host.E) → M, BIs R i M.val.toRingHom t bad B := by
  have key : ∀ v : HeightOneSpectrum (𝓞 D.host.E), ((bad : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal →
      (((R.C.mu0 i * R.xiH t * R.C.eta⁻¹).val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) ∈ M := by
    intro v hv
    have hv' : ((b : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := fun h => hv (by
      obtain ⟨c, rfl⟩ := hb
      rw [Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ h)
    have h1 := h₀ v.asIdeal v.ne_bot (by
      by_contra hne
      exact hv' (v.isMaximal.eq_of_le hne le_sup_left ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    rw [GlobalTheory.Mem.BVal.onId_prime, hL.xi_base, mul_one] at h1
    have h2 : (((R.xiH t).val v : ℂˣ) : ℂ) ∈ M := hM ▸ locK_mem R hL hF t v _
    have h4 : M.val.toRingHom (B₀ v.asIdeal) ∈ M := (B₀ v.asIdeal).2
    rw [h1] at h4
    have h3 := mul_mem h2 h4
    convert h3 using 1
    rw [mul_right_comm (R.C.mu0 i), Formalism.L2.Host.HChar.val_mul, Units.val_mul]
    ring
  classical
  refine ⟨fun cc => if h : cc ≠ ⊥ ∧ cc ⊔ Ideal.span {((bad : ℕ) : 𝓞 D.host.E)} = ⊤ then
    ⟨_, GlobalTheory.Mem.BVal.mem_of_primes _ M _ key cc h.1 h.2⟩ else 0, fun cc h0 h1 => ?_⟩
  simp only [dif_pos (And.intro h0 h1)]
  rfl


set_option maxHeartbeats 1000000 in
theorem exists_phi_over {F : Face D A} (hR : R.Char F) (hV : VStd D i) (t : T0) {La : Type} [AddCommGroup La]
    [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (hι : LatEmb (Wc D i) ι)
    (M : IntermediateField ℚ ℂ) (hM : M = D.what₂.embLL.toRatAlgHom.fieldRange)
    (hP : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (J : Ideal (𝓞 D.host.E))
    (hJ : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ∀ c ∈ J, ∃ c' ∈ PP.asIdeal, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E)) :
    ∃ φ : (Fin (Vc D i).rank → La ⧸ (J • ⊤ : Submodule (𝓞 D.host.E) La)) → M, PhiIs R i M.val.toRingHom t ι (J • ⊤) φ := by
  have hv : ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP),
      omegaK R.Pg y * omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) y ∈ M := fun y => by
    refine mul_mem ?_ ?_
    · unfold omegaK
      split_ifs
      exacts [one_mem _, zero_mem _]
    · unfold omegaQ
      split_ifs
      · exact prod_mem fun PP _ => zpow_mem (hM ▸ xiR_mem R hR.lev hR.fam t PP.1 PP.2 _) _
      · exact zero_mem _
  obtain ⟨-, e, he, -⟩ := hR.thP.vP i t
  have hβ := GlobalTheory.T.inverse_selfDual_frame_standard_space_integral D i _ _ hV (hR.lev.βV i)
  have hi : ∀ x a, rowP (Wc D i) (R.βW i) e (ι x) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun x a =>
    rowP_int _ _ _ (hR.lev.βW i) e _ he (fun PP h => hP PP (by simpa using h)) _
      (hι.2.le (LinearMap.mem_range_self ι x)) a
  refine ⟨fun q => ⟨_, hv fun PP => redM PP
    (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (q b).out)⟩, e, he, fun x =>
    ⟨(redM_uMat (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e (fun b => ι (x b)) fun b a => hi (x b) a).1, ?_⟩⟩
  exact omega_congr _ _ _ _ _ _ _ fun PP hPP => exists_datum (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e ι hi J PP (hJ PP hPP) x _
    fun b => (Submodule.Quotient.eq _).1 (Quotient.out_eq _)


set_option maxHeartbeats 2000000 in
theorem pinsOverL : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), R.Char F → Nonempty (FWTie T R κ v₀) → OMPins T R κ v₀ O i → QGuard R → GlobalTheory.TwistField.CoverField T R → GlobalTheory.TwistField.PinsOverL T R κ v₀ i := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O i hR hfw hO hG hC
  have hpb := GlobalTheory.LevelPrimes.pb_eq_of_tie D G Pl0 T0 A T R F κ v₀ O i hR hfw hO
  obtain ⟨fw⟩ := id hfw
  have hT := fw.laws
  obtain ⟨hc', hP⟩ := hO
  have hV : VStd D i := hP.lift.std
  have hB0 := (hP.tuple ()).B
  have hb0 := hP.bad ()
  have hjL := hP.lift.field
  have hlev := hP.lift.lev
  have hio := hP.io
  have hact := hP.act
  choose l₂ hl₁ hl₂ using exists_half_tupPrime T.toCore R hT.toLawsM hR.lev hpb hG
  obtain ⟨dδ, U₂, dict₂, xi, -, hcov, hhalf, hxi, hcxi, hmod, -⟩ :=
    GlobalTheory.CoverOverField.coversAt D G Pl0 T0 A T R hT hR.lev hR.fam.roots
      (GlobalTheory.TwistValues.xiVal D G Pl0 T0 A _ R hR.lev hR.fam) hC i (Vc D i).rank _ l₂ hl₁ hl₂ (O i).c' (O i).hle hc'
  obtain ⟨c0', hc0, hplace⟩ := GlobalTheory.T.exists_coeffExt_rationalForms_values_field D G Pl0 T0 A T R F κ v₀ hR hfw hpb i (O i).c'.F (O i).jL (inC (O i).c') hjL
  choose Cl fCl h J' bad Lh gam vol La Nc hrep hdv hvol hok hlat using fun t =>
    GlobalTheory.SplitReps.exists_repsR_repsOK R i (hR.lev.βV i) hV (O i).c'.F t (dδ t).l₂ hb0.1
  have hbad : ∀ t, 0 < bad t ∧ BadPin (bad t) (D.host.QS * D.host.q) D.host.d (D.host.g 0 * D.host.g 1) := fun t =>
    ⟨Nat.pos_of_ne_zero (hrep t).1, hb0.2.1.trans (hdv t), hb0.2.2.1.trans (hdv t), hb0.2.2.2.1.trans (hdv t),
      hb0.2.2.2.2.trans (hdv t)⟩
  choose B hBis using fun t => exists_BIs R i hR.lev hR.fam (O i).c'.F hc' hB0 t (hdv t)
  have hodd : Odd ((T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q) := by
    obtain ⟨e1, e2, -⟩ := hT.pins.2.2.2 _ (inR i)
    have h5 := Formalism.L2.NTheta.odd_r D.R
    have h6 := i.2
    have h7 := D.R.m_add_three_le_k
    rw [e1, e2]
    convert h5 using 1
    simp only [Ranks.sigW, Ranks.r]
    omega
  choose epF hepF using fun t => (GlobalTheory.ClassTieCompare.exists_epIs_iff (n := (Vc D i).rank) (Dw := T.Q.Dw ((i : ℕ) + 1))
    (bad t) (B t)).2 fun L cc g d => GlobalTheory.T.law_of_squares_selfDual_splitLattice _ _ _ _ hodd L cc g.1 g.2.2 d.1 d.2
  choose φ hφis using fun t => exists_phi_over R i hR hV t (iotaW T i) (latEmb_iotaW T hT i) (O i).c'.F hc'
    (hhalf t).2.2 (Mfr (dδ t).l₂) fun PP hPP c hc => by
    have hM : (dδ t).l₂.Mb ≤ PP.asIdeal := by
      rw [(hcov t).1.2.2.2.1]
      rcases hPP with hPP | hPP
      · rw [(hhalf t).1]
        exact Ideal.mul_le_left.trans (Ideal.prod_le_inf.trans (Finset.inf_le hPP))
      · exact Ideal.mul_le_right.trans ((hhalf t).2.1 PP hPP)
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ T.Q.H.bar.surjective).1 hc
    refine ⟨b, hM hb, ?_⟩
    change _ = star ((T.Q.H.bar b : 𝓞 D.host.E) : D.host.E)
    rw [T.Q.H.bar_eq]
    exact (star_star _).symm
  choose thAd hth using fun t => exists_thAd R i hR t c0' (h t) (hrep t).2.2.1 (hrep t).2.2.2.2.2.1 (v₀ i (sg0 D A))
  refine ⟨{ c' := (O i).c', hle := (O i).hle, jL := (O i).jL, hV := (O i).hV, c0' := c0', lev := (O i).lev, dδ := dδ, Cl' := Cl,
            bad := bad, Lh := Lh, La := La, Nc := Nc, gam := gam, vol := vol, ep := fun t k => epF t (Lh t k), B := B,
            epF := epF, io := (O i).io, hw := (O i).hw, φ := φ,
            w := fun t _ q => (dδ t).eF.symm (phiHat (dδ t).c₂ (fun x => (dδ t).eF (φ t x)) q),
            U₂ := U₂, dict₂ := dict₂, xi := xi, thAd := thAd,
            Plc := fun t x => ∃ x₀, Place R i t (h t) c0' (jVx R i t x₀) x }, hc',
    ⟨hjL, hV, fw.hv₀ i _, hc0, hlev⟩,
    fun t => ⟨⟨h t, J' t, hrep t, hplace t _ _, hth t, fun _ => Iff.rfl⟩, hBis t, hxi t, hφis t, hhalf t⟩,
    hact, hbad, fun t => ⟨hok t, hlat t⟩, fun t => ⟨fun _ => rfl, hepF t⟩, hio,
    fun t k q => AlgEquiv.apply_symm_apply _ _, hcov, hcxi, hmod⟩

end GlobalTheory.PinsOverField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNormalisedTupleDataOverCoefficientFieldStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalisedTupleData_over_coefficientField : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), R.Char F → Nonempty (FWTie T R κ v₀) → OMPins T R κ v₀ O i → QGuard R → GlobalTheory.TwistField.CoverField T R → GlobalTheory.TwistField.PinsOverL T R κ v₀ i := by
  first | exact @GlobalTheory.PinsOverField.pinsOverL | exact GlobalTheory.PinsOverField.pinsOverL | (intros; apply GlobalTheory.PinsOverField.pinsOverL <;> assumption)
end
