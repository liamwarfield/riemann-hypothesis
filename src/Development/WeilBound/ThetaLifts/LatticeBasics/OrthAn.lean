module

public import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.SigThConst

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.ConvOfCpt
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {B : Base F E} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {χ χ' : Chr F E} {o : Rep σ Y W} {r s r' s' : ℕ}

theorem conv_of_cpt (hT : ThetaBasic) (p : IsPair B M χ χ' o r s r' s') (c : Cpt σ Y.J) : ∀ Φ ∈ schA F _, M.Conv o Φ := by
  intro Φ hΦ h
  obtain ⟨t1, t2, -⟩ := (hT F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p).1 Φ hΦ
  have hc : Continuous fun g => theta o Φ g h := t1.comp (continuous_id.prodMk continuous_const)
  obtain ⟨C, hC⟩ := c.bdd hc fun γ hγ g => by simpa using t2 γ hγ 1 (one_mem _) g h
  exact Measure.integrableOn_of_bounded (M := C) (c.fin _ _ p.good.haar p.good.dom).ne hc.aestronglyMeasurable
    (Eventually.of_forall hC)

theorem I_lin (hT : ThetaBasic) (p : IsPair B M χ χ' o r s r' s') (c : Cpt σ Y.J) {Φ Ψ : Fn F n d} (hΦ : Φ ∈ schA F _)
    (hΨ : Ψ ∈ schA F _) (a : ℂ) : M.I o (Φ + a • Ψ) = M.I o Φ + a • M.I o Ψ := by
  funext h
  have e : ∀ g, theta o (Φ + a • Ψ) g h = theta o Φ g h + a * theta o Ψ g h := fun g => by
    simp only [theta, map_add (f := _), map_smul]
    rw [thetaSum_add F (p.weil.isUSplitting.pres _ _ hΦ) (Submodule.smul_mem _ _ (p.weil.isUSplitting.pres _ _ hΨ)),
      thetaSum_smul]
  simp only [Model.I, e, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_add (conv_of_cpt hT p c _ hΦ h) ((conv_of_cpt hT p c _ hΨ h).const_mul a), integral_const_mul]

theorem pol_sch (hM : M.IsGood B.ψ) : PolData B M ≤ schA F _ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, -, φ, h1, h2, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ h1 ((h2.and hM.std).mono fun _ h => h.1.trans h.2)

theorem int_right {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Γ : Subgroup G} [Countable Γ] {D : Set G}
    (h : IsFundamentalDomain Γ D μ) (f : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (g : G) :
    ∫ x in D, f (x * g) ∂μ = ∫ x in D, f x ∂μ := by
  have h' : IsFundamentalDomain Γ ((fun x => x * g) '' D) μ := by
    simpa [← Set.image_smul] using h.smul_of_comm (MulOpposite.op g)
  rw [← (measurePreserving_mul_right μ g).setIntegral_image_emb (Homeomorph.mulRight g).measurableEmbedding f D]
  exact h'.setIntegral_eq h fun γ x => hf γ γ.2 x

theorem I_act (hT : ThetaBasic) (p : IsPair B M χ χ' o r s r' s') (c : Cpt σ Y.J) {Φ : Fn F n d} (hΦ : Φ ∈ schA F _)
    (g : UA σ Y.J) : M.I o (o (g, 1) Φ) = M.I o Φ := by
  funext h
  obtain ⟨-, t2, -⟩ := (hT F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p).1 Φ hΦ
  haveI := c.cnt
  haveI := p.good.haar
  haveI := c.right _ p.good.haar
  have e : ∀ x, theta o (o (g, 1) Φ) x h = theta o Φ (x * g) h := fun x => by
    rw [theta, theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  simp only [Model.I, e]
  exact int_right p.good.dom (fun x => theta o Φ x h)
    (fun γ hγ x => by simpa using t2 γ hγ 1 (one_mem _) x h) g

theorem upd_sb {v : Pl F} {φ : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ} (h : ∀ u, φ u ∈ SB _) {z} (hz : z ∈ SB _) (u : Pl F) :
    Function.update φ v z u ∈ SB _ := by
  by_cases e : u = v
  · subst e; rwa [Function.update_self]
  · rw [Function.update_of_ne e]; exact h u

theorem upd_cof {v : Pl F} {φ φ' : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ} (h : ∀ᶠ u in cofinite, φ u = φ' u) (z) :
    ∀ᶠ u in cofinite, Function.update φ v z u = φ' u :=
  (h.and (eventually_cofinite_ne v)).mono fun _ e => by rw [Function.update_of_ne e.2]; exact e.1

theorem I_aug (hT : ThetaBasic) (p : IsPair B M χ χ' o r s r' s') (c : Cpt σ Y.J) (v : Pl F) (f : SInf F (Fin n × Fin d))
    {φ : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ} (h1 : ∀ u, φ u ∈ SB _) (h2 : ∀ᶠ u in cofinite, φ u = M.vac u)
    {z₀ z} (h0 : z₀ ∈ SB _) (hz : z ∈ augAt o v) :
    M.I o (pure f (Function.update φ v (z₀ + z))) = M.I o (pure f (Function.update φ v z₀)) := by
  have h3 := (h2.and p.good.std).mono fun _ h => h.1.trans h.2
  obtain ⟨t, ht, ht'⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ h3
  have mem : ∀ z ∈ SB _, pure f (Function.update φ v z) ∈ schA F _ := fun z hz =>
    GlobalTheory.TensUniq.pure_mem_schA f _ (upd_sb h1 hz) (upd_cof h3 z)
  have add : ∀ z ∈ SB _, ∀ z' ∈ SB _, ∀ a : ℂ, M.I o (pure f (Function.update φ v (z + a • z'))) =
      M.I o (pure f (Function.update φ v z)) + a • M.I o (pure f (Function.update φ v z')) := fun z hz z' hz' a => by
    rw [← I_lin hT p c (mem z hz) (mem z' hz'), ← ht', ← ht', ← ht']
    congr 1
    funext x
    simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have zero : M.I o (pure f (Function.update φ v 0)) = 0 := by
    have := add 0 (zero_mem _) 0 (zero_mem _) (-1)
    simpa using this
  have key : z ∈ SB _ ∧ M.I o (pure f (Function.update φ v z)) = 0 := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨g, -, x, hx, y, hy, a, rfl⟩ := hz
      refine ⟨sub_mem hy hx, ?_⟩
      have e := a t ⟨ht, ht' x ▸ mem x hx⟩
      rw [ht', ht'] at e
      rw [sub_eq_add_neg, ← neg_one_smul ℂ x, add y hy x hx, ← e, I_act hT p c (mem x hx)]
      simp
    | zero => exact ⟨zero_mem _, zero⟩
    | add x y _ _ hx hy => exact ⟨add_mem hx.1 hy.1, by simpa [hx.2, hy.2] using add x hx.1 y hy.1 1⟩
    | smul a x _ hx => exact ⟨Submodule.smul_mem _ _ hx.1, by simpa [hx.2, zero] using add 0 (zero_mem _) x hx.1 a⟩
  simpa [key.2] using add z₀ h0 z key.1 1

theorem toSo_of (hR : KReal) (hF : KFin) (hK : KCoinv) (hT : ThetaBasic) (hC : CptAll) : ToSo := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h hq Φ' hΦ
  obtain ⟨R, hr⟩ := hR F E σ B a a' G X om om' h
  obtain ⟨Rf, hf⟩ := hF F E σ B a a' G X om om' h
  obtain ⟨-, k1, k2, -⟩ := (hK F E σ B a a' G X om om' R Rf ⟨h, hr, hf⟩).1 _ h.chars.good
  have p := pairV' h
  have c := hC F E σ B _ _ _ _ h.base (.inl p.herm) (by omega)
  have le := pol_sch p.good
  induction hΦ using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨f, hf, φ, h1, h2, rfl⟩ := hz
    obtain ⟨y, hy, e⟩ := k2 B.τ₁ (Rf.p' _ (φ B.v₁))
    refine ⟨pure f (Function.update φ B.v₁ y), ⟨Submodule.subset_span ⟨f, hf, _, upd_sb h1 hy.1, upd_cof h2 y, rfl⟩,
      Submodule.subset_span ⟨f, _, upd_sb h1 hy.1, upd_cof h2 y, by rwa [Function.update_self], rfl⟩⟩, ?_⟩
    have := I_aug hT p c B.v₁ f h1 h2 hy.1 ((k1 _ (sub_mem (h1 _) hy.1)).1 (by rw [map_sub, e, sub_self]))
    rw [← this, add_sub_cancel, Function.update_eq_self]
  | zero => exact ⟨0, zero_mem _, rfl⟩
  | add x y hx hy ix iy =>
    obtain ⟨x', mx, ex⟩ := ix
    obtain ⟨y', my, ey⟩ := iy
    refine ⟨x' + y', add_mem mx my, ?_⟩
    rw [← one_smul ℂ y, ← one_smul ℂ y', I_lin hT p c (le mx.1) (le my.1), I_lin hT p c (le hx) (le hy), ex, ey]
  | smul t x hx ix =>
    obtain ⟨x', mx, ex⟩ := ix
    refine ⟨t • x', Submodule.smul_mem _ _ mx, ?_⟩
    rw [← zero_add (t • x), ← zero_add (t • x'), I_lin hT p c (zero_mem _) (le mx.1), I_lin hT p c (zero_mem _) (le hx), ex]

end GlobalTheory.ThK.Dbl

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.CuspLift
section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.PolZero
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem I_left {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {om : Rep σ X W} {Φ : Fn F n d}
    (h : ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ g h, theta om Φ (γ * g) (γ' * h) = theta om Φ g h) :
    ∀ γ ∈ ratU σ W.J, ∀ x, M.I om Φ (γ * x) = M.I om Φ x := fun γ hγ x => by
  unfold Model.I
  have e : ∀ g, theta om Φ g (γ * x) = theta om Φ g x := fun g => by simpa only [one_mul] using h 1 (one_mem _) γ hγ g x
  simp only [e]

theorem swap_bdd {A B : Type} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
    [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B] (μ : Measure A) (ν : Measure B)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {f : A × B → ℂ} (c : Continuous f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    ∫ a, ∫ b, f (a, b) ∂ν ∂μ = ∫ b, ∫ a, f (a, b) ∂μ ∂ν :=
  integral_integral_swap (f := fun a b => f (a, b)) (Integrable.of_bound c.aestronglyMeasurable C (Eventually.of_forall hC))

theorem int_th {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {om : Rep σ X W} {Ψ : Fn F n d}
    (cX : Cpt σ X.J) (cW : Cpt σ W.J) (h1 : M.μ.IsHaarMeasure) (h2 : IsFundamentalDomain (ratU σ X.J) M.dom M.μ)
    {μ : Measure (UA σ W.J)} {D : Set (UA σ W.J)} (hμ : μ.IsHaarMeasure) (hD : IsFundamentalDomain (ratU σ W.J) D μ)
    (hc : Continuous fun x : UA σ X.J × UA σ W.J => theta om Ψ x.1 x.2)
    (hi : ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ g h, theta om Ψ (γ * g) (γ' * h) = theta om Ψ g h)
    {φ : UA σ W.J → ℂ} (pc : Continuous φ) (pi : ∀ γ ∈ ratU σ W.J, ∀ g, φ (γ * g) = φ g) :
    ∫ g in M.dom, th om μ D φ Ψ g ∂M.μ = pet μ D φ (M.I om Ψ) := by
  haveI := cX.sc; haveI := cW.sc
  haveI : IsFiniteMeasure (M.μ.restrict M.dom) := isFiniteMeasure_restrict.2 (cX.fin _ _ h1 h2).ne
  haveI : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.2 (cW.fin _ _ hμ hD).ne
  have c : Continuous fun x : UA σ X.J × UA σ W.J => φ x.2 * star (theta om Ψ x.1 x.2) := (pc.comp continuous_snd).mul hc.star
  obtain ⟨C, hC⟩ := cX.bdd₂ cW c fun γ hγ δ hδ g g' => by simp only [pi δ hδ, hi γ hγ δ hδ]
  unfold th pet Model.I
  refine (swap_bdd _ _ c hC).trans <| integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [integral_const_mul]
  exact congrArg _ integral_conj

theorem polZero_of (hC : CptAll) (hH : HermLine) (hL : CoefLine) (hT : ThConst) (hN : NonZeroAn) (hM : MatchEx)
    (hB : ThetaBasic) (hI : PositivityTheory.ThKF.ICont) (hP : PolSch) : PolZero := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf h hp hq
  have t := h.triple
  have cW := hC F E σ B _ G.W _ _ t.base (Or.inr t.geo.hW) (by omega)
  have cV := hC F E σ B _ G.V' _ _ t.base (Or.inl t.geo.hV') (by omega)
  obtain ⟨μ, D, hμ, hD⟩ := cW.ex
  obtain ⟨m1, m2, m3⟩ := hM F E σ B a a' G X om om' R Rf h
  have b1 := (hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t)).1
  have b2 := (hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' t)).1
  have s1 : ∀ y ∈ pairs B G X R Rf, y.1 ∈ schA F _ := fun y hy =>
    hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t) _ (m3 _ _ hy.1 hy.2).1
  have s2 : ∀ y ∈ pairs B G X R Rf, y.2 ∈ schA F _ := fun y hy =>
    hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' t) _ (m3 _ _ hy.1 hy.2).2.1
  have c1 := (hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t)).1 (Or.inr (by omega))
  have c2 := (hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' t)).1 (Or.inr (by omega))
  have cc : ∀ s u, ∀ y ∈ pairs B G X R Rf, Continuous (comb G om om' s u y) := fun s u y hy =>
    ((c1 _ (s1 y hy)).const_smul s).add ((c2 _ (s2 y hy)).const_smul u)
  have ci : ∀ s u, ∀ y ∈ pairs B G X R Rf, ∀ γ ∈ ratU σ G.W.J, ∀ g, comb G om om' s u y (γ * g) = comb G om om' s u y g :=
    fun s u y hy γ hγ g => by
      simp only [comb, Pi.add_apply, Pi.smul_apply, I_left G.M (b1 _ (s1 y hy)).2.1 γ hγ, I_left G.M' (b2 _ (s2 y hy)).2.1 γ hγ]
  have e01 : ∀ y, comb G om om' 0 1 y = G.M'.I om' y.2 := fun y => by simp [comb]
  haveI : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.2 (cW.fin _ _ hμ hD).ne
  have ig : ∀ s u s' u', ∀ y ∈ pairs B G X R Rf, ∀ y' ∈ pairs B G X R Rf,
      Integrable (fun g => comb G om om' s u y g * star (comb G om om' s' u' y' g)) (μ.restrict D) := fun s u s' u' y hy y' hy' => by
    have c := (cc s u y hy).mul (cc s' u' y' hy').star
    obtain ⟨C, hC⟩ := cW.bdd c fun γ hγ g => by
      change comb G om om' s u y (γ * g) * star (comb G om om' s' u' y' (γ * g)) =
        comb G om om' s u y g * star (comb G om om' s' u' y' g)
      rw [ci s u y hy γ hγ, ci s' u' y' hy' γ hγ]
    exact Integrable.of_bound c.aestronglyMeasurable C (Eventually.of_forall hC)
  obtain ⟨c, hc⟩ := hH F E σ B a a' G X om om' R Rf h hp hq μ D hμ hD 1 0 0 1
  have orth : ∀ y ∈ pairs B G X R Rf, pet μ D (comb G om om' 1 (-c) y) (comb G om om' 0 1 y) = 0 := fun y hy => by
    have e : pet μ D (comb G om om' 1 (-c) y) (comb G om om' 0 1 y) =
        pet μ D (comb G om om' 1 0 y) (comb G om om' 0 1 y) - c * pet μ D (comb G om om' 0 1 y) (comb G om om' 0 1 y) := by
      unfold pet
      rw [← integral_const_mul, ← integral_sub (ig _ _ _ _ y hy y hy) ((ig _ _ _ _ y hy y hy).const_mul c)]
      refine integral_congr_ae (Eventually.of_forall fun g => ?_)
      simp only [comb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, hc y hy y hy, sub_self]
  obtain ⟨lam, hl⟩ := hH F E σ B a a' G X om om' R Rf h hp hq μ D hμ hD 1 (-c) 1 (-c)
  obtain ⟨⟨Φ₀, q1, q2⟩, Φ', r1, r2⟩ := And.imp (fun f => f hp) (fun f => f hq) (hN F E σ B a a' G X om om' t)
  obtain ⟨Φ, hΦ⟩ := m2 Φ' r1.1
  have hy : (Φ, Φ') ∈ pairs B G X R Rf := ⟨r1.2, hΦ⟩
  have v0 := cV.vol_ne t.geo.hM'.haar t.geo.hM'.dom
  have key : ∀ s u, th om' μ D (comb G om om' s u (Φ, Φ')) Φ' =
      fun _ => pet μ D (comb G om om' s u (Φ, Φ')) (comb G om om' 0 1 (Φ, Φ')) / (G.M'.μ.real G.M'.dom : ℂ) := fun s u => by
    have k := (hT F E σ B a a' G X om om' R Rf h s u (fun y hy => cW.rapid (cc s u y hy) (ci s u y hy)) μ D hμ hD _ hy).2 Φ'
      (s2 _ hy)
    have i := int_th G.M' cV cW t.geo.hM'.haar t.geo.hM'.dom hμ hD (b2 _ (s2 _ hy)).1 (b2 _ (s2 _ hy)).2.1 (cc s u _ hy) (ci s u _ hy)
    simp only [k, setIntegral_const, Complex.real_smul] at i
    funext g
    rw [k, e01, ← i, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.2 v0)]
  have n0 : pet μ D (comb G om om' 0 1 (Φ, Φ')) (comb G om om' 0 1 (Φ, Φ')) ≠ 0 := fun h0 =>
    r2 (e01 (Φ, Φ') ▸ cW.eq_zero hμ hD (cc 0 1 _ hy) (ci 0 1 _ hy) h0)
  have l0 : lam = 0 := by
    have := hL F E σ B a a' G X om om' R Rf h hp hq μ D hμ hD 1 (-c) lam hl _ hy Φ' r1.1
    rw [key, key, orth _ hy] at this
    generalize pet μ D (comb G om om' 0 1 (Φ, Φ')) (comb G om om' 0 1 (Φ, Φ')) = x at this n0
    simpa [pet, n0, v0] using this
  have main : PolConst B G X om om' R Rf c := fun Ψ Ψ' h1 h2 g => by
    have hz : (Ψ, Ψ') ∈ pairs B G X R Rf := ⟨h1, h2⟩
    have := congrFun (cW.eq_zero hμ hD (cc 1 (-c) _ hz) (ci 1 (-c) _ hz) (by rw [hl _ hz _ hz, l0, zero_mul])) g
    simp only [comb, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    linear_combination this
  refine ⟨c, fun c0 => q2 (funext fun g => ?_), main⟩
  obtain ⟨Ψ', h1, h2⟩ := m1 Φ₀ q1
  rw [main Φ₀ Ψ' h1 h2 g, c0, zero_mul]; rfl

end GlobalTheory.ThK.Dbl

end
end

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKEnd (unipU IsCusp)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem IsRapid.bound {φ : UA σ Y.J → ℂ} (hφ : IsRapid φ) (h1 : ∀ h : UA σ Y.J, 1 ≤ ht h) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (T : UA σ Y.J → ℂ) (A : ℝ), 0 ≤ A → (∀ γ ∈ ratU σ Y.J, ∀ h, T (γ * h) = T h) →
      (∀ h, ‖T h‖ ≤ A * (ht h : ℝ) ^ N) → ∀ h, ‖T h‖ * ‖φ h‖ ≤ A * M := by
  obtain ⟨C, hC⟩ := hφ.2.2 N
  refine ⟨2 ^ N * max C 0, by positivity, fun T A hA hi hb h => ?_⟩
  have q1 : 1 ≤ qht h := le_ciInf fun γ => h1 _
  obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt (f := fun γ : ratU σ Y.J => ht (γ.1 * h)) (b := 2 * qht h)
    (lt_two_mul_self (zero_lt_one.trans_le q1))
  calc _ ≤ A * (2 * qht h : ℝ) ^ N * ‖φ h‖ := mul_le_mul_of_nonneg_right (hi γ γ.2 h ▸ (hb _).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) (by exact_mod_cast hγ.le) N) hA)) (norm_nonneg _)
    _ = A * (2 ^ N * (‖φ h‖ * (qht h : ℝ) ^ N)) := by ring
    _ ≤ _ := by gcongr; exact (hC h).trans (le_max_left _ _)

variable {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} {χ : Chr F E} {s₀ : ℂ} {f : G2 σ Y → ℂ} {e : UA σ Y.J × UA σ Y.J →* G2 σ Y}

theorem eis_bound (he : ∀ h h', IsEmb h h' (e (h, h'))) {c : ℝ≥0} (h1 : ∀ h h' x, IsEmb (σ := σ) (Y := Y) h h' x → ht2 x ≤ c * (ht h * ht h'))
    (h2 : ∀ h : UA σ Y.J, 1 ≤ ht h) {φ : UA σ Y.J → ℂ} (hφ : IsRapid φ) (C : ℝ) (N : ℕ) (b : ℝ≥0) :
    ∃ M : ℝ, ∀ Ê : G2 σ Y → ℂ, (∀ c ∈ rat2 σ Y, ∀ x, Ê (c * x) = Ê x) → (∀ x, ‖Ê x‖ ≤ C * (ht2 x : ℝ) ^ N) →
      ∀ h, ht h ≤ b → ∀ h', ‖Ê (e (h, h'))‖ * ‖φ h'‖ ≤ M := by
  obtain ⟨M, -, hM⟩ := hφ.bound h2 N
  refine ⟨max C 0 * (c * b) ^ N * M, fun Ê hi hb h hh => hM (fun x => Ê (e (h, x))) _ (by positivity) (fun γ hγ x => ?_) fun x => ?_⟩
  · rw [← hi _ ((he 1 γ).rat (one_mem _) hγ) (e (h, x)), ← map_mul, Prod.mk_mul_mk, one_mul]
  · refine (hb _).trans ?_
    rw [mul_assoc, ← mul_pow]
    have : ht2 (e (h, x)) ≤ c * b * ht x := (h1 _ _ _ (he h x)).trans (by rw [mul_assoc]; gcongr)
    gcongr
    exacts [le_max_left _ _, by exact_mod_cast this]

theorem sfin {A : Type} [MeasurableSpace A] (μ : Measure A) [IsFiniteMeasure μ] : SFinite μ := inferInstance

theorem sfin' {A : Type} [Group A] [TopologicalSpace A] [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A]
    (μ : Measure A) [μ.IsHaarMeasure] : SFinite μ := inferInstance

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem ct_zero (hO : OffOpen) (hU : PositivityTheory.ThKEnd.Grp.UnipUGood) (hE1 : EisContinues) (hH : HtEmb) {B : Base F E} {r s : ℕ}
    (hB : B.IsGood σ) (hn : 1 ≤ n) (hY : Y.IsSkew σ B r s) (d0 : Y.J.det ≠ 0) [LocallyCompactSpace (UA σ Y.J)]
    [SecondCountableTopology (UA σ Y.J)] [T2Space (UA σ Y.J)] (hb : ∀ Ω : Set (UA σ Y.J), IsCompact Ω → ∃ C : ℝ≥0, ∀ g ∈ Ω, ht g ≤ C)
    (hχ : IsHecke F E χ) (he : ∀ h h', IsEmb h h' (e (h, h'))) (ce : Continuous e) (hS : IsStab2 B K)
    (hK : IsCompact (K : Set (G2 σ Y))) (ha : IsHgt K a) (ca : Continuous a) (a0 : ∀ x, 0 < a x) (cf : Continuous f)
    (hf : Law χ (s₀ + n / 2) f) {U Ê} (hE : IsEisCont (flat a f s₀) U Ê) {μ : Measure (UA σ Y.J)} {D : Set (UA σ Y.J)}
    (hμ : μ.IsHaarMeasure) (hD : IsFundamentalDomain (ratU σ Y.J) D μ) (fin : μ D < ⊤) {t₀ : ℝ}
    (hi : ∀ t, t₀ ≤ t → Integrable (fun g => a (e (1, g)) ^ t) μ) {φ : UA σ Y.J → ℂ} (hφ : IsRapid φ) (hc : IsCusp Y φ) :
    ∀ s ∈ U, IsCusp Y fun h => ∫ h' in D, Ê s (e (h, h')) * detInv χ h' * φ h' ∂μ := by
  intro s hs V v1 v2 κ 𝓜 k1 k2 h
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨g, -⟩ := hU F E σ hB.cm n Y (.inr hY.skew) d0 V
  haveI := g.sc
  haveI : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.2 fin.ne
  haveI : IsFiniteMeasure (κ.restrict 𝓜) := isFiniteMeasure_restrict.2 (g.fin κ 𝓜 k1 k2).2.ne
  haveI : SFinite (μ.restrict D) := sfin _
  haveI : SFinite (κ.restrict 𝓜) := sfin _
  haveI : SFinite μ := sfin' μ
  obtain ⟨c, c1, -, c3⟩ := hH F E σ n Y
  obtain ⟨t₁, half⟩ := hE.half
  have cE : ∀ s ∈ U, Continuous (Ê s) := fun s hs =>
    hE.cont.comp_continuous (f := fun x => (s, x)) (by fun_prop) fun _ => ⟨hs, trivial⟩
  have iv : ∀ s ∈ U, ∀ γ ∈ rat2 σ Y, ∀ x, Ê s (γ * x) = Ê s x := fun s hs γ hγ x =>
    An.ident hE.isOpen hE.conn (hE.hol _) (hE.hol _) (fun s hs => ⟨(half s hs).1,
      (hf.flat ha a0 s).eis_rat hχ (half s hs).2 hγ _⟩) hs
  obtain ⟨Ω, hΩ, cov⟩ := g.cov
  obtain ⟨b, hb'⟩ := hb _ ((hΩ.image continuous_subtype_val).image (continuous_mul_const h))
  let k : ℂ → unipU σ Y V × UA σ Y.J → ℂ := fun s y => Ê s (e (y.1.1 * h, y.2)) * detInv χ y.2 * φ y.2
  have ck : ∀ s ∈ U, Continuous (k s) := fun s hs =>
    (((cE s hs).comp (ce.comp (by fun_prop))).mul ((continuous_detInv hχ).comp continuous_snd)).mul (hφ.1.comp continuous_snd)
  have bk : ∀ s ∈ U, ∃ ε > 0, ∃ M, ∀ s' ∈ U ∩ Metric.ball s ε, ∀ y, ‖k s' y‖ ≤ M := fun s hs => by
    obtain ⟨ε, C, N, h0, hg⟩ := hE.grow s hs
    obtain ⟨M, hM⟩ := eis_bound he c1 c3 hφ C N b
    refine ⟨ε, h0, M, fun s' hs' y => ?_⟩
    obtain ⟨γ, hγ, h1⟩ := cov y.1
    have := hM (Ê s') (iv s' hs'.1) (hg s' hs'.2) _ (hb' _ ⟨_, ⟨_, h1, rfl⟩, rfl⟩) y.2
    rw [show e ((γ * y.1).1 * h, y.2) = e (γ.1, 1) * e (y.1.1 * h, y.2) by simp [← map_mul, mul_assoc],
      iv s' hs'.1 _ ((he _ _).rat hγ (one_mem _))] at this
    simpa only [k, norm_mul, norm_detInv, mul_one] using this
  have ik : ∀ s ∈ U, Integrable (k s) ((κ.restrict 𝓜).prod (μ.restrict D)) := fun s hs => by
    obtain ⟨ε, h0, M, hM⟩ := bk s hs
    exact .of_bound (ck s hs).aestronglyMeasurable M (.of_forall (hM s ⟨hs, Metric.mem_ball_self h0⟩))
  have hol : DifferentiableOn ℂ (fun s => ∫ y, k s y ∂(κ.restrict 𝓜).prod (μ.restrict D)) U := fun s hs => by
    obtain ⟨ε, h0, M, hM⟩ := bk s hs
    have o := hE.isOpen.inter (Metric.isOpen_ball (x := s) (ε := ε))
    exact ((An.diffOn_integral o (fun s hs => (ck s hs.1).aestronglyMeasurable)
      (fun y => (((hE.hol _).mul_const _).mul_const _).mono Set.inter_subset_left) fun S hS _ =>
        ⟨M, fun s hs => hM s (hS hs)⟩).differentiableAt (o.mem_nhds ⟨hs, Metric.mem_ball_self h0⟩)).differentiableWithinAt
  have l1 : Law (1 : Chr F E) ((0 : ℂ) + n / 2) fun x => (a x : ℂ) ^ ((0 : ℂ) + n / 2) := fun p t x hp => by
    beta_reduce
    rw [ha.mul hp, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (absE_pos _).le (a0 x).le]; simp
  have h1 : IsHecke F E (1 : Chr F E) := ⟨continuous_const, fun _ => rfl⟩
  obtain ⟨U₁, Ê₁, hE₁, -⟩ := hE1 F E σ B n Y r _ hB hn (.inr hY) 1 h1 0 (fun x => by simp only [pow_zero, ite_self]; rfl) K a hS ha 0 (fun x => (a x : ℂ) ^ ((0 : ℂ) + n / 2))
    ⟨(Complex.continuous_ofReal.comp ca).cpow continuous_const fun x => Complex.ofReal_mem_slitPlane.2 (a0 x), l1, by
      refine FiniteDimensional.span_of_finite ℂ ((Set.finite_singleton fun x => (a x : ℂ) ^ ((0 : ℂ) + n / 2)).subset ?_)
      rintro _ ⟨k, rfl⟩
      refine funext fun x => ?_
      obtain ⟨p, t, hp, k', hk', rfl⟩ := ha.iwa x
      show (a _ : ℂ) ^ _ = (a _ : ℂ) ^ _
      simp only [mul_assoc, ha.val p t hp _ (mul_mem hk' k.2), ha.val p t hp _ hk']⟩
  obtain ⟨t₂, half₁⟩ := hE₁.half
  rw [← integral_prod (k s) (ik s hs)]
  refine An.ident hE.isOpen hE.conn hol (differentiableOn_const 0) (t := max (max t₁ t₂) (t₀ - n / 2)) (fun s hs => ?_) hs
  have s1 := (le_max_left _ _).trans_lt hs
  obtain ⟨u, sm⟩ := half s ((le_max_left _ _).trans_lt s1)
  have cs := continuous_flat (s₀ := s₀) cf ca a0 s
  obtain ⟨C, hC⟩ := (hf.flat (s₀ := s₀) ha a0 s).bound cs ha hK
  have ez : (s - s₀ + (s₀ + n / 2)).re = s.re + n / 2 := by simp; ring
  rw [ez] at hC
  have i1 : Integrable (fun g => flat a f s₀ s (e (1, g))) μ :=
    ((hi (s.re + n / 2) (by have := (le_max_right _ _).trans_lt hs; linarith)).const_mul C).mono'
      (cs.comp (ce.comp (Continuous.prodMk_right 1))).aestronglyMeasurable (.of_forall fun g => hC _)
  have i2 := i1.mul_bdd (continuous_detInv hχ).aestronglyMeasurable (.of_forall fun g => (norm_detInv χ g).le)
  obtain ⟨u₁, sm₁⟩ := half₁ (s.re : ℂ) (by simpa using (le_max_right _ _).trans_lt s1)
  obtain ⟨ε, C₁, N, h0, hg⟩ := hE₁.grow _ u₁
  have hfin : ∀ x, ∑' q : Cos σ Y, ∫⁻ y in D, ‖eisTerm (flat a f s₀ s) (e (x, y)) q * detInv χ y * φ y‖ₑ ∂μ ≠ ⊤ := fun x => by
    obtain ⟨M, hM⟩ := eis_bound he c1 c3 hφ C₁ N (ht x)
    have hM' := hM _ (fun c hc => (l1.flat ha a0 _).eis_rat h1 sm₁ hc) (hg _ (Metric.mem_ball_self h0)) x le_rfl
    haveI : Countable (Cos σ Y) := by
      exact Set.countable_univ_iff.1 ((sm₁ 1).summable.countable_support.mono fun q _ => mul_ne_zero
        (Complex.cpow_ne_zero_iff.2 (.inl (Complex.ofReal_ne_zero.2 (a0 _).ne')))
        (Complex.cpow_ne_zero_iff.2 (.inl (Complex.ofReal_ne_zero.2 (a0 _).ne'))))
    rw [← lintegral_tsum (f := fun q y => ‖eisTerm (flat a f s₀ s) (e (x, y)) q * detInv χ y * φ y‖ₑ) fun q => (((cs.comp (continuous_const.mul (ce.comp (Continuous.prodMk_right x)))).mul
      (continuous_detInv hχ)).mul hφ.1).measurable.enorm.aemeasurable]
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in D, ENNReal.ofReal (max C 0 * M) ∂μ)
      (by rw [setLIntegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top fin.ne) (lintegral_mono fun y => ?_)
    have t1 : ∀ q : Cos σ Y, eisTerm (flat a (fun x => (a x : ℂ) ^ ((0 : ℂ) + n / 2)) 0 (s.re : ℂ)) (e (x, y)) q =
        ((a (q.out.1 * e (x, y)) ^ (s.re + n / 2) : ℝ) : ℂ) := fun q => by
      rw [eisTerm, flat, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 (a0 _).ne'), Complex.ofReal_cpow (a0 _).le]
      congr 1; push_cast; ring
    have t2 : HasSum (fun q : Cos σ Y => a (q.out.1 * e (x, y)) ^ (s.re + n / 2)) (Ê₁ s.re (e (x, y))).re := by
      simpa only [t1, Complex.ofReal_re] using Complex.hasSum_re (sm₁ (e (x, y)))
    have p0 : ∀ q : Cos σ Y, 0 ≤ max C 0 * (a (q.out.1 * e (x, y)) ^ (s.re + n / 2) * ‖φ y‖) := fun q => by
      have := Real.rpow_nonneg (a0 (q.out.1 * e (x, y))).le (s.re + n / 2); positivity
    have t3 := (t2.mul_right ‖φ y‖).mul_left (max C 0)
    refine (ENNReal.tsum_le_tsum fun q => ?_).trans ((ENNReal.ofReal_tsum_of_nonneg p0 t3.summable).symm.le.trans
      (ENNReal.ofReal_le_ofReal ?_))
    · rw [← ofReal_norm_eq_enorm, norm_mul, norm_mul, norm_detInv, mul_one, ← mul_assoc]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ((hC _).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (a0 _).le _))) (norm_nonneg _))
    · rw [t3.tsum_eq]
      exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right (Complex.re_le_norm _) (norm_nonneg _)).trans (hM' y))
        (le_max_right _ _)
  refine ⟨u, ?_⟩
  rw [integral_prod (k s) (ik s u)]
  simp only [k, fun x => unfoldC hO hU hB hY d0 hχ he ce cs (hf.flat ha a0 s) sm hμ hD i1 hφ hc x (hfin x)]
  obtain ⟨b₀, hb₀⟩ := hφ.2.2 0
  rw [integral_integral_swap (f := fun (m : unipU σ Y V) g => flat a f s₀ s (e (1, g)) * detInv χ g * φ (m.1 * h * g))
    ((i2.comp_snd _).mul_bdd (c := b₀) (hφ.1.comp (by fun_prop)).aestronglyMeasurable
      (.of_forall fun y => by simpa using hb₀ (y.1.1 * h * y.2)))]
  simp only [integral_const_mul, mul_assoc _ h, hc V v1 v2 κ 𝓜 k1 k2, mul_zero, integral_zero]

end GlobalTheory.ThK.Dbl

end
end

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open PositivityTheory.ThKEnd (unipU IsCusp Perp)

structure OrthIn : Prop where
  sw : SWFull
  box : BoxSec
  dbl : DblW
  hgt : HgtEx
  int : HgtInt
  cpt : Stab2Cpt
  eis : EisContinues
  off : OffOpen
  emb : HtEmb
  unip : PositivityTheory.ThKEnd.Grp.UnipUGood
  line : PositivityTheory.ThKEnd.Grp.UnipLine
  all : CptAll
  top : PositivityTheory.ThKEst.GrpTop
  eps : PositivityTheory.ThKEst.EpsOf
  vol : PositivityTheory.ThKEst.FinVolU
  basic : ThetaBasic
  arch : PositivityTheory.ThKF.ArchOp
  conj : PositivityTheory.ThKF.CartanConj
  move : PositivityTheory.ThKF.CartanMove
  levi : LeviEx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χ χ' : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}
private lemma exists_poly_height_bound_theta_of_min_eq_zero (I : OrthIn) (p : IsPair B M χ χ' om r s r' s') (h0 : min r s = 0) {Φ : Fn F n d}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ g h, ‖theta om Φ g h‖ ≤ C * (ht h : ℝ) ^ k := by
  obtain ⟨-, hinv, C, k, hb⟩ := (I.basic F E σ B n d X W M χ χ' om r s r' s' p).1 Φ hΦ
  have hcpt : Cpt σ X.J := I.all F E σ B n X r s p.base (Or.inl p.herm) h0
  obtain ⟨Ω, hΩ, hcov⟩ := hcpt.cov
  have hepsX := (I.eps F E σ B p.base n X r s (Or.inl p.herm)).1
  obtain ⟨C₀, hC₀⟩ := (I.top F E σ p.base.cm n X.J hepsX).2.2.2.2.2.2.2 Ω hΩ
  refine ⟨|C| * (C₀ : ℝ) ^ k, k, by positivity, fun g h => ?_⟩
  obtain ⟨γ, hγ, hγΩ⟩ := hcov g
  have e1 : theta om Φ g h = theta om Φ (γ * g) h := by
    have h3 := hinv γ hγ 1 (one_mem _) g h
    rw [one_mul] at h3
    exact h3.symm
  have h4 : (ht (γ * g) : ℝ) ≤ C₀ := by exact_mod_cast hC₀ _ hγΩ
  rw [e1]
  calc ‖theta om Φ (γ * g) h‖ ≤ C * ((ht (γ * g) : ℝ) * (ht h : ℝ)) ^ k := hb _ _
    _ ≤ |C| * ((ht (γ * g) : ℝ) * (ht h : ℝ)) ^ k :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * ((C₀ : ℝ) * (ht h : ℝ)) ^ k := by gcongr
    _ = |C| * (C₀ : ℝ) ^ k * (ht h : ℝ) ^ k := by rw [mul_pow, mul_assoc]

private lemma integral_integral_swap_of_bounded_continuous [SecondCountableTopology (UA σ W.J)] [SecondCountableTopology (UA σ X.J)]
    {μ : Measure (UA σ W.J)} {D : Set (UA σ W.J)} (hfin : μ D < ⊤) (hfin2 : M.μ M.dom < ⊤)
    {f : UA σ W.J → UA σ X.J → ℂ} (hf : Continuous (Function.uncurry f)) {C : ℝ}
    (hC : ∀ h g, ‖f h g‖ ≤ C) :
    ∫ h in D, ∫ g in M.dom, f h g ∂M.μ ∂μ = ∫ g in M.dom, ∫ h in D, f h g ∂μ ∂M.μ := by
  have : IsFiniteMeasure (μ.restrict D) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have : IsFiniteMeasure (M.μ.restrict M.dom) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin2⟩
  have : SFinite (μ.restrict D) := GlobalTheory.ThK.Dbl.sfin _
  have : SFinite (M.μ.restrict M.dom) := GlobalTheory.ThK.Dbl.sfin _
  apply MeasureTheory.integral_integral_swap
  exact Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => hC q.1 q.2)

theorem cusp_lift (I : OrthIn) (p : IsPair B M χ χ' om r s r' s') (h0 : min r s = 0) (hn : 1 ≤ n) (hd : 1 ≤ d)
    {φ : UA σ W.J → ℂ} (hφ : IsRapid φ) (hc : IsCusp W φ) {μ : Measure (UA σ W.J)} {D : Set (UA σ W.J)} (hμ : μ.IsHaarMeasure)
    (hD : IsFundamentalDomain (ratU σ W.J) D μ) {Φ₂ : Fn F n d} (h2 : Φ₂ ∈ PolData B M)
    (hth : ∀ g, th om μ D φ Φ₂ g = th om μ D φ Φ₂ 1) (hne : ∫ h in D, M.I om Φ₂ h * starRingEnd ℂ (φ h) ∂μ ≠ 0)
    {Φ₁ : Fn F n d} (h1 : Φ₁ ∈ PolData B M) : IsCusp W (M.I om Φ₁) := by
  have hB := p.base
  have hskew := p.skew
  have hepsW := (I.eps F E σ B hB d W r' s' (Or.inr hskew)).1
  have htopW := I.top F E σ hB.cm d W.J hepsW
  have : LocallyCompactSpace (UA σ W.J) := htopW.1
  have : SecondCountableTopology (UA σ W.J) := htopW.2.1
  have : T2Space (UA σ W.J) := htopW.2.2.1
  have hepsX := (I.eps F E σ B hB n X r s (Or.inl p.herm)).1
  have htopX := I.top F E σ hB.cm n X.J hepsX
  have : SecondCountableTopology (UA σ X.J) := htopX.2.1
  have hcpt : Cpt σ X.J := I.all F E σ B n X r s hB (Or.inl p.herm) h0
  have hfinD : μ D < ⊤ := I.vol F E σ hB.cm d W.J hepsW μ D hμ hD
  have hfinX : M.μ M.dom < ⊤ := hcpt.fin M.μ M.dom p.good.haar p.good.dom
  obtain ⟨⟨K, a, hS, ha, ca, a0⟩, e, ce, he⟩ := I.hgt F E σ B d W r' s' hB (Or.inr hskew)
  obtain ⟨t₀, hi⟩ := I.int F E σ B d W r' s' hB (Or.inr hskew) K a e hS ha he μ hμ
  have hK := I.cpt F E σ B d W r' s' hB (Or.inr hskew) K hS
  obtain ⟨-, -, -, ht1⟩ := I.emb F E σ d W
  obtain ⟨dd, om₂, S, l, hdbl, hbox, hcoord, -⟩ := I.dbl F E σ B n d X W M χ χ' om r s r' s' p
  have hsch1 := GlobalTheory.ThK.Dbl.pol_sch p.good h1
  have hsch2 := GlobalTheory.ThK.Dbl.pol_sch p.good h2
  obtain ⟨U, Ê, hEis, hs₀, hval⟩ := I.sw F E σ B n d X W M r s r' s' hB hn hd p.herm h0 hskew p.good χ p.hX
    p.resX dd om₂ S l hcoord hdbl K a hS ha Φ₁ h1 Φ₂ h2
  have hsec := I.box F E σ B n d X W M r s r' s' hB hn hd p.herm h0 hskew p.good χ p.hX p.resX dd om₂ S l
    hcoord hdbl K a hS ha Φ₁ h1 Φ₂ h2
  have hcE := GlobalTheory.ThK.Dbl.ct_zero I.off I.unip I.eis I.emb hB hd hskew hepsW.2 htopW.2.2.2.2.2.2.2 p.hX he ce
    hS hK ha ca a0 hsec.cont hsec.law hEis hμ hD hfinD hi hφ hc _ hs₀
  obtain ⟨C₁, k₁, hC₁0, hb₁⟩ := exists_poly_height_bound_theta_of_min_eq_zero I p h0 hsch1
  obtain ⟨C₂, k₂, hC₂0, hb₂⟩ := exists_poly_height_bound_theta_of_min_eq_zero I p h0 hsch2
  obtain ⟨Mφ, hMφ0, hMφ⟩ := hφ.bound ht1 k₂
  have hbasic1 := (I.basic F E σ B n d X W M χ χ' om r s r' s' p).1 Φ₁ hsch1
  have hbasic2 := (I.basic F E σ B n d X W M χ χ' om r s r' s' p).1 Φ₂ hsch2
  have hθφ : ∀ g h', ‖theta om Φ₂ g h'‖ * ‖φ h'‖ ≤ C₂ * Mφ := fun g h' =>
    hMφ (fun h' => theta om Φ₂ g h') C₂ hC₂0 (fun γ hγ h'' => by
      have h3 := hbasic2.2.1 1 (one_mem _) γ hγ g h''
      rw [one_mul] at h3
      exact h3) (fun h'' => hb₂ g h'') h'
  have hc2 : ∀ g, ∫ h in D, theta om Φ₂ g h * starRingEnd ℂ (φ h) ∂μ
      = starRingEnd ℂ (th om μ D φ Φ₂ 1) := by
    intro g
    rw [← hth g]
    unfold GlobalTheory.ThK.Dbl.th GlobalTheory.ThK.Dbl.pet
    rw [← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    beta_reduce
    rw [map_mul, starRingEnd_apply (star _), star_star, mul_comm]
  have hcont2 : Continuous (Function.uncurry fun (h : UA σ W.J) (g : UA σ X.J) =>
      theta om Φ₂ g h * starRingEnd ℂ (φ h)) := by
    show Continuous fun q : UA σ W.J × UA σ X.J => theta om Φ₂ q.2 q.1 * starRingEnd ℂ (φ q.1)
    exact (hbasic2.1.comp continuous_swap).mul (Complex.continuous_conj.comp (hφ.1.comp continuous_fst))
  have hbd2 : ∀ (h : UA σ W.J) (g : UA σ X.J), ‖theta om Φ₂ g h * starRingEnd ℂ (φ h)‖ ≤ C₂ * Mφ :=
    fun h g => by
      rw [norm_mul, RCLike.norm_conj]
      exact hθφ g h
  have hne' : ∫ h in D, M.I om Φ₂ h * starRingEnd ℂ (φ h) ∂μ
      = ((M.μ M.dom).toReal : ℂ) * starRingEnd ℂ (th om μ D φ Φ₂ 1) := by
    have e2 : ∀ h, M.I om Φ₂ h * starRingEnd ℂ (φ h)
        = ∫ g in M.dom, theta om Φ₂ g h * starRingEnd ℂ (φ h) ∂M.μ := fun h => by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.I
      rw [integral_mul_const]
    simp_rw [e2]
    rw [integral_integral_swap_of_bounded_continuous hfinD hfinX hcont2 hbd2]
    simp_rw [hc2]
    rw [setIntegral_const, Complex.real_smul]
    rfl
  have hv_th : ((M.μ M.dom).toReal : ℂ) ≠ 0 ∧ th om μ D φ Φ₂ 1 ≠ 0 := by
    have h5 := hne
    rw [hne'] at h5
    exact ⟨left_ne_zero_of_mul h5, fun h0' => h5 (by rw [h0', map_zero, mul_zero])⟩
  have hmain : ∀ h, ∫ h' in D, Ê ((↑n - ↑d) / 2) (e (h, h')) * detInv χ h' * φ h' ∂μ
      = (if d < n then (1 : ℂ) else 2) * ((M.μ M.dom).toReal : ℂ)⁻¹ * th om μ D φ Φ₂ 1 * M.I om Φ₁ h := by
    intro h
    have hpt : ∀ h' g, GlobalTheory.WeilM.thetaSum F ((om₂ (e (h, h'))) ((S g) (GlobalTheory.WeilM.boxFun Φ₁ (star Φ₂))))
        * detInv χ h' = theta om Φ₁ g h * star (theta om Φ₂ g h') := fun h' g => by
      rw [mul_comm]
      exact ((hbox Φ₁ hsch1 Φ₂ hsch2).2 g h h' _ (he h h')).1
    have e1 : ∀ h', Ê ((↑n - ↑d) / 2) (e (h, h')) * detInv χ h' * φ h'
        = (if d < n then (1 : ℂ) else 2) * ((M.μ M.dom).toReal : ℂ)⁻¹
          * ∫ g in M.dom, theta om Φ₁ g h * star (theta om Φ₂ g h') * φ h' ∂M.μ := by
      intro h'
      have e3 : ∫ g in M.dom, theta om Φ₁ g h * star (theta om Φ₂ g h') * φ h' ∂M.μ
          = (∫ g in M.dom, GlobalTheory.WeilM.thetaSum F ((om₂ (e (h, h'))) ((S g) (GlobalTheory.WeilM.boxFun Φ₁ (star Φ₂))))
            ∂M.μ) * detInv χ h' * φ h' := by
        rw [← integral_mul_const, ← integral_mul_const]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        beta_reduce
        rw [hpt h' g]
      have hr : M.μ.real M.dom = (M.μ M.dom).toReal := rfl
      rw [hval, MeasureTheory.setAverage_eq, Complex.real_smul, e3]
      try rw [hr]
      push_cast
      ring
    have hcont1 : Continuous (Function.uncurry fun (h' : UA σ W.J) (g : UA σ X.J) =>
        theta om Φ₁ g h * star (theta om Φ₂ g h') * φ h') := by
      show Continuous fun q : UA σ W.J × UA σ X.J => theta om Φ₁ q.2 h * star (theta om Φ₂ q.2 q.1) * φ q.1
      exact ((hbasic1.1.comp (continuous_snd.prodMk continuous_const)).mul
        ((hbasic2.1.comp continuous_swap).star)).mul (hφ.1.comp continuous_fst)
    have hbd1 : ∀ (h' : UA σ W.J) (g : UA σ X.J),
        ‖theta om Φ₁ g h * star (theta om Φ₂ g h') * φ h'‖ ≤ C₁ * (ht h : ℝ) ^ k₁ * (C₂ * Mφ) := by
      intro h' g
      rw [mul_assoc, norm_mul, norm_mul, norm_star]
      exact mul_le_mul (hb₁ g h) (hθφ g h') (by positivity) (mul_nonneg hC₁0 (by positivity))
    simp_rw [e1]
    rw [integral_const_mul, integral_integral_swap_of_bounded_continuous hfinD hfinX hcont1 hbd1]
    have e4 : ∀ g, ∫ h' in D, theta om Φ₁ g h * star (theta om Φ₂ g h') * φ h' ∂μ
        = theta om Φ₁ g h * th om μ D φ Φ₂ 1 := by
      intro g
      rw [← hth g]
      simp_rw [mul_assoc]
      rw [integral_const_mul]
      congr 1
      unfold GlobalTheory.ThK.Dbl.th GlobalTheory.ThK.Dbl.pet
      simp_rw [mul_comm (star _)]
    simp_rw [e4]
    rw [integral_mul_const]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.I
    ring
  have hκ : (if d < n then (1 : ℂ) else 2) * ((M.μ M.dom).toReal : ℂ)⁻¹ * th om μ D φ Φ₂ 1 ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ (inv_ne_zero hv_th.1)) hv_th.2
    split_ifs <;> norm_num
  intro U' hU' hiso μ' 𝓕 hμ' h𝓕 h''
  have h7 := hcE U' hU' hiso μ' 𝓕 hμ' h𝓕 h''
  simp only [hmain] at h7
  rw [integral_const_mul] at h7
  exact (mul_eq_zero.mp h7).resolve_left hκ
private lemma evFin_eq_zero_of_At_evI {κ : Type} (z : κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)
    (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z) (v : Pl F) (i : κ) :
    GlobalTheory.AdelicU.evFin F v (z i) = 0 := by
  have h1 := hz ((0, 1) : NumberField.InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
    (by
      show (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : NumberField.InfiniteAdeleRing F) = 0
      exact map_zero _)
  have h3 : (z i).2 = 0 := by
    have h4 : ((0, 1) : NumberField.InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F).2 * (z i).2
        = 0 := congrArg Prod.snd (congrFun h1 i)
    simpa using h4
  show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (z i).2 = 0
  rw [h3]
  exact map_zero _

theorem cusp_re (I : OrthIn) (p : IsPair B M χ χ' om r s r' s') (h0 : min r s = 0) (X₂ : Spc F E n) (W₂ : Spc F E d)
    (p₂ : IsPair B (X := reS X X₂) (W := reS W W₂) ⟨M.co, M.vac, M.μ, M.dom⟩ χ χ' om r s r' s')
    (hc : ∀ Φ ∈ PolData B M, IsCusp W (M.I om Φ)) {Φ : Fn F n d}
    (hΦ : Φ ∈ PolData B (σ := σ) (X := reS X X₂) (W := reS W W₂) ⟨M.co, M.vac, M.μ, M.dom⟩) : IsCusp W (M.I om Φ) := by
  obtain ⟨h, hh, hθ⟩ := I.conj F E σ B d W W₂ r' s' p.base p.skew p₂.skew
  obtain ⟨g, hg, -, hT⟩ := I.move F E σ B n d X W M χ χ' om r s r' s' p X₂ W₂ ⟨M.co, M.vac, M.μ, M.dom⟩ rfl p₂
    h hh hθ
  obtain ⟨T, hTa, -⟩ := I.arch F E σ B n d X W M χ χ' om r s r' s' p g hg h hh
  have hmapT := hT T hTa
  have hsch : ∀ Ψ ∈ PolData B (σ := σ) (X := reS X X₂) (W := reS W W₂) ⟨M.co, M.vac, M.μ, M.dom⟩,
      Ψ ∈ schA F (Fin n × Fin d) := fun Ψ hΨ => GlobalTheory.ThK.Dbl.pol_sch p₂.good hΨ
  have hgen : ∀ Ψ ∈ PolData B (σ := σ) (X := reS X X₂) (W := reS W W₂) ⟨M.co, M.vac, M.μ, M.dom⟩,
      (om (g, h)) Ψ ∈ PolData B M := by
    intro Ψ hΨ
    unfold GlobalTheory.ThK.PolData at hΨ
    induction hΨ using Submodule.span_induction with
    | mem x hx =>
      have hxs := hsch x (Submodule.subset_span hx)
      obtain ⟨f, hf, φ, hφ, hv, rfl⟩ := hx
      have hrest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (⇑f)
          (fun x => ∏ᶠ v, φ v fun i => GlobalTheory.AdelicU.evFin F v (x i)) := by
        refine ⟨fun x z hz => ?_, hxs⟩
        simp only [Pi.add_apply, map_add (f := _), evFin_eq_zero_of_At_evI z hz, add_zero]
      have h2 : (om (g, h)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (T f) φ := hTa.2 f _ hrest
      rw [h2]
      exact Submodule.subset_span ⟨T f, by rw [← hmapT]; exact Submodule.mem_map_of_mem hf, φ, hφ, hv, rfl⟩
    | zero =>
      rw [map_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul]
      exact Submodule.smul_mem _ a hx
  have hΦs := hsch Φ hΦ
  have hΨ := hc _ (hgen Φ hΦ)
  have hcpt : GlobalTheory.ThK.Dbl.Cpt σ X.J := I.all F E σ B n X r s p.base (Or.inl p.herm) h0
  have hI : M.I om ((om (g, h)) Φ) = fun h' => M.I om Φ (h' * h) := by
    have e1 : (g, h) = ((1 : UA σ X.J), h) * (g, 1) := by simp
    funext h'
    rw [e1, map_mul, Module.End.mul_apply, ← GlobalTheory.ThK.Dbl.I_act I.basic p hcpt hΦs g]
    have e2 : ∀ g' : UA σ X.J, (om (g', h')) ((om (1, h)) ((om (g, 1)) Φ)) = (om (g', h' * h)) ((om (g, 1)) Φ) :=
      fun g' => by rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.I, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta, e2]
  have key : IsCusp W (fun h' => M.I om Φ (h' * h)) := by
    rw [← hI]
    exact hΨ
  intro U hU hiso μ 𝓕 hμ h𝓕 h''
  have h9 := key U hU hiso μ 𝓕 hμ h𝓕 (h'' * h⁻¹)
  simpa [mul_assoc] using h9

theorem isCT_of_cusp (I : OrthIn) (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) {d₁ i₀ i₁ : ℕ} {W₁ : Spc F E d₁} (hW₁ : W₁.IsSkew σ B r' s')
    {H : Plane E d d₁} (hH : H.IsAdapted σ B W W₁ i₀ i₁) {f : UA σ W.J → ℂ} (hf : IsCusp W f) : IsCT H f 0 := by
  have hW₁d : W₁.J.det ≠ 0 := (I.eps F E σ B hB d₁ W₁ r' s' (Or.inr hW₁)).1.2
  have hP : PositivityTheory.ThKEnd.IsPlane σ H W W₁ := ⟨hH.rank, hH.xx, hH.yy, hH.xy, hH.orth, hH.gram, hW₁d⟩
  have hEq := I.line F E σ hB.cm d d₁ W W₁ H (Or.inr hW.skew) hP
  have hx : H.x ≠ 0 := by
    intro hx
    have h1 := hH.xy
    rw [hx] at h1
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form] at h1
  have hU : (E ∙ H.x) ≠ ⊥ := by
    rwa [Ne, Submodule.span_singleton_eq_bot]
  have hiso : ∀ u ∈ (E ∙ H.x), ∀ u' ∈ (E ∙ H.x), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ W.J u u' = 0 := by
    intro u hu u' hu'
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hu'
    have h0 := hH.xx
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form] at h0 ⊢
    have hs : (fun i => σ ((b • H.x) i)) = σ b • fun i => σ (H.x i) := by
      ext i
      simp [map_mul]
    rw [hs, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, h0]
    simp
  let P (N : Subgroup (UA σ W.J)) : Prop :=
    ∀ (μ : Measure N) (𝓕 : Set N), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ W.J).subgroupOf N) 𝓕 μ → μ 𝓕 = 1 →
        ∀ h, (0 : UA σ W.J → ℂ) h = ∫ u in 𝓕, f (u.1 * h) ∂μ
  change P (unip σ W H)
  rw [hEq]
  dsimp only [P]
  intro μ 𝓕 hμ h𝓕 _ h
  rw [Pi.zero_apply]
  exact (hf _ hU hiso μ 𝓕 hμ h𝓕 h).symm
private lemma isHecke_div_and_resEtaPow_div (α β : Chr F E) (m m' : ℕ) (K : Subgroup (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)ˣ)
    (hα : GlobalTheory.LFun.IsHecke F E α) (hβ : GlobalTheory.LFun.IsHecke F E β)
    (rα : GlobalTheory.WeilM.ResEtaPow K α m') (rβ : GlobalTheory.WeilM.ResEtaPow K β m) :
    GlobalTheory.LFun.IsHecke F E (β / α) ∧ GlobalTheory.WeilM.ResEtaPow K (β / α) (m + m') := by
  refine ⟨⟨hβ.1.div' hα.1, fun x => ?_⟩, fun u => ?_⟩
  · rw [MonoidHom.div_apply, hα.2 x, hβ.2 x, div_one]
  · rw [MonoidHom.div_apply, Circle.coe_div, rα u, rβ u]
    split_ifs
    · simp
    · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg, inv_one]

private lemma isPair_and_isPair_of_isTriple {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (T : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) ∧
      IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) := by
  obtain ⟨base, geo, chars, weil, weil'⟩ := T
  have h1 := isHecke_div_and_resEtaPow_div X.α X.β a a' _ chars.heckeα chars.heckeβ chars.resα chars.resβ
  have h2 := isHecke_div_and_resEtaPow_div X.β X.α a' a _ chars.heckeβ chars.heckeα chars.resβ chars.resα
  refine ⟨⟨base, geo.hV, geo.hW, geo.hM, chars.heckeβ, h1.1, chars.resβ, h1.2, weil⟩,
    ⟨base, geo.hV', geo.hW, geo.hM', chars.heckeα, h2.1, chars.resα, ?_, weil'⟩⟩
  rw [Nat.add_comm]
  exact h2.2

private lemma exists_trace_zero_generator_of_isCMExt (I : OrthIn) (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) {d₁ i₀ i₁ : ℕ} {W₁ : Spc F E d₁}
    (hW₁ : W₁.IsSkew σ B r' s') {H : Plane E d d₁} (hH : H.IsAdapted σ B W W₁ i₀ i₁)
    {f c c' : UA σ W.J → ℂ} (hc : IsCT H f c) (hc' : IsCT H f c') : c = c' := by
  have hW₁d : W₁.J.det ≠ 0 := (I.eps F E σ B hB d₁ W₁ r' s' (Or.inr hW₁)).1.2
  have hWd : W.J.det ≠ 0 := (I.eps F E σ B hB d W r s (Or.inr hW)).1.2
  have hP : PositivityTheory.ThKEnd.IsPlane σ H W W₁ := ⟨hH.rank, hH.xx, hH.yy, hH.xy, hH.orth, hH.gram, hW₁d⟩
  have hEq := I.line F E σ hB.cm d d₁ W W₁ H (Or.inr hW.skew) hP
  obtain ⟨μ, 𝓕, h1, h2, h3⟩ := (I.unip F E σ hB.cm d W (Or.inr hW.skew) hWd (E ∙ H.x)).1.ex
  let P (N : Subgroup (UA σ W.J)) (g : UA σ W.J → ℂ) : Prop :=
    ∀ (μ : Measure N) (𝓕 : Set N), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ W.J).subgroupOf N) 𝓕 μ → μ 𝓕 = 1 →
        ∀ h, g h = ∫ u in 𝓕, f (u.1 * h) ∂μ
  change P (unip σ W H) c at hc
  change P (unip σ W H) c' at hc'
  rw [hEq] at hc hc'
  dsimp only [P] at hc hc'
  funext h
  rw [hc μ 𝓕 h1 h2 h3 h, hc' μ 𝓕 h1 h2 h3 h]

theorem orthAn_of (I : OrthIn) (hR : PositivityTheory.ThKEnd.Orth.SigRapid) (hT : PositivityTheory.ThKEnd.Orth.SigThConst) (hN : NonZeroAn)
    (hA : TowerA) (hB : TowerB) (hE : EvZero) (hC : CTBigZero) (hC' : CTSmallZero) : PositivityTheory.ThKEnd.OrthAn := by
  intro F E _ _ _ _ _ σ B a a' G X om om' T f hf hc
  have hpair := isPair_and_isPair_of_isTriple T
  have hr := hR F E σ B a a' G X om om' T f hf hc
  have hG := T.geo
  refine ⟨fun hp hq Φ hΦ => ?_, fun hq hp Φ' hΦ' => ?_⟩
  · intro μ 𝓕 hμ h𝓕
    by_contra hne
    have hth := (hT F E σ B a a' G X om om' T f hf hr μ 𝓕 hμ h𝓕).1 Φ (GlobalTheory.ThK.Dbl.pol_sch hG.hM hΦ)
    have hcusp : ∀ Φ₁ ∈ GlobalTheory.ThK.PolData B G.M, IsCusp G.W (G.M.I om Φ₁) := fun Φ₁ hΦ₁ =>
      cusp_lift I hpair.1 (by simp [hp]) (by have := hG.lt; omega) (by have := hG.lt; omega) hr hc hμ h𝓕
        hΦ hth hne hΦ₁
    obtain ⟨b, rfl⟩ : ∃ b, a' = b + 2 := ⟨a' - 2, by have := hG.aBig; omega⟩
    obtain ⟨V, V', W, T', G₁, H, H', cfg, om₁, om₁', T₁⟩ := hB F E σ B a b G X om om' T hq
    have hpair' := isPair_and_isPair_of_isTriple T'
    have hcR : ∀ Ψ ∈ GlobalTheory.ThK.PolData B (GlobalTheory.ThK.reG G V V' W).M,
        IsCusp (GlobalTheory.ThK.reG G V V' W).W ((GlobalTheory.ThK.reG G V V' W).M.I om Ψ) := fun Ψ hΨ =>
      cusp_re I hpair.1 (by simp [hp]) V W hpair'.1 hcusp hΨ
    obtain ⟨⟨e, hev⟩, hmap⟩ := hE F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hpair'.1 _ _ _ H' _ _ G₁.M cfg.eV cfg.hH'
      T₁.geo.hM
    obtain ⟨C, hC0, hCT⟩ := hC F E σ B a b _ G₁ H H' cfg e hev
    obtain ⟨Φ₁, hΦ₁, hne₁⟩ := (hN F E σ B a b G₁ X om₁ om₁' T₁).1 (by rw [cfg.ep]; exact hp)
    rw [← hmap e hev] at hΦ₁
    obtain ⟨Ψ, hΨ, rfl⟩ := Submodule.mem_map.mp hΦ₁
    apply hne₁
    funext h₁
    obtain ⟨m, hm⟩ := I.levi F E σ B _ _ _ _ H' _ _ _ _ T.base T'.geo.hW cfg.hH' h₁
    have hct0 : IsCT H' ((GlobalTheory.ThK.reG G V V' W).M.I om Ψ) 0 :=
      isCT_of_cusp I T.base T'.geo.hW T₁.geo.hW cfg.hH' (hcR Ψ hΨ)
    have hsplit : GlobalTheory.ThK.Split2 G₁.W H' X ((GlobalTheory.ThK.reG G V V' W).M.I om Ψ) 0 0 :=
      ⟨by rw [add_zero]; exact hct0, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩
    have h5 := hCT X om om' om₁ om₁' T' T₁ Ψ hΨ 0 0 hsplit h₁ m hm 1
    rw [Prod.mk_one_one] at h5
    have h7 : ((om : Rep σ (GlobalTheory.ThK.reG G V V' W).V (GlobalTheory.ThK.reG G V V' W).W) 1) Ψ = Ψ := by
      rw [map_one]
      rfl
    have h8 := (mul_eq_zero.mp (h5.symm.trans (Pi.zero_apply _))).resolve_left hC0
    rw [Pi.zero_apply]
    exact (congrArg (fun t => G₁.M.I om₁ (e t) h₁) h7.symm).trans h8
  · intro μ 𝓕 hμ h𝓕
    by_contra hne
    have hΦ'p := (Submodule.mem_inf.mp hΦ').1
    have hth := (hT F E σ B a a' G X om om' T f hf hr μ 𝓕 hμ h𝓕).2 Φ' (GlobalTheory.ThK.Dbl.pol_sch hG.hM' hΦ'p)
    have hcusp : ∀ Φ₁ ∈ GlobalTheory.ThK.PolData B G.M', IsCusp G.W (G.M'.I om' Φ₁) := fun Φ₁ hΦ₁ =>
      cusp_lift I hpair.2 (by simp [hq]) (by have := hG.aBig; omega) (by have := hG.aBig; omega) hr hc hμ
        h𝓕 hΦ'p hth hne hΦ₁
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by have := hG.aBig; have := hG.lt; omega⟩
    obtain ⟨V, V', W, T', G₁, H, H', cfg, om₁, om₁', T₁⟩ := hA F E σ B b a' G X om om' T hq hp
    have hpair' := isPair_and_isPair_of_isTriple T'
    have hcR : ∀ Ψ ∈ GlobalTheory.ThK.PolData B (GlobalTheory.ThK.reG G V V' W).M',
        IsCusp (GlobalTheory.ThK.reG G V V' W).W ((GlobalTheory.ThK.reG G V V' W).M'.I om' Ψ) := fun Ψ hΨ =>
      cusp_re I hpair.2 (by simp [hq]) V' W hpair'.2 hcusp hΨ
    obtain ⟨⟨e, hev⟩, hmap⟩ := hE F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hpair'.2 _ _ _ H' _ _ G₁.M' cfg.eV cfg.hH'
      T₁.geo.hM'
    obtain ⟨C, hC0, hCT⟩ := hC' F E σ B b a' _ G₁ H H' cfg e hev
    obtain ⟨Φ₁, hΦ₁, hne₁⟩ := (hN F E σ B b a' G₁ X om₁ om₁' T₁).2 cfg.q1
    have hΦ₁p := (Submodule.mem_inf.mp hΦ₁).1
    rw [← hmap e hev] at hΦ₁p
    obtain ⟨Ψ, hΨ, rfl⟩ := Submodule.mem_map.mp hΦ₁p
    apply hne₁
    funext h₁
    obtain ⟨m, hm⟩ := I.levi F E σ B _ _ _ _ H' _ _ _ _ T.base T'.geo.hW cfg.hH' h₁
    have hct0 : IsCT H' ((GlobalTheory.ThK.reG G V V' W).M'.I om' Ψ) 0 :=
      isCT_of_cusp I T.base T'.geo.hW T₁.geo.hW cfg.hH' (hcR Ψ hΨ)
    obtain ⟨fa, hsp, hlaw⟩ := hCT X om om' om₁ om₁' T' T₁ Ψ hΨ
    have hfa : fa = 0 := by
      have h6 := exists_trace_zero_generator_of_isCMExt I T.base T'.geo.hW T₁.geo.hW cfg.hH' hsp.1 hct0
      simpa using h6
    have h5 := hlaw h₁ m hm 1
    rw [hfa, Prod.mk_one_one] at h5
    have h7 : ((om' : Rep σ (GlobalTheory.ThK.reG G V V' W).V' (GlobalTheory.ThK.reG G V V' W).W) 1) Ψ = Ψ := by
      rw [map_one]
      rfl
    have h8 := (mul_eq_zero.mp (h5.symm.trans (Pi.zero_apply _))).resolve_left hC0
    rw [Pi.zero_apply]
    exact (congrArg (fun t => G₁.M'.I om₁' (e t) h₁) h7.symm).trans h8

end GlobalTheory.ThK.Dbl

end
