module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HermitianCodeWordWeilElementMemQuadraticField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteOrbitsOfFiniteFibres
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvSmulMemOfRedL
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfOpenCompact
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubConjEqNeg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGramSchmidtIndefiniteHermitianFrames

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram
noncomputable section

namespace GlobalTheory.Mem.Col2.StepZero

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.HLatOps
open scoped ComplexOrder

section Metric

variable {K : Type} [Field K] [NumberField K] [StarRing K] (C : CSD K)

@[reducible] def valDatum : GSD K where
  G := Unit
  D := Unit
  V := C.V
  ιV := C.ιV
  bV := C.bV
  pair := C.pair
  ρ := 1
  Nab _ := ⊥
  Del _ := ⊥

theorem majAt_eq_classSum (hb : C.HasRatBasis) (hp : ∀ v : InfinitePlace K, (C.H.map v.embedding).PosDef)
    (v : InfinitePlace K) (x y : C.Forms) :
    Formalism.HermitianLatticesTheory.majAt C.basis (stdFrame C.H) v x y =
      ∑ c, ((C.wt c : ℕ) : ℂ)⁻¹ * (valDatum C).pairAt v (x.1 c) (y.1 c) := by
  have hs : IsSesq (fun v (x y : C.Forms) => ∑ c, ((C.wt c : ℕ) : ℂ)⁻¹ * (valDatum C).pairAt v (x.1 c) (y.1 c)) := by
    intro v
    refine ⟨fun x x' y => ?_, fun x y y' => ?_, fun a x y => ?_, fun a x y => ?_⟩
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← mul_add, ← GSD.pairAt_add_left]
      rfl
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← mul_add, ← GSD.pairAt_add_right]
      rfl
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [mul_left_comm, ← GSD.pairAt_smul_left]
      rfl
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [mul_left_comm, ← GSD.pairAt_smul_right]
      rfl
  have hg : gramOf C.basis (fun (x y : C.Forms) => ∑ c, ((C.wt c : ℕ) : ℂ)⁻¹ * (valDatum C).pairAt v (x.1 c) (y.1 c)) =
      C.H.map v.embedding := by
    ext a a'
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [gramOf, Matrix.of_apply, Matrix.map_apply, CSD.H, CSD.csum, map_sum, map_mul, map_inv₀, map_natCast]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    exact ((valDatum C).pairAt_of_rat v _ _ fun i => C.basis_rat hb a c i).symm
  rw [sesq_eq_sum (isSesq_maj C.basis (stdFrame C.H)) C.basis v x y, sesq_eq_sum hs C.basis v x y, gramOf_maj, hg]
  have := (frameOfSpec _ _ (hp v)).2
  unfold metOf at this
  unfold stdFrame
  rw [this]

end Metric

section Forget

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
  {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q}
  (pref : DecoF X.E n ST SG Q → Prop) (lam : X.Tau → DomWeight n) {Λ₀ : LevFam X.E X.K n SG}


variable (ST Λ₀) in
abbrev base : GSD X.K := formGSD (roundPk X lam fun d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) => d.1.Lsh) Λ₀

def down (hΛ : ∀ b, Λ b = Λ₀) (b : β) : (stepY ST y β Λ Θ pref).G b →* FormG Λ₀ where
  toFun g := (g.1, ⟨g.2.1.1, hΛ b ▸ g.2.1.2⟩)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem deco_smul (hΛ : ∀ b, Λ b = Λ₀) (b : β) (g : (stepY ST y β Λ Θ pref).G b) (p : (stepY ST y β Λ Θ pref).D b) :
    (g • p).1.1.deco = down pref hΛ b g • p.1.1.deco := rfl

theorem chr_eq_one {Θ' : LevQFam X.E X.K n Q} (h : Θ' = LevQFam.top X.E X.K n Q) (c : Θ'.grp) : Θ'.chr c = 1 := by
  subst h
  exact LevQFam.top_chr c

theorem mem_grp {Θ' : LevQFam X.E X.K n Q} (h : Θ' = LevQFam.top X.E X.K n Q) (c : GLQ X.E n Q) : c ∈ Θ'.grp := by
  subst h
  exact (Subgroup.mem_pi _).2 fun _ _ => Subgroup.mem_top _

theorem chr_congr {Λ' : LevFam X.E X.K n SG} (h : Λ' = Λ₀) (a : Λ'.grp) : Λ'.chr a = Λ₀.chr ⟨a.1, h ▸ a.2⟩ := by
  subst h
  rfl

theorem rho_eq (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (b : β) (g : (stepY ST y β Λ Θ pref).G b) :
    (stepY ST y β Λ Θ pref).rho X.emb lam b g = (base ST lam Λ₀).ρ (down pref hΛ b g) := by
  have h : (stepY ST y β Λ Θ pref).chr b g = Λ₀.chr (down pref hΛ b g).2 := by
    show (Λ b).chr g.2.1 * (Θ b).chr g.2.2 = _
    rw [chr_eq_one (hΘ b), mul_one, chr_congr (hΛ b)]
    rfl
  show (((stepY ST y β Λ Θ pref).chr b g : X.Kˣ) : X.K) • rhoVr X.emb lam ((stepY ST y β Λ Θ pref).gam b g) = _
  rw [h]
  rfl

theorem form_smul (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (φ : (base ST lam Λ₀).EqFun) (b : β)
    (g : (stepY ST y β Λ Θ pref).G b) (p : (stepY ST y β Λ Θ pref).D b) :
    φ.1 (g • p).1.1.deco = (stepY ST y β Λ Θ pref).rho X.emb lam b g (φ.1 p.1.1.deco) := by
  rw [rho_eq pref lam hΛ hΘ]
  exact φ.2 (down pref hΛ b g) p.1.1.deco

theorem pt_ext (hy : ∀ N, y.ys N = {∅}) {p q : PtY ST SG Q y} (h : p.1.1 = q.1.1) : p = q := by
  have h1 := p.2
  have h2 := q.2
  rw [hy, Set.mem_singleton_iff] at h1 h2
  exact Subtype.ext (Prod.ext h (h1.trans h2.symm))

theorem exists_lift (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (b : β)
    (p q : (stepY ST y β Λ Θ pref).D b) (g₀ : FormG Λ₀) (h : g₀ • p.1.1.deco = q.1.1.deco) :
    ∃ g : (stepY ST y β Λ Θ pref).G b, down pref hΛ b g = g₀ ∧ g • p = q := by
  obtain ⟨c, hc⟩ := GlobalTheory.FramedForms.exists_smul_of_deco_eq
    (p := ((g₀.1, g₀.2.1, 1) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • p.1.1) (q := q.1.1) h
  refine ⟨(g₀.1, ⟨g₀.2.1, (hΛ b).symm ▸ g₀.2.2⟩, ⟨c, mem_grp (hΘ b) c⟩), rfl, pt_ext hy ?_⟩
  rw [hc, smul_smul]
  simp only [Prod.mk_mul_mk, one_mul, mul_one]
  rfl

theorem exists_pt (hy : ∀ N, y.ys N = {∅}) (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) : ∃ p : PtY ST SG Q y, p.1.1.deco = d := by
  obtain ⟨γ, -, hγ⟩ := GlobalTheory.SemilocalBasis.exists_equiv X.E n Q d.1.N
    { toIsLattice := d.2.lat
      span_eq_top := GlobalTheory.LvT.Pts.span_eq_top_of_unimodular d.1.N d.2.lat d.2.uni }
  exact ⟨⟨(⟨(d, fun _ => γ), fun P x => hγ P.1 P.2 x⟩, ∅), by rw [hy]; rfl⟩, rfl⟩

theorem card_stab (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (b : β)
    (p : (stepY ST y β Λ Θ pref).D b) :
    Nat.card (MulAction.stabilizer ((stepY ST y β Λ Θ pref).G b) p) =
      Nat.card (MulAction.stabilizer (FormG Λ₀) p.1.1.deco) := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun g => ⟨down pref hΛ b g.1, (deco_smul pref hΛ b g.1 p).symm.trans (congrArg (fun q => q.1.1.deco) g.2)⟩) ⟨?_, ?_⟩)
  · intro g g' h
    have h1 : g.1.1 = g'.1.1 := congrArg (fun a => a.1.1) h
    have h2 : (g.1⁻¹ * g'.1) = 1 := stepY_eq_one y β Λ Θ pref b _ p (g⁻¹ * g').2 (by
      show g.1.1⁻¹ * g'.1.1 = 1
      rw [h1, inv_mul_cancel])
    exact Subtype.ext (inv_mul_eq_one.1 h2)
  · intro g₀
    obtain ⟨g, h1, h2⟩ := exists_lift pref hy hΛ hΘ b p p g₀.1 g₀.2
    exact ⟨⟨g, h2⟩, Subtype.ext h1⟩

def clMap (c : (stepY ST y β Λ Θ pref).Cl) : (base ST lam Λ₀).Cl :=
  (base ST lam Λ₀).cls ((stepY ST y β Λ Θ pref).rep c).1.1.deco

theorem clMap_cl (hΛ : ∀ b, Λ b = Λ₀) (b : β) (p : (stepY ST y β Λ Θ pref).D b) :
    clMap (Λ₀ := Λ₀) pref lam ((stepY ST y β Λ Θ pref).cl b p) = (base ST lam Λ₀).cls p.1.1.deco := by
  conv_rhs => rw [← (stepY ST y β Λ Θ pref).mv_smul b p, deco_smul pref hΛ]
  exact ((base ST lam Λ₀).cls_smul _ _).symm

theorem clMap_bijective [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀)
    (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) :
    Function.Bijective (clMap (y := y) (Λ := Λ) (Θ := Θ) (Λ₀ := Λ₀) pref lam) := by
  refine ⟨?_, fun c₀ => ?_⟩
  · rintro ⟨b, q⟩ ⟨b', q'⟩ h
    obtain rfl : b = b' := Subsingleton.elim _ _
    obtain ⟨g₀, hg⟩ := ((base ST lam Λ₀).cls_eq_iff _ _).1 h
    obtain ⟨g, -, h2⟩ := exists_lift pref hy hΛ hΘ b _ _ g₀ hg
    congr 1
    rw [← (stepY ST y β Λ Θ pref).rp_spec b q, ← (stepY ST y β Λ Θ pref).rp_spec b q']
    exact Quotient.sound ⟨g, h2⟩
  · induction c₀ using Quotient.inductionOn' with
    | h d =>
      obtain ⟨p, rfl⟩ := exists_pt (Q := Q) hy d
      exact ⟨(stepY ST y β Λ Θ pref).cl default p, clMap_cl pref lam hΛ default p⟩

def clEquiv [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) :
    (stepY ST y β Λ Θ pref).Cl ≃ (base ST lam Λ₀).Cl :=
  Equiv.ofBijective _ (clMap_bijective pref lam hy hΛ hΘ)

end Forget

section Zero

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ} (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word)

theorem m_pos (R : Ranks) : 0 < R.m := lt_of_lt_of_le (by norm_num) R.two_le_m

variable (sel mu cst) in
theorem ysAt_zero (N : Submodule (𝓞 X.E) (Sp X.E (R.N 0))) : (ysAt R sel mu cst 0).ys N = {∅} := by
  have h : ¬ (0 + 1 = R.m) := by have := R.two_le_m; omega
  unfold ysAt
  rw [if_neg h]
  rfl

@[reducible] def idxUnique (hL : L.Ok Ch sel mu cst G m2) : Unique (Idx sel mu L 0) where
  default := ⟨some hL.zero_uniq.choose, by simpa using m_pos R⟩
  uniq := by
    rintro ⟨_ | b, hb⟩
    · exact absurd (hb.2 (m_pos R)) (by simp)
    · exact Subtype.ext (congrArg some (hL.zero_uniq.choose_spec b))

theorem levGAt_zero (hL : L.Ok Ch sel mu cst G m2) (b : Idx sel mu L 0) : levGAt sel mu L Tp 0 b = colLev Ch 0 := by
  obtain ⟨_ | b, hb⟩ := b
  · exact absurd (hb.2 (m_pos R)) (by simp)
  · exact hL.zero_G b

theorem levQAt_zero (hL : L.Ok Ch sel mu cst G m2) (b : Idx sel mu L 0) :
    levQAt sel mu L Tp 0 b = LevQFam.top X.E X.K (R.N 0) _ := by
  obtain ⟨_ | b, hb⟩ := b
  · exact absurd (hb.2 (m_pos R)) (by simp)
  · exact hL.zero_Q b

variable (hX : X.Ok) (hL : L.Ok Ch sel mu cst G m2) (h : ((stepAt sel mu cst L Tp u 0).fam X.emb (lamT (W.hc u) 0)).Ok)

variable (rho : ∀ i (b : Idx sel mu L i), (stepAt sel mu cst L Tp u i).D b → ℂ)
  (rho' : ∀ i (b : Idx sel mu L (i + 1)), (stepAt sel mu cst L Tp u (i + 1)).D b → ℂ) (cD : X.Tau → ℂ)
  (Th : ∀ i (b : Idx sel mu L i) (b' : Idx sel mu L (i + 1)), (stepAt sel mu cst L Tp u i).D b →
    (stepAt sel mu cst L Tp u (i + 1)).D b' → Formalism.L2.Ker.VCx X.Tau (R.N i) (R.N (i + 1)) → ℂ)
  (xi0 : X.E) (du : ℕ) (Ds Gp : ℝ) (σ : X.K →+* ℂ)

theorem embF_injective {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]
    {n : ℕ} (T : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) (h : (T.fam emb lam).Ok) :
    Function.Injective (T.embF emb σ lam h) :=
  inj_of_li σ _ (T.hlat emb lam h).b (T.lawBasis_of_ok emb σ lam h).1

theorem embF_mem_Fi {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]
    {n : ℕ} (T : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) (h : (T.fam emb lam).Ok)
    (x : T.FormsK emb lam h) : T.embF emb σ lam h x ∈ T.Fi emb σ lam := by
  rw [← (T.lawBasis_of_ok emb σ lam h).2]
  exact mem_span_basis_image σ (T.hlat emb lam h).b _ x

end Zero

end GlobalTheory.Mem.Col2.StepZero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EasyInputs
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.EasyInputs

theorem smAll (D : D7) : SmAll D := fun V S M τ => by
  obtain ⟨w, hw, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (GlobalTheory.GardingVec.sm_ne_bot D V S M τ)
  exact ⟨⟨w, hw⟩, by simpa using h0⟩

theorem dimOK (D : D7) : DimOK D := fun i σ ρ => GlobalTheory.Mem.WeylDimPos.dimK_kapAt_Wc_pos D i σ ρ

theorem cartanOK (D : D7) : CartanOK D := by
  refine ⟨fun V S M _ τ => GlobalTheory.Chain.VacVec.cart_isCartanInv M τ, fun V hs hp τ => ?_⟩
  have h := GlobalTheory.RepsObj.gramAt_posDef hp hs τ
  exact ⟨by simp, by simp, by simpa using h⟩

theorem spOK (D : D7) : SpOK D := by
  refine ⟨fun τ => Or.inl ?_, fun τ => Or.inl (D.X'_posDef τ)⟩
  have hm : D.R.m - 1 ≤ D.R.m := Nat.sub_le _ _
  show (D.sp.Y (min (D.R.m - 1) D.R.m)).sig τ = ((D.sp.Y (min (D.R.m - 1) D.R.m)).rank, 0)
  rw [min_eq_left hm, D.Y_sigval _ hm τ, D.sp.Y_rank _ hm, sigYD]
  have := D.R.two_le_m
  have h1 : (D.R.m - (D.R.m - 1)) / 2 = 0 := by omega
  rw [h1, Nat.sub_zero]

theorem selfDualOK (D : D7) : SelfDualOK D := by
  rintro V β Λ N ⟨-, hd, hN, h1, h2⟩
  have hM0 : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hL := (GlobalTheory.PlaceModel.isSelfDualC_latFrame V).1
  rw [← GlobalTheory.PlaceModel.coe_latFrame] at h1 h2
  refine ⟨⟨?_, ?_⟩, fun y => ?_⟩
  · let f : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) :=
      (LinearMap.lsmul D.host.E (Fin V.rank → D.host.E) (N : D.host.E)⁻¹).restrictScalars (𝓞 D.host.E)
    refine (hL.fg.map f).of_le fun x hx => ⟨_, h2 x hx, ?_⟩
    change (N : D.host.E)⁻¹ • ((N : D.host.E) • x) = x
    rw [smul_smul, inv_mul_cancel₀ hM0, one_smul]
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · rw [← GlobalTheory.SDFrameLattice.mem_dualL_iff, hd]


open scoped Pointwise in
theorem petAll (D : D7) : PetAll D := by
  intro V μ 𝓕 hμ h𝓕 F hc hl h0 hi
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall fun g => by positivity) hi]
  have hs : Function.support (fun g => ‖F g‖ ^ 2) = Function.support F := by
    ext g
    simp [Function.mem_support]
  rw [hs, pos_iff_ne_zero]
  intro hz
  have hinv : ∀ γ : GQ V, γ • Function.support F = Function.support F := fun γ => by
    ext g
    rw [Set.mem_smul_set_iff_inv_smul_mem, Function.mem_support, Function.mem_support]
    have : F (γ⁻¹ • g) = F g := hl _ (γ⁻¹).2 g
    rw [this]
  have hzero := h𝓕.measure_zero_of_invariant _ hinv hz
  exact (hc.isOpen_support.measure_pos μ (Function.support_nonempty_iff.2 h0)).ne' hzero

theorem easy_inputs : ∀ D : D7, CartanOK D ∧ SelfDualOK D ∧ SpOK D ∧ DimOK D ∧ PetAll D ∧ SmAll D := fun D =>
  ⟨cartanOK D, selfDualOK D, spOK D, dimOK D, petAll D, smAll D⟩

end GlobalTheory.Mem.EasyInputs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyExt
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.TrueGeo
namespace GlobalTheory.TrueGeoModel
variable {F : Type} [Field F] [NumberField F]

theorem nonempty_ext (v : HeightOneSpectrum (𝓞 F)) : Nonempty (Ext v) := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  let K := v.adicCompletion F
  have h1 : ‖FinitePlace.embedding v (algebraMap (𝓞 F) F a)‖ < 1 := (FinitePlace.norm_lt_one_iff_mem F v a).2 ha
  have h0 : FinitePlace.embedding v (algebraMap (𝓞 F) F a) ≠ 0 := by
    simpa using ha0
  letI : NontriviallyNormedField K := NontriviallyNormedField.ofNormNeOne ⟨_, h0, h1.ne⟩
  let L := AlgebraicClosure K
  letI : Algebra F L := ((algebraMap K L).comp (FinitePlace.embedding v)).toAlgebra
  let j : AlgebraicClosure F →ₐ[F] L := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let N := spectralMulAlgNorm K L
  let w : AbsoluteValue (AlgebraicClosure F) ℝ :=
    (MulRingNorm.mulRingNormEquivAbsoluteValue N.toMulRingNorm).comp (f := j.toRingHom) j.injective
  have hw (x) : w x = spectralNorm K L (j x) := rfl
  have hn (x y) : w (x + y) ≤ max (w x) (w y) := by
    rw [hw, hw, hw, map_add (f := _)]; exact isNonarchimedean_spectralNorm _ _
  refine ⟨⟨w, fun x => ?_, ⟨⟨⟨⟨⟨{x | w x ≤ 1}, ?_⟩, by simp⟩, ?_, by simp⟩, ?_⟩, ?_⟩, fun _ => Iff.rfl⟩⟩
  · rw [hw, j.commutes, ← FinitePlace.norm_embedding]
    exact spectralNorm_extends _
  · intro x y hx hy
    simp only [Set.mem_setOf_eq, map_mul] at *
    exact mul_le_one₀ hx (w.nonneg _) hy
  · intro x y hx hy
    exact (hn x y).trans (max_le hx hy)
  · intro x hx
    simpa using hx
  · intro x
    rcases le_total (w x) 1 with h | h
    · exact .inl h
    · refine .inr ?_
      change w x⁻¹ ≤ 1
      rw [map_inv₀]; exact inv_le_one_of_one_le₀ h

end GlobalTheory.TrueGeoModel
end
end

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ExtConj
variable {F : Type} [Field F] [NumberField F]

theorem valuation_lt_one_iff {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (y : AlgebraicClosure F) :
    e.O.valuation y < 1 ↔ e.w y < 1 := by
  rw [ReciprocityTheory.Gal.valuation_lt_one_iff', e.mem_O, e.mem_O, map_inv₀]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have h0 : 0 < e.w y := e.w.pos hy
    simp only [hy, false_or, not_le, one_lt_inv₀ h0]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

theorem lies_over {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (x : 𝓞 F) :
    e.O.valuation (algebraMap F (AlgebraicClosure F) (x : F)) < 1 ↔ x ∈ v.asIdeal := by
  rw [valuation_lt_one_iff, e.w_alg, ← FinitePlace.norm_embedding]
  exact FinitePlace.norm_lt_one_iff_mem F v x

theorem conj (v : HeightOneSpectrum (𝓞 F)) (e e' : Ext v) :
    ∃ g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, ∀ x, e'.w x = e.w (g x) := by
  obtain ⟨g, hg⟩ := ReciprocityTheory.Gal.exists_smul_eq_of_over (lies_over e) (lies_over e')
  refine ⟨g⁻¹, ?_⟩
  let u : AbsoluteValue (AlgebraicClosure F) ℝ :=
    e.w.comp (f := (g⁻¹ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F).toRingEquiv.toRingHom) (g⁻¹).injective
  have hu (x) : u x = e.w (g⁻¹ x) := rfl
  have he : u.IsEquiv e'.w := AbsoluteValue.isEquiv_iff_lt_one_iff.2 fun x => by
    rw [hu, ← valuation_lt_one_iff, ← valuation_lt_one_iff, ← hg, ReciprocityTheory.Gal.smul_valuation_lt_one_iff]
  obtain ⟨c, hc, hce⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 he
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have h1 : e'.w (algebraMap F _ (a : F)) < 1 := (valuation_lt_one_iff e' _).1 ((lies_over e' a).2 ha)
  have h0 : 0 < e'.w (algebraMap F _ (a : F)) := e'.w.pos (by simpa using ha0)
  have h2 : u (algebraMap F _ (a : F)) = e'.w (algebraMap F _ (a : F)) := by
    rw [hu, AlgEquiv.commutes, e.w_alg, e'.w_alg]
  have h3 := congrFun hce (algebraMap F _ (a : F))
  simp only [h2] at h3
  have hc1 : c = 1 := by
    have h4 := congrArg Real.log h3
    rw [Real.log_rpow h0] at h4
    have := (Real.log_neg h0 h1).ne
    exact mul_right_cancel₀ this (by rw [h4, one_mul])
  intro x
  rw [← hu, ← hce, hc1]
  simp

theorem factor {K : Type} [Field K] {X : Scheme.{0}} (y : Sp K ⟶ X) (x : X) (h : below y = x) :
    ∃ ψ : X.residueField x ⟶ CommRingCat.of K, Spec.map ψ ≫ X.fromSpecResidueField x = y := by
  subst h
  exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X y⟩

theorem below_comp {K : Type} [Field K] {X : Scheme.{0}} (x : X) (ψ : X.residueField x ⟶ CommRingCat.of K) :
    below (K := K) (Spec.map ψ ≫ X.fromSpecResidueField x) = x :=
  (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply x _)

theorem closed_point_geometric_fibres_finite {k K : Type} [Field k] [Field K] [Algebra k K] [IsAlgClosed K] {X : Scheme.{0}} (s : X ⟶ Sp k)
    [LocallyOfFiniteType s] (x : X) (hx : IsClosed ({x} : Set X)) :
    Nonempty {y : {y : Sp K ⟶ X // y ≫ s = spMap (algebraMap k K)} // below y.1 = x} ∧
      Finite {y : {y : Sp K ⟶ X // y ≫ s = spMap (algebraMap k K)} // below y.1 = x} := by
  have := isClosed_singleton_iff_isClosedImmersion.1 hx
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ s)
  have hfin : IsFinite (Spec.map φ) := by
    rw [hφ]
    exact isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 inferInstance
  letI : Algebra k (X.residueField x) := φ.hom.toAlgebra
  haveI : Module.Finite k (X.residueField x) := (IsFinite.SpecMap_iff φ).1 hfin
  have hP (ψ : X.residueField x →ₐ[k] K) :
      (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField x) ≫ s = spMap (algebraMap k K) := by
    have h : φ ≫ CommRingCat.ofHom ψ.toRingHom = CommRingCat.ofHom (algebraMap k K) :=
      CommRingCat.hom_ext ψ.comp_algebraMap
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    exact congrArg Spec.map h
  let P : (X.residueField x →ₐ[k] K) → {y : {y : Sp K ⟶ X // y ≫ s = spMap (algebraMap k K)} // below y.1 = x} :=
    fun ψ => ⟨⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField x, hP ψ⟩,
      below_comp x _⟩
  refine ⟨⟨P IsAlgClosed.lift⟩, Finite.of_surjective P ?_⟩
  rintro ⟨⟨y, hy⟩, hyx⟩
  obtain ⟨ψ, h⟩ := factor y x hyx
  have h2 : Spec.map (φ ≫ ψ) = Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [Spec.map_comp, hφ, ← Category.assoc, h]
    exact hy
  have h3 := Spec.map_injective h2
  exact ⟨⟨ψ.hom, fun a => congrArg (fun t => t.hom a) h3⟩, Subtype.ext (Subtype.ext h)⟩

theorem pts (Y : Var F) (x : Y.X) (hx : IsClosed ({x} : Set Y.X)) :
    Nonempty {y : AlgPt Y // below y.1 = x} ∧ Finite {y : AlgPt Y // below y.1 = x} :=
  closed_point_geometric_fibres_finite Y.str x hx

theorem main : ∀ (F : Type) [Field F] [NumberField F] , (∀ v : HeightOneSpectrum (𝓞 F), Nonempty (Ext v)) ∧ (∀ Y : Var F, ∀ x : Y.X, IsClosed ({x} : Set Y.X) → Nonempty {y : AlgPt Y // below y.1 = x} ∧ Finite {y : AlgPt Y // below y.1 = x}) ∧ ∀ (v : HeightOneSpectrum (𝓞 F)) (e e' : Ext v), ∃ g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, ∀ x, e'.w x = e.w (g x) :=
  fun _ _ _ => ⟨GlobalTheory.TrueGeoModel.nonempty_ext, pts, conj⟩

end GlobalTheory.TrueGeo.ExtConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeCongruenceInLevelCharacterOne
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeCongruenceInLevelCharacterOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.LevFinCong

variable {D : D7}

theorem finE_mem_UA (V : HSp D) (κ : GA D V) : finE V κ ∈ UA D.sp.cm V.gram := by
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  have := (GlobalTheory.Mass.swapPts (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram (π κ)).2
  rwa [GlobalTheory.Mass.coe_swapPts, hπ κ] at this

theorem isOpen_comap_Kg (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (T : Finset (Pl D.host.E)) :
    IsOpen ((((Kg D.sp.cm V.gram β T).comap
      ((Formalism.UG.bc (swapAE D)).comp (Bridge.Gf V).subtype)) : Subgroup (Bridge.Gf V)) : Set (Bridge.Gf V)) := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : IsTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) _
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have hc : Continuous ((Bridge.Gf V).subtype) := continuous_subtype_val
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ_mat β T hc (map_one _)] with x hh
  obtain ⟨h2, h3⟩ := hh
  obtain ⟨g, hg⟩ := x.2
  have h1 : Formalism.UG.bc (swapAE D) x.1 ∈ UA D.sp.cm V.gram := by
    rw [← hg]; exact finE_mem_UA V g
  exact ⟨⟨h1, h2⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨h2, h3 PP hP⟩⟩

theorem exists_finCong_lev : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank), ∃ N : ℕ, 0 < N ∧ ∀ k ∈ GfC V, GlobalTheory.Member.FinCong V N k → k ∈ levS V β L ∧ levChi V β L k = 1 := by
  classical
  intro D V β L
  obtain ⟨N, hN, hK⟩ := GlobalTheory.SplitRepsOpen.exists_finCong_le D V _ (isOpen_comap_Kg V β (L.Pg ∪ L.Q))
  refine ⟨N, hN, fun k hf hk => ?_⟩
  have hk' : finE V k ∈ Kg D.sp.cm V.gram β (L.Pg ∪ L.Q) := hK k hk
  refine ⟨⟨hf, ?_⟩, ?_⟩
  · exact Kg_le_lev (D := L) (T := L.Pg ∪ L.Q) Finset.subset_union_left Finset.subset_union_right hk'
  · unfold levChi
    rw [GlobalTheory.GoodFiniteDim.levFn_eq_one Finset.subset_union_left Finset.subset_union_right hk', Units.val_one]

end GlobalTheory.LevFinCong
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeCongruenceInLevelCharacterOneStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_congruence_in_level_character_one : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank), ∃ N : ℕ, 0 < N ∧ ∀ k ∈ GfC V, GlobalTheory.Member.FinCong V N k → k ∈ levS V β L ∧ levChi V β L k = 1 := by
  first | exact @GlobalTheory.LevFinCong.exists_finCong_lev | exact GlobalTheory.LevFinCong.exists_finCong_lev | (intros; apply GlobalTheory.LevFinCong.exists_finCong_lev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberFinitePushforward
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.ProjFin

theorem isFractionRing_evaluation (X : Scheme.{0}) [IsIntegral X] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x = genericPoint X) (hxU : x ∈ U) :
    letI := (X.evaluation U x hxU).hom.toAlgebra
    IsFractionRing Γ(X, U) (X.residueField x) := by
  subst hx
  letI := (X.evaluation U _ hxU).hom.toAlgebra
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  let φ : X.functionField →+* X.residueField (genericPoint X) := (X.residue _).hom
  let e : X.functionField ≃ₐ[Γ(X, U)] X.residueField (genericPoint X) :=
    { RingEquiv.ofBijective φ ⟨φ.injective, X.residue_surjective _⟩ with
      commutes' := fun _ => rfl }
  exact IsLocalization.isLocalization_of_algEquiv _ e

theorem finrank_app_eq_residueDegree {Z Z' : Scheme.{0}} [IsIntegral Z] [IsIntegral Z']
    (f : Z' ⟶ Z) [IsFinite f] (h : f (genericPoint Z') = genericPoint Z) {U : Z.Opens}
    (hU : IsAffineOpen U) (hxU : f (genericPoint Z') ∈ U) :
    letI := (f.app U).hom.toAlgebra
    Module.finrank Γ(Z, U) Γ(Z', f ⁻¹ᵁ U) = f.residueDegree (genericPoint Z') := by
  letI := (f.app U).hom.toAlgebra
  letI := (Z.evaluation U _ hxU).hom.toAlgebra
  letI : Algebra Γ(Z', f ⁻¹ᵁ U) (Z'.residueField (genericPoint Z')) :=
    (Z'.evaluation (f ⁻¹ᵁ U) _ hxU).hom.toAlgebra
  letI := (f.residueFieldMap (genericPoint Z')).hom.toAlgebra
  letI : Algebra Γ(Z, U) (Z'.residueField (genericPoint Z')) :=
    (f.app U ≫ Z'.evaluation (f ⁻¹ᵁ U) _ hxU).hom.toAlgebra
  haveI : IsScalarTower Γ(Z, U) Γ(Z', f ⁻¹ᵁ U) (Z'.residueField (genericPoint Z')) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(Z, U) (Z.residueField (f (genericPoint Z')))
      (Z'.residueField (genericPoint Z')) :=
    IsScalarTower.of_algebraMap_eq' congr($(Scheme.evaluation_naturality f _ hxU).hom).symm
  haveI := isFractionRing_evaluation Z hU h hxU
  haveI := isFractionRing_evaluation Z' (hU.preimage f) rfl hxU
  exact (IsFractionRing.finrank_eq Γ(Z, U) (Z.residueField (f (genericPoint Z')))
    Γ(Z', f ⁻¹ᵁ U) (Z'.residueField (genericPoint Z'))).symm

theorem genRank_eq_finrank_sections {X : Scheme.{0}} [IsIntegral X] (F : X.Modules)
    [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) (hx : genericPoint X ∈ U) :
    VB.genRank F = Module.finrank Γ(X, U) Γ(F, U) := by
  haveI : Nonempty U := ⟨⟨_, hx⟩⟩
  have key (y : U) : Module.finrank (X.presheaf.stalk (y : X)) (F.presheaf.stalk (y : X) :) =
      Module.finrank Γ(X, U) Γ(F, U) := by
    have := hU.isLocalization_stalk y
    have := QCoh.isLocalizedModule_germLinear F hU y
    have hp := (hU.primeIdealOf y).asIdeal.primeCompl_le_nonZeroDivisors
    rw [IsLocalization.finrank_eq _ _ hp, IsLocalizedModule.finrank_eq _ (QCoh.germLinear F y) hp]
  exact key ⟨_, hx⟩

theorem isFiniteQC_pushforward_structureModule {Z Z' : Scheme.{0}} (f : Z' ⟶ Z) [IsFinite f] :
    QCoh.IsFiniteQC ((Scheme.Modules.pushforward f).obj (structureModule Z')) :=
  ⟨inferInstance, fun _ hV => QCoh.finite_sections_pushforward f _ hV
    (hF := QCoh.finite_sections (structureModule Z') (hV.preimage f))⟩

theorem genRank_pushforward {Z Z' : Scheme.{0}} [IsIntegral Z] [IsIntegral Z'] (f : Z' ⟶ Z)
    [IsFinite f] (h : f (genericPoint Z') = genericPoint Z) :
    VB.genRank ((Scheme.Modules.pushforward f).obj (structureModule Z')) =
      f.residueDegree (genericPoint Z') := by
  obtain ⟨U, hU, hxU⟩ := QCoh.exists_affine_mem (genericPoint Z)
  have hx' : f (genericPoint Z') ∈ U := h ▸ hxU
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  have h1 : VB.genRank ((Scheme.Modules.pushforward f).obj (structureModule Z')) =
      Module.finrank Γ(Z, U) Γ((Scheme.Modules.pushforward f).obj (structureModule Z'), U) :=
    genRank_eq_finrank_sections _ hU hxU
  letI := (f.app U).hom.toAlgebra
  let e : Γ((Scheme.Modules.pushforward f).obj (structureModule Z'), U) ≃ₗ[Γ(Z, U)]
      Γ(Z', f ⁻¹ᵁ U) :=
    { toFun := fun s => s
      invFun := fun s => s
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [h1, e.finrank_eq, finrank_app_eq_residueDegree f h hU hx']

theorem interNumOn_eq_residueDegree_mul : ∀ (κ : Type) [Field κ] (Z Z' : Scheme.{0}) [IsIntegral Z]
    [IsIntegral Z'] [Algebra κ Γ(Z, ⊤)] (f : Z' ⟶ Z) [IsFinite f], IsProjOver (strHom κ (X := Z)) →
    topologicalKrullDim Z = 1 → f (genericPoint Z') = genericPoint Z → ∀ N : LB Z, N.IsLB →
    interNumOn κ f ![N] = (f.residueDegree (genericPoint Z') : ℤ) *
      interNum κ (structureModule Z) ![N] := by
  intro κ _ Z Z' _ _ _ f _ hP hd hg N hN
  haveI := isFiniteQC_pushforward_structureModule f
  rw [interNumOn_def, GlobalTheory.T.intersectionNumber_eq_genericRank_mul_projCurve κ Z hP hd _ N hN, genRank_pushforward f hg]

end GlobalTheory.ProjFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsZeroOfInvOfNotRegularNormal
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.NormalPole

theorem exists_height_one {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] (f : K) (Q : Ideal R)
    (hQ : ∀ s c : R, algebraMap R K s * f = algebraMap R K c → s ∈ Q) [Q.IsPrime] :
    ∃ p : Ideal R, p.IsPrime ∧ p ≤ Q ∧ p.height = 1 ∧
      ∀ s c : R, algebraMap R K s * f = algebraMap R K c → s ∈ p := by
  obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := R) f
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hcK : algebraMap R K c ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr hc0
  let d : Ideal R := (Ideal.span {c}).colon {b}
  have hd : ∀ s, s ∈ d ↔ c ∣ s * b := fun s => by
    simp only [d, Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_span_singleton]
  have reg : ∀ s, (∃ e : R, algebraMap R K s * (algebraMap R K b / algebraMap R K c) =
      algebraMap R K e) ↔ s ∈ d := fun s => by
    rw [hd]
    refine exists_congr fun e => ?_
    rw [← mul_div_assoc, div_eq_iff hcK, ← map_mul, ← map_mul, (IsFractionRing.injective R _).eq_iff,
      mul_comm e]
  have hdQ : d ≤ Q := fun s hs => by
    obtain ⟨e, he⟩ := (reg s).2 hs
    exact hQ s e he
  obtain ⟨p, hp, hpQ⟩ := Ideal.exists_minimalPrimes_le hdQ
  have hpa : p ∈ associatedPrimes R (R ⧸ d) := by
    apply Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
    rw [Ideal.annihilator_quotient]
    exact hp
  obtain ⟨hpp, x, hx⟩ := isAssociatedPrime_iff.mp hpa
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h1 : p.height = 1 := height_eq_one_of_forall_mem_iff_dvd (b := x * b) hc0 fun r => by
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, hd, _root_.mul_assoc]
  exact ⟨p, hpp, hpQ, h1, fun s e he => hp.1.2 ((reg s).1 ⟨e, he⟩)⟩

theorem mem_range_iff {R B K : Type} [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra R K]
    [Algebra B K] [IsScalarTower R B K] (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime B p] (f : K) :
    (∃ a : B, algebraMap B K a = f) ↔
      ∃ s c : R, algebraMap R K s * f = algebraMap R K c ∧ s ∉ p := by
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨⟨c, s⟩, e⟩ := IsLocalization.surj p.primeCompl a
    refine ⟨s, c, ?_, s.2⟩
    rw [IsScalarTower.algebraMap_apply R B K, IsScalarTower.algebraMap_apply R B K c, ← map_mul,
      mul_comm, e]
  · rintro ⟨s, c, e, hs⟩
    obtain ⟨u, hu⟩ := IsLocalization.map_units B (⟨s, hs⟩ : p.primeCompl)
    refine ⟨↑u⁻¹ * algebraMap R B c, ?_⟩
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← e, IsScalarTower.algebraMap_apply R B K s]
    have hu' : algebraMap R B s = u := hu.symm
    rw [hu', ← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]

end GlobalTheory.NormalPole
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocCompSplit
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.DefU

theorem exists_locComp_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → ∃ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), IsAdmissible σ.ρ ∧ π.IsLocComp w σ ∧ (IsUnramU π.V w ↔ GlobalTheory.LGrp.IsSpherical σ.ρ (GlobalTheory.LFun.KGL w (n := n))) := by
  intro E _ _ _ n π w hw
  obtain ⟨e, he⟩ := GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL E n w hw
  obtain ⟨σ₀, hadm, hirr, f, hf0, hfm, hf⟩ := GlobalTheory.T.exists_admissible_localComponent_definiteUnitary E n π w
  obtain ⟨r, -, -, hr2⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w
  have hsym : ∀ x : locU n w, e.symm (cLoc w (x : UA E n)) = x := fun x => by
    rw [← he, e.symm_apply_apply]
  have hcl : ∀ g, cLoc w ((e.symm g : locU n w) : UA E n) = g := fun g => by
    rw [← he, e.apply_symm_apply]
  let ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) σ₀.V :=
    σ₀.ρ.comp e.symm.toMulEquiv.toMonoidHom
  have hρ : ∀ g v, ρ g v = σ₀.ρ (e.symm g) v := fun _ _ => rfl
  let σ : SmIrr (GL (Fin n) (w.adicCompletion E)) :=
    { V := σ₀.V
      ρ := ρ
      smooth := fun v => (σ₀.smooth v).preimage e.symm.continuous
      irred := GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv σ₀.ρ e.symm.toMulEquiv σ₀.irred }
  have hf' : ∀ (x : locU n w) v, f (σ₀.ρ x v) = RU E n x (f v) := hf
  refine ⟨σ, GlobalTheory.CuspMult.isAdmissible_comp_equiv σ₀.ρ e.symm hadm, ⟨σ.irred, f, hf0, hfm, fun x v => ?_⟩, ?_, ?_⟩
  · change f (ρ (cLoc w (x : UA E n)) v) = _
    rw [hρ, hsym, hf']
  · rintro ⟨φ, hφ, h0, hK⟩
    let F : σ₀.ρ.IntertwiningMap (π.rep.comp (locU n w).subtype) :=
      ⟨f.codRestrict π.V hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf' x v)⟩
    have hF0 : F ≠ 0 := fun h =>
      hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
    have hsup := (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor (UA E n) (locU n w) π.V σ₀.V σ₀.V π.rep (locU n w).subtype σ₀.ρ σ₀.ρ
      π.isIrreducible_rep σ₀.irred σ₀.irred (fun g => ⟨r g, fun y => hr2 g y⟩) F hF0).1
    obtain ⟨v, hv0, hv⟩ := GlobalTheory.CuspRep.LocSph.exists_fixed_of_mem_iSup (π.rep.comp (locU n w).subtype) σ₀.ρ σ₀.irred
      (fun h : σ₀.ρ.IntertwiningMap (π.rep.comp (locU n w).subtype) => h.toLinearMap)
      (fun h g u => LinearMap.congr_fun (h.isIntertwining' g) u)
      {k | cLoc w (k : UA E n) ∈ GlobalTheory.LFun.KGL w (n := n)} ⟨φ, hφ⟩
      (fun h => h0 (congrArg Subtype.val h)) (fun k hk => Subtype.ext (hK k k.2 hk))
      (hsup ▸ Submodule.mem_top)
    intro hb
    have hmem : v ∈ fixed ρ (GlobalTheory.LFun.KGL w (n := n)) := fun g => by
      have h1 : σ₀.ρ (e.symm g.1) v = v := hv _ (by
        have h2 : cLoc w ((e.symm g.1 : locU n w) : UA E n) ∈ GlobalTheory.LFun.KGL w (n := n) := by
          rw [hcl]
          exact g.2
        exact h2)
      simpa [hρ] using h1
    have hb' : fixed ρ (GlobalTheory.LFun.KGL w (n := n)) = ⊥ := hb
    rw [hb'] at hmem
    exact hv0 ((Submodule.mem_bot _).1 hmem)
  · intro hsph
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hsph
    have hinj : Function.Injective f := by
      have hk := ((GlobalTheory.CuspRep.isIrreducible_iff _).1 σ₀.irred).2 (LinearMap.ker f) (fun g u hu => by
        rw [LinearMap.mem_ker] at hu ⊢
        rw [hf', hu, map_zero])
      rcases hk with h | h
      · exact LinearMap.ker_eq_bot.1 h
      · exact absurd (LinearMap.ker_eq_top.1 h) hf0
    refine ⟨f v, hfm v, fun h => hv0 (hinj (h.trans (map_zero f).symm)), fun x hx hk => ?_⟩
    have h1 : σ₀.ρ (⟨x, hx⟩ : locU n w) v = v := by
      have h2 : ρ (cLoc w x) v = v := by simpa using hv ⟨_, hk⟩
      rwa [hρ, hsym (⟨x, hx⟩ : locU n w)] at h2
    have h3 := hf' ⟨x, hx⟩ v
    rw [h1] at h3
    exact h3.symm

end GlobalTheory.DefU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RhoStabChiInLL0
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.RatDatRExp

theorem chi_val_small {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (hL : R.toLevCh.Is A.μ0) (hV : GlobalTheory.RealGeo.ValKs R) (i : Fin D.R.m) (PP : Pl D.host.E) (hP : PP ∈ R.Pg)
    (u : (kP PP)ˣ) :
    ∃ y : Ks, ((R.chi ((i : ℕ) + 1) PP u : ℂˣ) : ℂ) = D.what₂.embLL (algebraMap Ks D.what₂.LL y) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : kP PP)
  have ha0 : (a : D.host.E) ≠ 0 := by
    intro h
    have h0 : a = 0 := RingOfIntegers.coe_eq_zero_iff.mp h
    apply u.ne_zero
    rw [← ha, h0, map_zero]
  let k : D.host.Eˣ := Units.mk0 _ ha0
  obtain ⟨ι, hι, hint, happ⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι hι hint happ PP
  have hv : PP.valuation D.host.E (k : D.host.E) ≤ 1 := PP.valuation_le_one a
  have hinf := (GlobalTheory.UnramCharUnique.loc_parts he _ hv).1
  obtain ⟨y, hy⟩ := hV i (Formalism.L2.JoinChr.locU he.1 k) hinf
  have h1 := (hL.mu0 i).2 PP e he k (Formalism.L2.JoinChr.locU he.1 k) rfl
  have h2 := hL.chi i PP hP a k u rfl ha.symm
  refine ⟨y⁻¹, ?_⟩
  rw [MonoidHom.inv_apply] at h2
  have h3 : R.chi ((i : ℕ) + 1) PP u = ((R.C.mu0 i).locK PP k)⁻¹ := by rw [← h2, inv_inv]
  rw [h3, Units.val_inv_eq_inv_val, ← h1, hy, map_inv₀, map_inv₀]

end GlobalTheory.Mem.RatDatRExp

namespace GlobalTheory.Mem.RatDatRExp

theorem rhoStab_chiInLL0 : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (C : Formalism.L2.Pj.CoreJ D) [Algebra C.Q.c.F D.what₂.LL] (R : RealDat3 D A3 C.Q.c.F) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (kKs : C.Q.c.F →+* ↥D.LL0) (hk : ∀ x, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap C.Q.c.F D.what₂.LL x), Pins R F cG → GlobalTheory.RealGeo.InGeo g → ∀ j, 1 ≤ j → j ≤ D.R.m → NX.RhoStab (NX.ratDatR R cG kKs hk) j ∧ NX.ChiInLL0 (NX.ratDatR R cG kKs hk) j := by
  intro D G _ _ Pl0 I0 T A3 C _ R F cG B kKs hk hP _ j _ _
  refine ⟨?_, ?_⟩
  · intro g0 x hx
    change (R.FW (NX.idxOf D j)).ρ g0 x ∈ (R.FW (NX.idxOf D j)).WK
    change x ∈ (R.FW (NX.idxOf D j)).WK at hx
    by_cases hK : Formalism.IndefR.FWT.ActKeeps (κ := B.κ) B.O (NX.idxOf D j)
    · obtain ⟨hf, heq⟩ := (B.rhoGeo (NX.idxOf D j)).1 hK g0 ((B.fw.e (NX.idxOf D j)).symm ⟨x, hx⟩)
      rw [LinearEquiv.apply_symm_apply] at heq
      rw [← heq]
      exact Submodule.coe_mem _
    · rw [(B.rhoGeo (NX.idxOf D j)).2 hK g0]
      exact hx
  · intro g0
    change (((R.FW (NX.idxOf D j)).chi g0 : D.what₂.LLˣ) : D.what₂.LL) ∈ D.LL0
    have hL := hP.char.base.lev
    have hW := hP.char.base.grp.chiW
    have hV := hP.keep.valKs
    have hy : ∀ PP : R.Pg, ∃ y : C.Q.c.F,
        ((R.chi ((NX.idxOf D j : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g0 PP)) : ℂˣ) : ℂ) =
          D.what₂.embLL (algebraMap C.Q.c.F D.what₂.LL y) := fun PP =>
      chi_val_small R.toRealDat hL hV (NX.idxOf D j) PP.1 PP.2 _
    choose y hy using hy
    have h1 := hW (NX.idxOf D j) g0
    rw [Finset.prod_congr rfl (fun PP _ => hy PP), ← map_prod, ← map_prod] at h1
    have h2 := D.what₂.embLL.injective h1
    rw [h2, ← hk]
    exact (kKs _).2

end GlobalTheory.Mem.RatDatRExp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasEigEigOfType
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows

noncomputable section

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def eigOfType (R : RealDat3 D A3 Ks) (F : Face3 D A3) {X0 : BaseLevelRowSide D} (Y : Read (A3 := A3) R.toRealDat F.lv2 X0)
    (π : D.what₂.FT) : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ :=
  principalLevelFrame.cOfT (Y.PW ⟨0, Y.hm⟩)
    (levS _ (R.βW ⟨0, Y.hm⟩) (R.datWp ⟨0, Y.hm⟩ (R.toRealDat.levL F.lv2 false (sg0 D A3.A))))
    (levChi _ (R.βW ⟨0, Y.hm⟩) (R.datWp ⟨0, Y.hm⟩ (R.toRealDat.levL F.lv2 false (sg0 D A3.A))))
    (SsetF R.toRealDat (Y.tupT D.what₂.mu0)) (principalLevelFrame.rowRepR R.θ (Y.eFT π))

def HasEig (R : RealDat3 D A3 Ks) (F : Face3 D A3) {X0 : BaseLevelRowSide D} (Y : Read (A3 := A3) R.toRealDat F.lv2 X0)
    (π : D.what₂.FT) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Prop :=
  principalLevelFrame.IsEigOf (Y.PW ⟨0, Y.hm⟩)
    (levS _ (R.βW ⟨0, Y.hm⟩) (R.datWp ⟨0, Y.hm⟩ (R.toRealDat.levL F.lv2 false (sg0 D A3.A))))
    (levChi _ (R.βW ⟨0, Y.hm⟩) (R.datWp ⟨0, Y.hm⟩ (R.toRealDat.levL F.lv2 false (sg0 D A3.A))))
    (SsetF R.toRealDat (Y.tupT D.what₂.mu0)) (principalLevelFrame.rowRepR R.θ (Y.eFT π)) c

theorem hasEig_eigOfType {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
    {Y : Read (A3 := A3) R.toRealDat F.lv2 X0} {π : D.what₂.FT} (h : ∃ c, HasEig R F Y π c) :
    HasEig R F Y π (eigOfType R F Y π) := by
  unfold eigOfType principalLevelFrame.cOfT
  unfold HasEig at h ⊢
  rw [dite_eq_left h]
  exact h.choose_spec

end GlobalTheory.Mem.R3

end
end
