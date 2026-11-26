module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CotangentBidualToTangentFunctionInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreZeroMemCoinvariants
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCartanInvOneSplitStab
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteDualNumber
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HTLat GlobalTheory.EigenSplit
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat.OmegaRank

theorem mem_pow_iff {R : Type} [CommRing R] (a : R) (n : ℕ) (x : R) :
    x ∈ (Ideal.span {a} ^ n • ⊤ : Submodule R R) ↔ a ^ n ∣ x := by
  rw [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]

theorem dual_dvd_iff {O : Type} [CommRing O] (p n : ℕ) (x : DualNumber O) :
    (p : DualNumber O) ^ n ∣ x ↔ (p : O) ^ n ∣ x.fst ∧ (p : O) ^ n ∣ x.snd := by
  have e : (p : DualNumber O) ^ n = TrivSqZeroExt.inl ((p : O) ^ n) := by
    rw [← TrivSqZeroExt.inl_pow, TrivSqZeroExt.inl_natCast]
  rw [e]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y.fst, by simp⟩, ⟨y.snd, by simp⟩⟩
  · rintro ⟨⟨a, ha⟩, b, hb⟩
    exact ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, by ext <;> simp [ha, hb]⟩

theorem isAdicComplete_dualNumber {O : Type} [CommRing O] (p : ℕ)
    [h : IsAdicComplete (Ideal.span {(p : O)}) O] :
    IsAdicComplete (Ideal.span {(p : DualNumber O)}) (DualNumber O) := {
  toIsHausdorff := ⟨fun x hx => by
    simp only [SModEq.zero, mem_pow_iff, dual_dvd_iff] at hx
    refine TrivSqZeroExt.ext (h.toIsHausdorff.haus x.fst fun n => ?_)
      (h.toIsHausdorff.haus x.snd fun n => ?_)
    · rw [SModEq.zero, mem_pow_iff]; exact (hx n).1
    · rw [SModEq.zero, mem_pow_iff]; exact (hx n).2⟩,
  toIsPrecomplete := ⟨fun f hf => by
    simp only [SModEq.sub_mem, mem_pow_iff, dual_dvd_iff] at hf ⊢
    obtain ⟨a, ha⟩ := h.toIsPrecomplete.prec (f := fun n => (f n).fst) fun {m n} hmn => by
      rw [SModEq.sub_mem, mem_pow_iff]; exact (hf hmn).1
    obtain ⟨b, hb⟩ := h.toIsPrecomplete.prec (f := fun n => (f n).snd) fun {m n} hmn => by
      rw [SModEq.sub_mem, mem_pow_iff]; exact (hf hmn).2
    simp only [SModEq.sub_mem, mem_pow_iff] at ha hb
    exact ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, fun n => ⟨by simpa using ha n, by simpa using hb n⟩⟩⟩ }

theorem exists_param {O : Type} [CommRing O] [IsLocalRing O] (H : Over (Sp O)) [GrpObj H] {n : ℕ}
    (hH : SmoothOfRelativeDimension n H.hom) :
    ∃ e : (Fin n → O) ≃ LieG H, (∀ c d, (e (c + d)).1 = (e c).1 * (e d).1) ∧
      ∀ (a : O) c, (e (a • c)).1 = ptMap (dualScale a) ≫ (e c).1 := by
  obtain ⟨x, hx⟩ := KeyPow.exists_isUnivChart H hH
  refine ⟨⟨fun c => ⟨Chart.tvec (x := x) c, Chart.isTan_tvec hx c⟩, fun w => Chart.tcoord hx w.1 w.2,
    fun c => Chart.tcoord_tvec hx c, fun w => Subtype.ext (Chart.tcoord_spec hx w.1 w.2).symm⟩,
    fun c d => Chart.tvec_add hx c d, fun a c => Chart.tvec_smul hx a c⟩

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

theorem smoothDim_model : SmoothOfRelativeDimension P.A.g P.G.hom := by
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  have := P.semi.smooth
  have := P.semi.geomConnected
  have : ConnectedSpace P.G.left := GeometricallyConnected.connectedSpace P.G.hom P.G.hom.isOpenMap
  obtain ⟨n, hn⟩ := exists_dim_of_preconnected P.G.hom (Classical.arbitrary _)
  have h₁ : SmoothOfRelativeDimension n P.A.A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback P.gen_pull.1 hn
  rwa [← H1.dim_unique _ h₁ P.A.smoothDim (η[P.A.A].left (IsLocalRing.closedPoint C))]

section Lim

variable {R : Type} [CommRing R] [Algebra O R]


variable (p O R) in
abbrev redR (m : ℕ) : R →ₐ[O] R ⧸ Ideal.span {(p : R) ^ m} := Ideal.Quotient.mkₐ O _

omit [Fact p.Prime] in
theorem nilpR (m : ℕ) : IsNilpotent (p : R ⧸ Ideal.span {(p : R) ^ m}) := ⟨m, by
  rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _⟩

omit [Fact p.Prime] in
theorem factor_redR (m : ℕ) : ptMap (Ideal.Quotient.factorₐ O (Ideal.span_singleton_le_span_singleton.mpr
    (pow_dvd_pow (p : R) (Nat.le_succ m)))) ≫ ptMap (redR p O R (m + 1)) = ptMap (redR p O R m) := by
  rw [TangentPow.ptMap_comp_ptMap]
  rfl

def Corr (x : specO O R ⟶ P.Gt) (y : specO O R ⟶ P.G) : Prop :=
  ∀ m, ptMap (redR p O R m) ≫ y = P.cmp _ (nilpR m) (ptMap (redR p O R m) ≫ x)

variable {P}

theorem Corr.mul {x x' : specO O R ⟶ P.Gt} {y y' : specO O R ⟶ P.G} (h : Corr P x y) (h' : Corr P x' y') :
    Corr P (x * x') (y * y') := fun m => by
  rw [MonObj.comp_mul, MonObj.comp_mul, map_mul, h, h']

theorem Corr.one : Corr P (1 : specO O R ⟶ P.Gt) 1 := fun m => by
  rw [MonObj.comp_one, MonObj.comp_one, map_one]

theorem Corr.comp {R' : Type} [CommRing R'] [Algebra O R'] (φ : R →ₐ[O] R') {x : specO O R ⟶ P.Gt}
    {y : specO O R ⟶ P.G} (h : Corr P x y) : Corr P (ptMap φ ≫ x) (ptMap φ ≫ y) := fun m => by
  let ψ : (R ⧸ Ideal.span {(p : R) ^ m}) →ₐ[O] R' ⧸ Ideal.span {(p : R') ^ m} :=
    Ideal.quotientMapₐ _ φ (by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow, map_natCast]
      exact Ideal.mem_span_singleton_self _)
  have e : ptMap (redR p O R' m) ≫ ptMap φ = ptMap ψ ≫ ptMap (redR p O R m) := by
    rw [TangentPow.ptMap_comp_ptMap, TangentPow.ptMap_comp_ptMap]
    rfl
  rw [← Category.assoc, ← Category.assoc, e, Category.assoc, Category.assoc, h,
    P.cmp_nat _ _ (nilpR m) (nilpR m)]

variable [IsLocalRing R] (hp : ¬ IsUnit (p : R)) (hc : IsAdicComplete (Ideal.span {(p : R)}) R)
include hp hc

theorem existsUnique_right (x : specO O R ⟶ P.Gt) : ∃! y, Corr P x y :=
  AdicPt.existsUnique_lim O R (p : R) hp hc P.G _
    fun m => by rw [← P.cmp_nat _ _ (nilpR (m + 1)) (nilpR m), ← Category.assoc, factor_redR]

theorem existsUnique_left (y : specO O R ⟶ P.G) : ∃! x, Corr P x y := by
  have h := AdicPt.existsUnique_lim O R (p : R) hp hc P.Gt
    (fun m => (P.cmp _ (nilpR m)).symm (ptMap (redR p O R m) ≫ y)) fun m =>
      (P.cmp _ (nilpR m)).injective (by
        rw [P.cmp_nat _ _ (nilpR (m + 1)) (nilpR m), MulEquiv.apply_symm_apply,
          MulEquiv.apply_symm_apply, ← Category.assoc, factor_redR])
  obtain ⟨x, hx, hu⟩ := h
  refine ⟨x, fun m => by rw [hx, MulEquiv.apply_symm_apply], fun x' hx' => hu x' fun m => ?_⟩
  rw [hx' m, MulEquiv.symm_apply_apply]

end Lim

theorem exists_lieEquiv [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] :
    ∃ e : LieG P.G ≃ LieG P.Gt, (∀ x y z : LieG P.G, z.1 = x.1 * y.1 → (e z).1 = (e x).1 * (e y).1) ∧
      ∀ (a : O) (x z : LieG P.G), z.1 = ptMap (dualScale a) ≫ x.1 →
        (e z).1 = ptMap (dualScale a) ≫ (e x).1 := by
  haveI := P.isLocalRing
  haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)
  have hp₀ : ¬ IsUnit (p : O) := Fact.out
  have hp : ¬ IsUnit (p : DualNumber O) := fun h => hp₀ (by
    simpa using h.map (TrivSqZeroExt.fstHom O O O))
  have hc := isAdicComplete_dualNumber (O := O) p
  have hl := existsUnique_left (P := P) hp hc
  have hr := existsUnique_right (P := P) hp hc
  let f : LieG P.G → LieG P.Gt := fun y => ⟨(hl y.1).choose,
    (existsUnique_left (P := P) hp₀ inferInstance 1).unique
      (by
        have h := (hl y.1).choose_spec.1.comp (TrivSqZeroExt.fstHom O O O)
        rw [y.2] at h
        exact h) Corr.one⟩
  let g : LieG P.Gt → LieG P.G := fun x => ⟨(hr x.1).choose,
    (existsUnique_right (P := P) hp₀ inferInstance 1).unique
      (by
        have h := (hr x.1).choose_spec.1.comp (TrivSqZeroExt.fstHom O O O)
        rw [x.2] at h
        exact h) Corr.one⟩
  have hf : ∀ y, Corr P (f y).1 y.1 := fun y => (hl y.1).choose_spec.1
  have hg : ∀ x, Corr P x.1 (g x).1 := fun x => (hr x.1).choose_spec.1
  refine ⟨⟨f, g, fun y => Subtype.ext ((hr _).unique (hg _) (hf y)),
    fun x => Subtype.ext ((hl _).unique (hf _) (hg x))⟩, fun x y z h => ?_, fun a x z h => ?_⟩
  · exact (hl _).unique (hf z) (h ▸ (hf x).mul (hf y))
  · exact (hl _).unique (hf z) (h ▸ (hf x).comp (dualScale a))

end GlobalTheory.HTLat.OmegaRank
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanCharacterTranslatesCoinvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanCharacterTranslatesCoinvariant
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.PRep

namespace GlobalTheory.RankFibre

def stabSub {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V) :
    Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
    rw [hh, hg]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hg]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem of_parts (Lirr : (GlobalTheory.Published.BernsteinUnitaryProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β → ∀ M : Submodule ℂ (GL (Fin (a + b)) k → ℂ), M ≤ GlobalTheory.RankFibre.indScal ν β a b → (∀ f ∈ M, ∀ h : GL (Fin (a + b)) k, (fun x => f (x * h)) ∈ M) → M = ⊥ ∨ GlobalTheory.RankFibre.indScal ν β a b ≤ M)) (Llaw : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν β : kˣ →* ℂˣ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ), GlobalTheory.RankFibre.fibre ν β a b Φ ∈ GlobalTheory.PRep.indSpace (GlobalTheory.SmGL.parab k (GlobalTheory.RankFibre.blocks a b)) (GlobalTheory.SmGL.ofChar (GlobalTheory.RankFibre.parChar ν β a b)))) (Lsmooth : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), IsOpen {h : GL (Fin d) k | GlobalTheory.SplitFlip.omA ν β 1 h Φ = Φ})) (Linteg : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB k a (a + b), MeasureTheory.Integrable (fun g : GL (Fin a) k => Φ (g.val * GlobalTheory.SplitFlip.X0 k finSumFinEquiv) * (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2)) (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))))) (Lker : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB k a (a + b), GlobalTheory.RankFibre.fibre ν β a b Φ = 0 → Φ ∈ GlobalTheory.RankFibre.coinv ν β a (a + b))) : GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ), a ≤ d →
    ∀ (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β →
    ∀ N : Submodule ℂ (Matrix (Fin a) (Fin d) k → ℂ),
      Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
        Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ} ≤ N →
      N ≤ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) →
      (∀ (h : GL (Fin d) k), ∀ Ψ ∈ N, GlobalTheory.SplitFlip.omA ν β 1 h Ψ ∈ N) →
      (∀ Ψ ∈ N, (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0) →
          Ψ ∈ Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
            Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ}) ∨
      (∀ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0) → Ψ ∈ N) := by
  intro HB k _ _ _ _ a d had ν β hνs hνu hβs hβu N hCN hNSB hNst
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le had
  borelize k

  have hS0 : ∀ (h : GL (Fin (a + b)) k) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ),
      Φ ∈ fullRankSB k a (a + b) → omA ν β 1 h Φ ∈ fullRankSB k a (a + b) := by
    intro h Φ hΦ
    refine ⟨omA_mem_SB ν β 1 h hΦ.1, fun Y hY => ?_⟩
    have hr : (((1 : GL (Fin a) k)⁻¹).val * Y * (invT h).val).rank ≠ a := by
      rwa [inv_one, Units.val_one, Matrix.one_mul,
        Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units (invT h))]
    simp only [omA, hΦ.2 _ hr, mul_zero]

  have hint : ∀ Φ ∈ fullRankSB k a (a + b), ∀ x : GL (Fin (a + b)) k,
      Integrable (fun g : GL (Fin a) k => omA ν β 1 x Φ (g.val * X0 k finSumFinEquiv) * (ν (gdet g) : ℂ) *
        apow (gdet g) (((a + b : ℕ) : ℂ) / 2)) (haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) :=
    fun Φ hΦ x => Linteg k a b ν hνs _ (hS0 x Φ hΦ)
  have hadd : ∀ Φ ∈ fullRankSB k a (a + b), ∀ Ψ ∈ fullRankSB k a (a + b),
      fibre ν β a b (Φ + Ψ) = fibre ν β a b Φ + fibre ν β a b Ψ := by
    intro Φ hΦ Ψ hΨ
    funext x
    rw [Pi.add_apply]
    unfold fibre
    rw [← integral_add (hint Φ hΦ x) (hint Ψ hΨ x)]
    congr 1
    funext g
    simp only [omA, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hsmul : ∀ (c : ℂ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ),
      fibre ν β a b (c • Φ) = c • fibre ν β a b Φ := by
    intro c Φ
    funext x
    rw [Pi.smul_apply, smul_eq_mul]
    unfold fibre
    rw [← integral_const_mul]
    congr 1
    funext g
    simp only [omA, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hzero : fibre ν β a b 0 = 0 := by
    funext x
    simp [fibre, omA]

  let M : Submodule ℂ (GL (Fin (a + b)) k → ℂ) :=
    { carrier := {f | ∃ Ψ ∈ N, Ψ ∈ fullRankSB k a (a + b) ∧ fibre ν β a b Ψ = f}
      zero_mem' := ⟨0, N.zero_mem, (fullRankSB k a (a + b)).zero_mem, hzero⟩
      add_mem' := by
        rintro _ _ ⟨Φ, h1, h2, rfl⟩ ⟨Ψ, h3, h4, rfl⟩
        exact ⟨Φ + Ψ, N.add_mem h1 h3, (fullRankSB k a (a + b)).add_mem h2 h4, hadd Φ h2 Ψ h4⟩
      smul_mem' := by
        rintro c _ ⟨Φ, h1, h2, rfl⟩
        exact ⟨c • Φ, N.smul_mem c h1, (fullRankSB k a (a + b)).smul_mem c h2, hsmul c Φ⟩ }
  have hind : ∀ Ψ ∈ fullRankSB k a (a + b), fibre ν β a b Ψ ∈ indScal ν β a b := by
    intro Ψ hΨ
    refine ⟨?_, Llaw k a b ν β Ψ⟩
    have hle : stabSub ((repA ν β).comp (MonoidHom.inr (GL (Fin a) k) (GL (Fin (a + b)) k))) Ψ ≤
        stabSub (rightReg ℂ (GL (Fin (a + b)) k) ℂ) (fibre ν β a b Ψ) := by
      intro h hh
      have hh' : omA ν β 1 h Ψ = Ψ := hh
      show rightReg ℂ (GL (Fin (a + b)) k) ℂ h (fibre ν β a b Ψ) = fibre ν β a b Ψ
      funext x
      show fibre ν β a b Ψ (x * h) = fibre ν β a b Ψ x
      rw [← fibre_omA, hh']
    exact Subgroup.isOpen_mono hle (Lsmooth k a (a + b) ν β hβs Ψ hΨ.1)
  have hMle : M ≤ indScal ν β a b := by
    rintro _ ⟨Ψ, -, hΨ, rfl⟩
    exact hind Ψ hΨ
  have hMst : ∀ f ∈ M, ∀ h : GL (Fin (a + b)) k, (fun x => f (x * h)) ∈ M := by
    rintro _ ⟨Ψ, h1, h2, rfl⟩ h
    exact ⟨omA ν β 1 h Ψ, hNst h Ψ h1, hS0 h Ψ h2, funext fun x => fibre_omA ν β a b h Ψ x⟩
  rcases Lirr HB k a b ν β hνs hνu hβs hβu M hMle hMst with h0 | hT
  · left
    intro Ψ hΨN hΨr
    have hΨ : Ψ ∈ fullRankSB k a (a + b) := ⟨hNSB hΨN, hΨr⟩
    have hm : fibre ν β a b Ψ ∈ M := ⟨Ψ, hΨN, hΨ, rfl⟩
    rw [h0, Submodule.mem_bot] at hm
    exact Lker k a b ν β hνs hβs Ψ hΨ hm
  · right
    intro Φ hΦ hΦr
    have hΦS : Φ ∈ fullRankSB k a (a + b) := ⟨hΦ, hΦr⟩
    obtain ⟨Ψ, hΨN, hΨS, hZ⟩ := hT (hind Φ hΦS)
    have hd : Φ - Ψ ∈ coinv ν β a (a + b) := by
      refine Lker k a b ν β hνs hβs _ ((fullRankSB k a (a + b)).sub_mem hΦS hΨS) ?_
      rw [sub_eq_add_neg, ← neg_one_smul ℂ Ψ, hadd Φ hΦS _ ((fullRankSB k a (a + b)).smul_mem _ hΨS),
        hsmul, hZ]
      simp
    have := N.add_mem (hCN hd) hΨN
    simpa using this

theorem coinv_or_fullRank_le : GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ), a ≤ d →
    ∀ (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β →
    ∀ N : Submodule ℂ (Matrix (Fin a) (Fin d) k → ℂ),
      Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
        Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ} ≤ N →
      N ≤ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) →
      (∀ (h : GL (Fin d) k), ∀ Ψ ∈ N, GlobalTheory.SplitFlip.omA ν β 1 h Ψ ∈ N) →
      (∀ Ψ ∈ N, (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0) →
          Ψ ∈ Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
            Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ}) ∨
      (∀ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0) → Ψ ∈ N) :=
  of_parts GlobalTheory.T.induced_scalar_irreducible GlobalTheory.T.fibre_mem_induced_space GlobalTheory.T.isOpen_stabilizer_schwartzBruhat GlobalTheory.T.integrable_full_rank_fibre GlobalTheory.T.fibre_zero_mem_coinvariants

end GlobalTheory.RankFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanCharacterTranslatesCoinvariantStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_character_translates_coinvariant : GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ), a ≤ d →
    ∀ (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β →
    ∀ N : Submodule ℂ (Matrix (Fin a) (Fin d) k → ℂ),
      Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
        Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ} ≤ N →
      N ≤ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) →
      (∀ (h : GL (Fin d) k), ∀ Ψ ∈ N, GlobalTheory.SplitFlip.omA ν β 1 h Ψ ∈ N) →
      (∀ Ψ ∈ N, (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0) →
          Ψ ∈ Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
            Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ}) ∨
      (∀ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0) → Ψ ∈ N) := by
  first | exact @GlobalTheory.RankFibre.coinv_or_fullRank_le | exact GlobalTheory.RankFibre.coinv_or_fullRank_le | (intros; apply GlobalTheory.RankFibre.coinv_or_fullRank_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilCharSurjectiveAndMapRangeAl
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsSeriesOfTorsionCharacters
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace CharGerm

section Series

variable {R₀ κ : Type} [CommRing R₀]

end Series

section Torsion

variable {R₀ : Type} [CommRing R₀] {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G] {g : ℕ}
  {x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G)}
  (h0 : ∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1)
  (hnat : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
    (φ : S →ₐ[R₀] S') (a : Fin g → S), (∀ i, IsNilpotent (a i)) →
      spMap φ ≫ x S a = x S' (fun i => φ (a i)))
  (hinj : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
    (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b)
  (hsurj : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
    (ρ : S →ₐ[R₀] S'), Function.Surjective ρ → (∀ a ∈ RingHom.ker ρ, IsNilpotent a) →
      ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
        ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)





end Torsion

section Value

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.KernelNoTorsion GlobalTheory.GmPoints

variable {R₀ : Type} [CommRing R₀] {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G] {p : ℕ}
  (χ : Tv G p)

lemma comp_χ_of_le {T : Over (Spec (CommRingCat.of R₀))} {m n : ℕ} (h : m ≤ n)
    (u : T ⟶ torsion G (p ^ m)) (v : T ⟶ torsion G (p ^ n))
    (huv : u ≫ torsion.ι G (p ^ m) = v ≫ torsion.ι G (p ^ n)) : u ≫ χ.χ m = v ≫ χ.χ n := by
  induction n, h using Nat.le_induction with
  | base => rw [torsion_hom_ext huv]
  | succ n hmn ih =>
    have h1 : (u ≫ torsion.ι G (p ^ m)) ^ (p ^ n) = 1 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      rw [pow_add, pow_mul, ← MonObj.comp_pow, torsionι_pow, MonObj.comp_one, one_pow]
    rw [ih (torsionLift _ h1) (torsionLift_ι _ _).symm]
    exact χ.compat n _ _ _ (by rw [torsionLift_ι, huv])

lemma comp_χ_eq {T : Over (Spec (CommRingCat.of R₀))} {m n : ℕ}
    (u : T ⟶ torsion G (p ^ m)) (v : T ⟶ torsion G (p ^ n))
    (huv : u ≫ torsion.ι G (p ^ m) = v ≫ torsion.ι G (p ^ n)) : u ≫ χ.χ m = v ≫ χ.χ n := by
  rcases le_total m n with h | h
  · exact comp_χ_of_le χ h u v huv
  · exact (comp_χ_of_le χ h v u huv.symm).symm


end Value

end CharGerm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTateOfCharacter
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChTor

namespace GlobalTheory.ChTor

theorem exists_tate_of_character :
    ∀ (Γ : Type) [Group Γ] (U : Type) [CommGroup U] (p : ℕ), 1 ≤ p → (∀ a b : Γ, a * b = b * a) → ∀ e : ℕ → Γ → Γ → U, (∀ k : ℕ, 1 ≤ k → (∀ (l : ℕ) (z s : Γ), 1 ≤ l → z ^ k = 1 → s ^ (k * l) = 1 → e (k * l) z s = e k z (s ^ l)) ∧ ∀ κ : Γ → U, (∀ z z', z ^ k = 1 → z' ^ k = 1 → κ (z * z') = κ z * κ z') → ∃! s : Γ, s ^ k = 1 ∧ ∀ z, z ^ k = 1 → e k z s = κ z) → ∀ κ : Γ → U, (∀ z z', (∃ m, z ^ (p ^ m) = 1) → (∃ m, z' ^ (p ^ m) = 1) → κ (z * z') = κ z * κ z') → ∃ s : ℕ → Γ, (∀ m, s m ^ (p ^ m) = 1 ∧ s (m + 1) ^ p = s m) ∧ ∀ m z, z ^ (p ^ m) = 1 → e (p ^ m) z (s m) = κ z := by
  intro Γ _ U _ p hp hc e he κ hκ
  have hpm : ∀ m : ℕ, 1 ≤ p ^ m := fun m => Nat.one_le_pow _ _ hp
  have key : ∀ m : ℕ, ∃! s : Γ, s ^ (p ^ m) = 1 ∧ ∀ z, z ^ (p ^ m) = 1 → e (p ^ m) z s = κ z :=
    fun m => (he (p ^ m) (hpm m)).2 κ (fun z z' hz hz' => hκ z z' ⟨m, hz⟩ ⟨m, hz'⟩)
  choose s hs hu using key
  refine ⟨s, fun m => ⟨(hs m).1, ?_⟩, fun m => (hs m).2⟩
  have h1 : s (m + 1) ^ (p ^ m * p) = 1 := by rw [← pow_succ]; exact (hs (m + 1)).1
  apply hu m
  refine ⟨by rw [← pow_mul, mul_comm]; exact h1, fun z hz => ?_⟩
  rw [← (he (p ^ m) (hpm m)).1 p z (s (m + 1)) hp hz h1, ← pow_succ]
  apply (hs (m + 1)).2
  rw [pow_succ, pow_mul, hz, one_pow]

end GlobalTheory.ChTor
end

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HTLat GlobalTheory.EigenSplit
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat

open KernelNoTorsion GmPoints

theorem exists_subgroup_hom_of_tv {O : Type} [CommRing O] {G : Over (Spec (CommRingCat.of O))}
    [GrpObj G] [IsCommMonObj G] {p : ℕ} {R : Type} [CommRing R] [Algebra O R] (ψ : Tv G p) :
    ∃ (H : Subgroup (specO O R ⟶ G)) (θ : H →* Rˣ),
      ∀ (n : ℕ) (w : specO O R ⟶ torsion G (p ^ n)),
        ∃ h : w ≫ torsion.ι G (p ^ n) ∈ H, θ ⟨_, h⟩ = unitOf (w ≫ ψ.χ n) := by
  have hl : ∀ {x : specO O R ⟶ G} {n : ℕ} (m : ℕ), x ^ p ^ n = 1 → x ^ p ^ (n + m) = 1 :=
    fun m hn => by rw [pow_add, pow_mul, hn, one_pow]
  let H : Subgroup (specO O R ⟶ G) :=
    { carrier := {x | ∃ n : ℕ, x ^ p ^ n = 1}
      one_mem' := ⟨0, one_pow _⟩
      mul_mem' := by
        rintro x y ⟨n, hn⟩ ⟨m, hm⟩
        exact ⟨n + m, by rw [mul_pow, hl m hn, add_comm, hl n hm, _root_.one_mul]⟩
      inv_mem' := by
        rintro x ⟨n, hn⟩
        exact ⟨n, by rw [inv_pow, hn, inv_one]⟩ }
  let θ : H → Rˣ := fun x => unitOf (torsionLift x.1 x.2.choose_spec ≫ ψ.χ x.2.choose)
  have hθ : ∀ (x : H) (n : ℕ) (w : specO O R ⟶ torsion G (p ^ n)),
      w ≫ torsion.ι G (p ^ n) = x.1 → θ x = unitOf (w ≫ ψ.χ n) := fun x n w hw =>
    congrArg unitOf (CharGerm.comp_χ_eq ψ _ _ (by rw [hw, torsionLift_ι]))
  refine ⟨H, MonoidHom.mk' θ fun x y => ?_, fun n w =>
    ⟨⟨n, by rw [← MonObj.comp_pow, torsionι_pow, MonObj.comp_one]⟩, hθ _ n w rfl⟩⟩
  obtain ⟨n, hn⟩ := x.2
  obtain ⟨m, hm⟩ := y.2
  have hx : x.1 ^ p ^ (n + m) = 1 := hl m hn
  have hy : y.1 ^ p ^ (n + m) = 1 := by rw [add_comm]; exact hl n hm
  have hxy : (x * y).1 ^ p ^ (n + m) = 1 := by rw [Subgroup.coe_mul, mul_pow, hx, hy, _root_.one_mul]
  rw [hθ x _ _ (torsionLift_ι _ hx), hθ y _ _ (torsionLift_ι _ hy),
    hθ (x * y) _ _ (torsionLift_ι _ hxy), ← unitOf_mul]
  congr 1
  exact ψ.isChar _ _ _ _ _ (by rw [torsionLift_ι, torsionLift_ι, torsionLift_ι]; rfl)

theorem weilChar_surjective_and_map_range_al :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), Function.Surjective P.weilChar ∧ (LinearMap.range P.al).map (omega P.Gt).subtype = htSpan P.Gt p := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P
  have hs : Function.Surjective P.weilChar := fun χ => by
    obtain ⟨H, θ, hθ⟩ := exists_subgroup_hom_of_tv (R := O) χ
    obtain ⟨κ, hκ⟩ := TorsionCharacter.exists_extend_character (P.toA.comp H.subtype)
      (P.toA_injective.comp H.subtype_injective)
      ((Units.map (algebraMap O C).toMonoidHom).comp θ)
    obtain ⟨s, hs1, hs2⟩ := ChTor.exists_tate_of_character (ChTor.Pts P.A.A) Cˣ p
      (Fact.out : p.Prime).pos (fun a b => mul_comm a b) (weil P.A)
      (fun k hk => ⟨fun l z s hl hz hs => weil_level hk hl hz hs, weil_perfect hk⟩) κ
      fun z z' _ _ => map_mul κ z z'
    refine ⟨Tate.mk s hs1, (P.existsUnique_isWeilChar _).unique (P.isWeilChar_weilChar _)
      fun n w => ?_⟩
    obtain ⟨h, hw⟩ := hθ n w
    rw [Tate.lev_mk, hs2 n _ (P.toA_pow w), ← hw]
    exact (congrArg Units.val (hκ ⟨_, h⟩)).symm
  refine ⟨hs, le_antisymm P.map_range_al_le ?_⟩
  rw [← map_span_dlogTv]
  refine Submodule.map_mono (Submodule.span_le.2 ?_)
  rintro _ ⟨χ, rfl⟩
  obtain ⟨t, rfl⟩ := hs χ
  exact ⟨1 ⊗ₜ t, by rw [P.al_tmul, one_smul]; rfl⟩

end GlobalTheory.HTLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLaws
noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RealLift.PolRangePf

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem atPl_eq' (w : ι) (L : Module.End ℂ (V w)) :
    atPl w L = PiTensorProduct.mapMultilinear ℂ V V (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w L) := rfl

theorem atPl_add' (w : ι) (L L' : Module.End ℂ (V w)) : atPl w (L + L') = atPl w L + atPl w L' := by
  simp only [atPl_eq', MultilinearMap.map_update_add]

theorem atPl_smul' (w : ι) (c : ℂ) (L : Module.End ℂ (V w)) : atPl w (c • L) = c • atPl w L := by
  simp only [atPl_eq', MultilinearMap.map_update_smul, RingHom.id_apply]

theorem atPl_zero' (w : ι) : atPl w (0 : Module.End ℂ (V w)) = 0 := by
  simp only [atPl_eq', MultilinearMap.map_update_zero]

theorem atPl_tprod (w : ι) (L : Module.End ℂ (V w)) (f : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  rw [atPl, PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp [Function.update_of_ne h]

end Tensor

theorem heisOp_zero {P Q R S : ℕ} : heisOp (P := P) (Q := Q) (R := R) (S := S) 0 = 0 := by
  simp [heisOp]

theorem Jm_transpose' (p q : ℕ) : (Jm p q)ᵀ = Jm p q := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_transpose]

theorem exists_at_piInf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (z : InfinitePlace F → ℂ) : ∃ a : AE F E, At (evI F) a ∧ ∀ w, piInf (τ w) a = z w := GlobalTheory.T.exists_archimedean_adele_CM_prescribed_embedding_values hcm τ z

theorem exists_mat_at {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {m k : Type} (z : InfinitePlace F → Matrix m k ℂ) :
    ∃ u : Matrix m k (AE F E), At (evI F) u ∧ ∀ w, u.map (piInf (τ w)) = z w := by
  choose a ha using fun i j => exists_at_piInf hcm τ (fun w => z w i j)
  refine ⟨Matrix.of a, fun x hx => ?_, fun w => ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.zero_apply]
    exact (ha i j).1 x hx
  · ext i j
    simp [(ha i j).2 w]

theorem mulX_mem_span {P Q R S : ℕ} (l : Ln P Q R S) :
    LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S) ∈
      Submodule.span ℂ (Set.range (heisOp (P := P) (Q := Q) (R := R) (S := S))) := GlobalTheory.T.fockVariableMultiplication_mem_span_heisenbergOperators l

theorem tens_top {ι σ : Type} [Fintype ι] [DecidableEq ι] (N : Submodule ℂ (⨂[ℂ] _ : ι, MvPolynomial σ ℂ))
    (h1 : PiTensorProduct.tprod ℂ (fun _ => (1 : MvPolynomial σ ℂ)) ∈ N)
    (hN : ∀ w l, ∀ T ∈ N, atPl w (LinearMap.mulLeft ℂ (MvPolynomial.X l : MvPolynomial σ ℂ)) T ∈ N) : N = ⊤ := GlobalTheory.T.piTensorMvPolynomial_submodule_eq_top_of_one_mul_X N h1 hN

theorem tens_top_heis {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ}
    (N : Submodule ℂ (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S))
    (h1 : PiTensorProduct.tprod ℂ (fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S)) ∈ N)
    (hN : ∀ w c, ∀ T ∈ N, atPl w (heisOp (P := P) (Q := Q) (R := R) (S := S) c) T ∈ N) : N = ⊤ := by
  refine tens_top N h1 fun w l T hT => ?_
  let K : Submodule ℂ (Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S)) :=
    { carrier := {L | ∀ T ∈ N, atPl w L T ∈ N}
      add_mem' := fun {a b} ha hb T hT => by
        rw [atPl_add', LinearMap.add_apply]; exact N.add_mem (ha T hT) (hb T hT)
      zero_mem' := fun T _ => by rw [atPl_zero']; exact N.zero_mem
      smul_mem' := fun c a ha T hT => by rw [atPl_smul', LinearMap.smul_apply]; exact N.smul_mem c (ha T hT) }
  have hK : Submodule.span ℂ (Set.range (heisOp (P := P) (Q := Q) (R := R) (S := S))) ≤ K :=
    Submodule.span_le.2 (by rintro _ ⟨c, rfl⟩; exact hN w c)
  exact hK (mulX_mem_span l) T hT

theorem heisOp_twist_one {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) :
    heisOp (Complex.I • (Jm P Q * c * Jm R S)) 1 = Complex.I • heisOp c 1 := GlobalTheory.T.fockHeisenbergOperator_I_signatureConj_apply_one c

theorem sumPl_twist_one {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ} (c : ι → Matrix (Ix P Q) (Ix R S) ℂ) :
    sumPl (fun w => heisOp (Complex.I • (Jm P Q * c w * Jm R S))) (PiTensorProduct.tprod ℂ (fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S)))
      = Complex.I • sumPl (fun w => heisOp (c w)) (PiTensorProduct.tprod ℂ (fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S))) := by
  simp only [sumPl, LinearMap.sum_apply, Finset.smul_sum, atPl_tprod, heisOp_twist_one]
  refine Finset.sum_congr rfl fun w _ => ?_
  exact (PiTensorProduct.tprod ℂ).map_update_smul _ w Complex.I _

theorem polRange_of (hL : ActsLaws) (_hD : DerEx) (hV : VacLine) : PolRange := by
  intro F E _ _ _ _ _ σ n d P Q R S X W M ψ τ A C Φ hcm hψ hfr hθX hθW hΦ
  have hz : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) (t : ℝ), M.co.rho ψ (realAd F t • u) 0 = 0 := by
    intro u t; funext x; simp [Darboux.rho, schr]
  have toD : ∀ u (f f₁ : SInf F (Fin n × Fin d)), SD (fun t => M.co.rho ψ (realAd F t • u)) f f₁ →
      ActsD (evI F) (M.heisLine ψ u) f f₁ := fun u f f₁ h => (hL F (Fin n × Fin d) f f₁ f₁).1 _ (hz u) h
  have uniq : ∀ u (f f₁ f₂ : SInf F (Fin n × Fin d)), ActsD (evI F) (M.heisLine ψ u) f f₁ →
      ActsD (evI F) (M.heisLine ψ u) f f₂ → f₁ = f₂ := fun u f f₁ f₂ h1 h2 => (hL F _ f f₁ f₂).2.2.1 _ h1 h2
  choose A' hA' using fun w => (hfr.2.1 w).2
  choose C' hC' using fun w => (hfr.2.2 w).2
  have decomp : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) w,
      u.map (piInf (τ w)) = A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ := by
    intro u w
    rw [show A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ =
        (A w * A' w) * u.map (piInf (τ w)) * ((C w) * (C' w))ᵀ by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc], hA', hC']
    simp
  have der : ∀ u, At (evI F) u → ∀ c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ,
      (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → ∀ T,
      ActsD (evI F) (M.heisLine ψ u) (Φ T) (Φ (sumPl (fun w => heisOp (c w)) T)) :=
    fun u hu c hc T => toD _ _ _ (hΦ.2 u hu c hc T)
  have tw : ∀ w (c : Matrix (Ix P Q) (Ix R S) ℂ) (e : ℂ),
      A w * (e • (Jm P Q * c * Jm R S)) * (C w)ᵀ = e • (X.θ w * (A w * c * (C w)ᵀ) * (W.θ w)ᵀ) := by
    intro w c e
    have h2 : (C w)ᵀ * (W.θ w)ᵀ = Jm R S * (C w)ᵀ := by
      rw [← Matrix.transpose_mul, hθW w, Matrix.transpose_mul, Jm_transpose']
    calc A w * (e • (Jm P Q * c * Jm R S)) * (C w)ᵀ = e • ((A w * Jm P Q) * c * (Jm R S * (C w)ᵀ)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = _ := by rw [← hθX w, ← h2]; simp only [Matrix.mul_assoc]
  have gauss1 : M.IsGauss ψ τ (Φ (PiTensorProduct.tprod ℂ (fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S)))) := by
    refine ⟨fun _ => 1, fun u u' hu hu' hrel f f' hf hf' => ?_⟩
    have hc : ∀ w, u.map (piInf (τ w)) = A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ := decomp u
    have hc' : ∀ w, u'.map (piInf (τ w)) =
        A w * (Complex.I • (Jm P Q * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * Jm R S)) * (C w)ᵀ := by
      intro w; rw [hrel w, tw, ← hc w]; simp
    rw [uniq u _ _ _ hf (der u hu _ hc _), uniq u' _ _ _ hf' (der u' hu' _ hc' _), sumPl_twist_one, map_smul]
  have gauss_mem : ∀ f₀, M.IsGauss ψ τ f₀ → f₀ ∈ M.Pol ψ τ := fun f₀ h => by
    unfold Model.Pol
    exact Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h
  have pol_der : ∀ u, At (evI F) u → ∀ f ∈ M.Pol ψ τ, ∀ f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ → f₁ ∈ M.Pol ψ τ := by
    intro u hu f hf f₁ h1
    unfold Model.Pol at hf ⊢
    exact Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h1
  apply le_antisymm
  · rintro _ ⟨T, rfl⟩
    have htop : (M.Pol ψ τ).comap Φ = ⊤ := by
      refine tens_top_heis _ (gauss_mem _ gauss1) fun w c T hT => ?_
      obtain ⟨u, hu, hu'⟩ := exists_mat_at hcm τ
        (fun w' => A w' * Function.update (0 : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) w c w' * (C w')ᵀ)
      have hs : sumPl (fun w' => heisOp (Function.update (0 : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) w c w')) T =
          atPl w (heisOp c) T := by
        rw [sumPl, LinearMap.sum_apply, Finset.sum_eq_single w]
        · simp
        · intro b _ hb; simp [Function.update_of_ne hb, heisOp_zero, atPl_zero']
        · simp
      have := pol_der u hu _ hT _ (der u hu _ hu' T)
      rwa [hs] at this
    have : T ∈ (M.Pol ψ τ).comap Φ := htop ▸ Submodule.mem_top
    exact this
  · unfold Model.Pol
    refine sInf_le ⟨fun f₀ hf₀ => ?_, fun u hu f hf f₁ h1 => ?_⟩
    · obtain ⟨ε, hε⟩ := hf₀
      obtain ⟨z, hz⟩ := hV F E σ (Fin n) (Fin d) (Fin n × Fin d) P Q R S ψ τ (incM F X.J) (incM F W.J) M.co 1
        Complex.I A C Φ hcm hψ hfr hΦ f₀ ε (fun u u' hu hu' c hc hc' f f' hf hf' =>
          hε u u' hu hu' (fun w => by rw [hc' w, tw, ← hc w]) f f' (toD _ _ _ hf) (toD _ _ _ hf'))
      exact ⟨z • PiTensorProduct.tprod ℂ (fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S)), by rw [map_smul, hz]⟩
    · obtain ⟨T, rfl⟩ := hf
      exact ⟨_, (uniq u _ _ _ (der u hu _ (decomp u) T) h1)⟩

end GlobalTheory.RealLift.PolRangePf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLawsStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws : GlobalTheory.RealLift.ActsLaws → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.PolRange := by
  first | exact @GlobalTheory.RealLift.PolRangePf.polRange_of | exact GlobalTheory.RealLift.PolRangePf.polRange_of | (intros; apply GlobalTheory.RealLift.PolRangePf.polRange_of <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivPullEqVPull
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Vert GlobalTheory.Vert.Model GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections res_pullbackSections pullbackSections_res
  pullback_map_app_pullbackSections)
open GlobalTheory.Twist (resM resM_resM app_resM)

namespace GlobalTheory.Vert.DivPull

section Sections

variable {X Y Y' W : Scheme.{0}}

theorem pullbackComp_inv_app (b : W ⟶ Y) (a : Y ⟶ X) (E : X.Modules) {U : X.Opens} {V : Y.Opens}
    {T : W.Opens} (h₁ : V ≤ a ⁻¹ᵁ U) (h₂ : T ≤ b ⁻¹ᵁ V) (h : T ≤ (b ≫ a) ⁻¹ᵁ U) (s : Γ(E, U)) :
    ((Scheme.Modules.pullbackComp b a).inv.app E).app T (pullbackSections (b ≫ a) E h s) =
      pullbackSections b _ h₂ (pullbackSections a E h₁ s) := by
  have e := unit_conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction a).comp
    (Scheme.Modules.pullbackPushforwardAdjunction b))
    (Scheme.Modules.pullbackPushforwardAdjunction (b ≫ a)) (Scheme.Modules.pullbackComp b a).inv E
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at e
  refine (app_resM _ h _).trans (Eq.trans ?_ (pullbackSections_res b _ h₂ h₁ _).symm)
  exact congrArg (resM _ h) congr(($e).app U s).symm

theorem detUnit_congr {F : X.Modules} {r : ℕ} {U U' T T' V : X.Opens} {e : Fin r → Γ(F, U)}
    {e' : Fin r → Γ(F, U')} {d : Fin r → Γ(F, T)} {d' : Fin r → Γ(F, T')} (he : IsFrame e)
    (he' : IsFrame e') (hd : IsFrame d) (hd' : IsFrame d') (h : V ≤ U) (h' : V ≤ U') (k : V ≤ T)
    (k' : V ≤ T') (H : ∀ i, resM F h (e i) = resM F k (d i))
    (H' : ∀ i, resM F h' (e' i) = resM F k' (d' i)) :
    he.detUnit he' h h' = hd.detUnit hd' k k' := by
  have e₁ : he.basis h = hd.basis k :=
    DFunLike.ext _ _ fun i => by simp only [IsFrame.basis_apply, H]
  refine Units.ext ?_
  simp only [IsFrame.val_detUnit, e₁, H']

end Sections

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Z Z₁ : Model O}
  {f : Z₁.X ⟶ Z.X} (hf : f ≫ Z.str = Z₁.str) {E E' : Z.X.Modules} {r : ℕ}

end GlobalTheory.Vert.DivPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFinitePiTensorSumOfFactorOperators
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFinitePiTensorSumOfFactorOperators
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RealLift

theorem atPl_mem_range_map {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (L : ∀ i, Module.End ℂ (V i)) (N : ∀ i, Submodule ℂ (V i)) (hN : ∀ i, ∀ y ∈ N i, L i y ∈ N i)
    (w : ι) (y : ⨂[ℂ] i, V i) (hy : y ∈ LinearMap.range (PiTensorProduct.map fun i => (N i).subtype)) :
    atPl w (L w) y ∈ LinearMap.range (PiTensorProduct.map fun i => (N i).subtype) := by
  obtain ⟨t, rfl⟩ := hy
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    have hx : ∀ j, (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w (L w) j) (x j : V j) ∈ N j := by
      intro j
      by_cases h : j = w
      · subst h
        simp only [Function.update_self]
        exact hN j _ (x j).2
      · simp only [Function.update_of_ne h, LinearMap.id_apply]
        exact (x j).2
    refine ⟨r • PiTensorProduct.tprod ℂ (fun j => (⟨_, hx j⟩ : N j)), ?_⟩
    simp [atPl, PiTensorProduct.map_tprod]
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _)]
    exact Submodule.add_mem _ ha hb

theorem locFin_sumPl : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (L : ∀ i, Module.End ℂ (V i)), (∀ i, GlobalTheory.RealLift.LocFin (L i)) →
    GlobalTheory.RealLift.LocFin (GlobalTheory.RealLift.sumPl L) := by
  intro ι _ _ V _ _ L hL v
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    choose N hNf hfN hN using fun i => hL i (f i)
    refine ⟨LinearMap.range (PiTensorProduct.map fun i => (N i).subtype), inferInstance, ?_, ?_⟩
    · exact ⟨r • PiTensorProduct.tprod ℂ (fun i => (⟨f i, hfN i⟩ : N i)), by simp [PiTensorProduct.map_tprod]⟩
    · intro y hy
      rw [sumPl, LinearMap.sum_apply]
      exact Submodule.sum_mem _ fun w _ => atPl_mem_range_map L N hN w y hy
  | add a b ha hb =>
    obtain ⟨N₁, h₁, ha₁, hs₁⟩ := ha
    obtain ⟨N₂, h₂, hb₂, hs₂⟩ := hb
    refine ⟨N₁ ⊔ N₂, inferInstance, Submodule.add_mem_sup ha₁ hb₂, ?_⟩
    intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hs₁ y₁ hy₁) (hs₂ y₂ hy₂)

end GlobalTheory.RealLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFinitePiTensorSumOfFactorOperatorsStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyFinite_piTensorSumOfFactorOperators : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] (L : ∀ i, Module.End ℂ (V i)), (∀ i, GlobalTheory.RealLift.LocFin (L i)) → GlobalTheory.RealLift.LocFin (GlobalTheory.RealLift.sumPl L) := by
  first | exact @GlobalTheory.RealLift.locFin_sumPl | exact GlobalTheory.RealLift.locFin_sumPl | (intros; apply GlobalTheory.RealLift.locFin_sumPl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaFreeFiniteBijectiveOfSmooth
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HTLat GlobalTheory.EigenSplit
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat


open GlobalTheory.HodgeTateCompare in
theorem omega_free_finite_bijective_of_smooth {O : Type} [CommRing O] [IsLocalRing O]
    (G : Over (Spec (CommRingCat.of O))) [GrpObj G] [Smooth G.hom] :
    Module.Free O (omega G) ∧ Module.Finite O (omega G) ∧
      Function.Bijective (fun (x : LieG G) => ((LinearMap.proj x : (LieG G → O) →ₗ[O] O) ∘ₗ
        (omega G).subtype : Module.Dual O (omega G))) := by
  obtain ⟨h₁, h₂⟩ := finite_projective_of_smooth (G := G)
  haveI : Module.Free O (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.Cotangent G) := Module.free_of_flat_of_isLocalRing
  refine ⟨.of_equiv (omegaEquiv G), .equiv (omegaEquiv G), ?_⟩
  refine (Function.Bijective.of_comp_iff _ (lieEquiv G).bijective).1 ?_
  refine (Function.Bijective.of_comp_iff' (omegaEquiv G).dualMap.bijective _).1 ?_
  convert Function.bijective_id
  funext w
  exact LinearMap.ext fun f => ev_apply f w

theorem Point.omega_free_finite_bijective : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), Module.Free O (omega P.Gt) ∧ Module.Finite O (omega P.Gt) ∧ Function.Bijective (fun (x : LieG P.Gt) => ((LinearMap.proj x : (LieG P.Gt → O) →ₗ[O] O) ∘ₗ (omega P.Gt).subtype : Module.Dual O (omega P.Gt))) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P
  haveI := P.isLocalRing
  haveI := (GlobalTheory.UnitRigidity.smooth_geometricallyConnected_of_isGt _ _ ⟨P.D⟩).1
  exact omega_free_finite_bijective_of_smooth P.Gt

end GlobalTheory.HTLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldCompletionTensorOfIsInertAt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldCompletionTensorOfIsInertAt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertTensorField

theorem isField_tensor_of_isInertAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → IsField (Fv F v ⊗[F] E) := by
  intro F E _ _ _ _ _ σ B hB v w hvw
  have hp : (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime := by
    rw [show v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = w.asIdeal from hvw]
    exact w.isPrime
  exact GlobalTheory.InertField.isField_of_inert F E hB.cm.2.2.1 v hp

end GlobalTheory.InertTensorField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldCompletionTensorOfIsInertAtStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isField_completion_tensor_of_isInertAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → IsField (Fv F v ⊗[F] E) := by
  first | exact @GlobalTheory.InertTensorField.isField_tensor_of_isInertAt | exact GlobalTheory.InertTensorField.isField_tensor_of_isInertAt | (intros; apply GlobalTheory.InertTensorField.isField_tensor_of_isInertAt <;> assumption)
end
end
