module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NatCastMemMaximalIdealOfOverLa
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HermitianDatumDirectPower
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionNowhereZeroOfGenerates
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NumberFieldFinitePlaceCompletionEmbedding

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelSubgroup
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.RecDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem det_gram_ne_zero {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) :
    S.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have hy : S.frame.equivFun.symm v = 0 := by
    apply S.nondeg.2
    intro x
    have hi : ∀ i, S.hT (S.frame i) (S.frame.equivFun.symm v) = 0 := by
      intro i
      have := congrFun h0 i
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Module.Basis.equivFun_symm_apply, map_sum]
      simpa [Matrix.mulVec, dotProduct, Formalism.BasicNotions.HSpace.gram, mul_comm] using this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← S.frame.sum_repr x, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hi, smul_zero]
  exact S.frame.equivFun.symm.map_eq_zero_iff.1 hy

theorem det_mul_sigR_det {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0) (g : GL (Fin M) (R ⊗[F] E))
    (hg : g ∈ HR R σ J) : g.1.det * sigR R σ g.1.det = 1 := by
  have h : Formalism.UG.cT (sigR R σ) g.1 * JR R J * g.1 = JR R J := hg
  have h2 := congrArg Matrix.det h
  have hu : IsUnit (JR (F := F) R J).det := by
    have : (JR (F := F) R J).det = inclR (F := F) R J.det := ((inclR (F := F) R).map_det J).symm
    rw [this]
    exact (IsUnit.mk0 _ hJ).map _
  have h3 : (Formalism.UG.cT (sigR R σ) g.1).det = sigR R σ g.1.det := by
    rw [Formalism.UG.cT, Matrix.det_transpose]
    exact ((sigR R σ).map_det g.1).symm
  rw [Matrix.det_mul, Matrix.det_mul, h3] at h2
  apply hu.mul_left_cancel
  linear_combination h2

theorem det_finHom_norm {D : D7} (V : HSp D) (k : GA D V) :
    (finHom V k).1.det * sigR (Af D.host.F) D.sp.cm.sig (finHom V k).1.det = 1 := by
  have h := det_mul_sigR_det (AF D.host.F) D.sp.cm.sig V.gram (det_gram_ne_zero V) (matHom V k) k.2
  let φ := (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have e : (finHom V k).1.det = φ (matHom V k).1.det := (φ.map_det _).symm
  have c : ∀ x, sigR (Af D.host.F) D.sp.cm.sig (φ x) = φ (sigR (AF D.host.F) D.sp.cm.sig x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [φ, sigR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [e, c, ← map_mul, h, map_one]

theorem finHom_inv_mulVec_mem {D : D7} (V : HSp D) (k : GA D V)
    (hk : ∀ z ∈ latHat V, (finHom V k).1.mulVec z ∈ latHat V) :
    ∀ z ∈ latHat V, (finHom V k⁻¹).1.mulVec z ∈ latHat V := by
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
    V.L0.map (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))
  have hL : latHat V = GlobalTheory.AdLat.hat D.host.F (L : Set (Fin V.rank → D.host.E)) := by
    unfold Formalism.L2.Pj.latHat GlobalTheory.AdLat.hat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
  have hfg : L.FG := V.standardTuple_isLattice.fg.map _
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have hspan : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        V.frame.equivFun.trans ((starLinearEquiv D.host.E).trans V.frame.equivFun.symm)
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨x, hx, hx₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e x ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        change a • e x ∈ Formalism.E.hdual V.hT V.L0
        simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
          LinearMap.restrictScalars_apply, Submodule.mem_one]
        intro y hy
        have hxy : V.hT (e x) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩)
            (LinearMap.mem_ker.mp hx)
        have hyx : V.hT y (e x) = 0 := by
          have hh := V.herm.eq (e x) y
          simpa [hxy] using hh.symm
        simp [map_smul, hyx]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
    have : (L : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := rfl
    rw [this, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  let c : D.host.E ≃ₐ[D.host.F] D.host.E :=
    AlgEquiv.ofBijective D.sp.cm.sig (D.sp.cm.sig.bijective)
  rw [hL] at hk ⊢
  rw [map_inv]
  exact GlobalTheory.AdLat.inv_mulVec_mem_hat _ _ _ L (finHom V k) c hfg hsp hk (det_finHom_norm V k)

theorem exists_level_subgroup {G A : Type} [Group G] [CommRing A] {n : ℕ} (f : G →* GL (Fin n) A) (H : Subgroup G)
    (Λ : AddSubgroup (Fin n → A)) (N : ℕ)
    (hinv : ∀ k : G, (∀ z ∈ Λ, (f k).1.mulVec z ∈ Λ) → ∀ z ∈ Λ, (f k⁻¹).1.mulVec z ∈ Λ) :
    ∃ K : Subgroup G, (∀ k, k ∈ K ↔ k ∈ H ∧ ∀ z ∈ Λ, ∃ y ∈ Λ, (f k).1.mulVec z - z = N • y) ∧
      ∀ k ∈ K, (f k).1.mulVec '' (Λ : Set (Fin n → A)) = Λ := by
  have hin : ∀ k : G, (∀ z ∈ Λ, ∃ y ∈ Λ, (f k).1.mulVec z - z = N • y) →
      ∀ z ∈ Λ, (f k).1.mulVec z ∈ Λ := by
    intro k hk z hz
    obtain ⟨y, hy, e⟩ := hk z hz
    rw [sub_eq_iff_eq_add.1 e]
    exact add_mem (nsmul_mem hy N) hz
  have hmul : ∀ (a b : G) z, (f (a * b)).1.mulVec z = (f a).1.mulVec ((f b).1.mulVec z) := by
    intro a b z
    rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  have hone : ∀ z, (f 1).1.mulVec z = z := by
    intro z
    rw [map_one, Units.val_one, Matrix.one_mulVec]
  refine ⟨{ carrier := {k | k ∈ H ∧ ∀ z ∈ Λ, ∃ y ∈ Λ, (f k).1.mulVec z - z = N • y}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun k => Iff.rfl, ?_⟩
  · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun z hz => ?_⟩
    obtain ⟨y, hy, e⟩ := hb' z hz
    obtain ⟨y', hy', e'⟩ := ha' _ (hin b hb' z hz)
    refine ⟨y' + y, add_mem hy' hy, ?_⟩
    rw [hmul, nsmul_add, ← e, ← e']
    abel
  · exact ⟨one_mem _, fun z _ => ⟨0, zero_mem _, by rw [hone, sub_self, nsmul_zero]⟩⟩
  · rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun z hz => ?_⟩
    obtain ⟨y, hy, e⟩ := ha' _ (hinv a (hin a ha') z hz)
    refine ⟨-y, neg_mem hy, ?_⟩
    rw [← hmul, mul_inv_cancel, hone] at e
    rw [neg_nsmul, ← e, neg_sub]
  · rintro k ⟨-, hk⟩
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hin k hk z hz
    · intro z hz
      exact ⟨_, hinv k (hin k hk) z hz, (hmul k k⁻¹ z).symm.trans (by rw [mul_inv_cancel, hone])⟩

theorem exists_isLevelK : ∀ (D : D7) (V : HSp D) (N : ℕ), ∃ Kf : Subgroup (GA D V), IsLevelK V N Kf ∧ ∀ k ∈ Kf, (finHom V k).1.mulVec '' (latHat V : Set _) = latHat V :=
  fun _ V N => exists_level_subgroup (finHom V) (GfC V) (latHat V) N (finHom_inv_mulVec_mem V)

end GlobalTheory.RecDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ConjugationActsOnCmTorsionByMultiplication
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ConjugationActsOnCmTorsionByMultiplication
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat.Acts

theorem corr (ω : ℂ) (f : ℤ × ℤ → ℂ) (hf : ∀ s, f s = s.1 + s.2 * ω) (R : ℂ → ℂ → Prop)
    (tot : ∀ z, ∃ z', R z z') (sur : ∀ z', ∃ z, R z z')
    (add : ∀ z z' y y', R z z' → R y y' → R (z + y) (z' + y'))
    (om : ∀ z z', R z z' → R (ω * z) (ω * z'))
    (iff : ∀ z z' y y', R z z' → R y y' → ((∃ a, z - y = f a) ↔ ∃ a, z' - y' = f a))
    (rsp : ∀ z z' y', R z z' → (∃ a, z' - y' = f a) → R z y') (n : ℕ) (hn : 0 < n) :
    (∃ s, ∀ a, R (f a / n) (f s * f a / n)) ∧
      ∀ s, (∀ a, R (f a / n) (f s * f a / n)) → ∃ s' a, f s' * f s = 1 + n * f a := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have f0 : f (0, 0) = 0 := by simp [hf]
  have f1 : f (1, 0) = 1 := by simp [hf]
  have h0 : R 0 0 := by
    obtain ⟨z', h⟩ := tot 0
    obtain ⟨a, ha⟩ := (iff _ _ _ _ (add _ _ _ _ h h) h).1 ⟨(0, 0), by simp [f0]⟩
    exact rsp _ _ _ h ⟨a, by rw [← ha]; ring⟩
  have neg : ∀ z z', R z z' → R (-z) (-z') := by
    intro z z' h
    obtain ⟨y, hy⟩ := tot (-z)
    obtain ⟨a, ha⟩ := (iff _ _ _ _ (add _ _ _ _ h hy) h0).1 ⟨(0, 0), by simp [f0]⟩
    exact rsp _ _ _ hy ⟨a, by rw [← ha]; ring⟩
  have int : ∀ (m : ℤ) z z', R z z' → R (m * z) (m * z') := by
    intro m z z' h
    induction m using Int.induction_on with
    | zero => simpa using h0
    | succ k ih =>
      have := add _ _ _ _ ih h
      convert this using 1 <;> push_cast <;> ring
    | pred k ih =>
      have := add _ _ _ _ ih (neg _ _ h)
      convert this using 1 <;> push_cast <;> ring
  have mul : ∀ a z z', R z z' → R (f a * z) (f a * z') := by
    intro a z z' h
    have := add _ _ _ _ (int a.1 _ _ h) (int a.2 _ _ (om _ _ h))
    convert this using 1 <;> rw [hf] <;> ring
  constructor
  · obtain ⟨z', h⟩ := tot (1 / n)
    obtain ⟨s, hs⟩ := (iff _ _ _ _ (int n _ _ h) h0).1 ⟨(1, 0), by rw [f1]; push_cast; field_simp; ring⟩
    refine ⟨s, fun a => ?_⟩
    have := mul a _ _ h
    convert this using 1
    · ring
    · rw [← hs]; push_cast; field_simp; ring
  · intro s hs
    obtain ⟨z, h⟩ := sur (1 / n)
    obtain ⟨s', hs'⟩ := (iff _ _ _ _ (int n _ _ h) h0).2 ⟨(1, 0), by rw [f1]; push_cast; field_simp; ring⟩
    obtain ⟨a, ha⟩ := (iff _ _ _ _ (hs s') h).1 ⟨(0, 0), by rw [f0, ← hs']; push_cast; field_simp; ring⟩
    refine ⟨s', a, ?_⟩
    rw [← ha]; field_simp; ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem spMap_symm (τ : ℂ ≃+* ℂ) : spMap (τ.symm : ℂ →+* ℂ) ≫ spMap (τ : ℂ →+* ℂ) = 𝟙 _ := by
  show Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x; simp

theorem pt_over (C : Curve H) (z : ℂ) : C.pt z ≫ C.P.A.hom = 𝟙 _ := Over.w (C.u.ex fun _ => C.c * z)

theorem pt_add (C : Curve H) {f : Sp ℂ ⟶ Sp ℂ} {io : C.P.A.left ⟶ C.P.A.left}
    (h : IsGrpPullback C.P.A C.P.A f io) {z z' y y' : ℂ} (hz : C.pt z' ≫ io = f ≫ C.pt z)
    (hy : C.pt y' ≫ io = f ≫ C.pt y) : C.pt (z' + y') ≫ io = f ≫ C.pt (z + y) := by
  have e : ∀ a b, C.pt (a + b) = (C.u.ex (fun _ => C.c * a) * C.u.ex (fun _ => C.c * b)).left := by
    intro a b
    rw [← C.u.ex_add, Curve.pt]
    congr 2
    funext _; simp [mul_add]
  let U : Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ f) ⟶ 𝟙_ (Over (Sp ℂ)) := Over.homMk f (by simp)
  have := h.2 _ (C.u.ex fun _ => C.c * z') (C.u.ex fun _ => C.c * y') (U ≫ C.u.ex fun _ => C.c * z)
    (U ≫ C.u.ex fun _ => C.c * y) hz.symm hy.symm
  rw [← MonObj.comp_mul] at this
  rw [e, e]
  exact this.symm

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (C : Curve H), ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ io : C.P.A.left ⟶ C.P.A.left, IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ n : ℕ, 0 < n → (∃ s, C.ActsBy τ io n s) ∧ ∀ s, C.ActsBy τ io n s → (∃ s' a, wC H s' * wC H s = 1 + n * wC H a) ∧ ∀ m : ℕ, m ∣ n → C.ActsBy τ io m s := by
  intro E _ _ _ H C τ hτ io h n hn
  obtain ⟨W, -, hW, hker, hon, hcomm⟩ := GlobalTheory.T.exists_cmEndomorphism_comm_conjugation E H C
  have hc := hcomm τ hτ io h
  have key := corr (wC H (0, 1)) (wC H) (fun s => by simp [wC])
    (fun z z' => C.pt z' ≫ io = spMap (τ : ℂ →+* ℂ) ≫ C.pt z)
    (fun z => by
      have w : (spMap (τ : ℂ →+* ℂ) ≫ C.pt z) ≫ C.P.A.hom = 𝟙 _ ≫ spMap (τ : ℂ →+* ℂ) := by
        rw [Category.assoc, pt_over]; simp
      obtain ⟨z', hz⟩ := hon (h.1.lift _ _ w) (h.1.lift_snd _ _ w)
      exact ⟨z', by rw [hz, h.1.lift_fst]⟩)
    (fun z' => by
      obtain ⟨z, hz⟩ := hon (spMap (τ.symm : ℂ →+* ℂ) ≫ C.pt z' ≫ io) (by
        rw [Category.assoc, Category.assoc, h.1.w, ← Category.assoc (C.pt z'), pt_over, Category.id_comp,
          spMap_symm])
      refine ⟨z, ?_⟩
      have := spMap_symm τ.symm
      rw [RingEquiv.symm_symm] at this
      rw [hz, ← Category.assoc, this, Category.id_comp])
    (fun z z' y y' hz hy => pt_add C h hz hy)
    (fun z z' hz => by
      rw [← hW, ← hW, Category.assoc, hc, ← Category.assoc, hz, Category.assoc])
    (fun z z' y y' hz hy => by
      rw [← hker, ← hker]
      constructor
      · intro e
        apply h.1.hom_ext
        · rw [hz, hy, e]
        · rw [pt_over, pt_over]
      · intro e
        have e' : spMap (τ : ℂ →+* ℂ) ≫ C.pt z = spMap (τ : ℂ →+* ℂ) ≫ C.pt y := by rw [← hz, ← hy, e]
        have := congrArg (spMap (τ.symm : ℂ →+* ℂ) ≫ ·) e'
        simpa only [← Category.assoc, spMap_symm, Category.id_comp] using this)
    (fun z z' y' hz e => by rw [← (hker _ _).2 e]; exact hz) n hn
  refine ⟨key.1.imp fun s hs => ⟨h, hs⟩, fun s hs => ⟨key.2 s hs.2, ?_⟩⟩
  rintro m ⟨k, rfl⟩
  refine ⟨h, fun a => ?_⟩
  have hk : (k : ℂ) ≠ 0 := by
    rintro hk
    have : k = 0 := by exact_mod_cast hk
    simp [this] at hn
  have e : wC H (k * a.1, k * a.2) = k * wC H a := by simp [wC]; ring
  have := hs.2 (k * a.1, k * a.2)
  rw [e] at this
  have hm : (m : ℂ) ≠ 0 := by
    rintro hk
    have : m = 0 := by exact_mod_cast hk
    simp [this] at hn
  have e1 : wC H s * (k * wC H a) / ((m * k : ℕ) : ℂ) = wC H s * wC H a / m := by push_cast; field_simp
  have e2 : (k * wC H a) / ((m * k : ℕ) : ℂ) = wC H a / m := by push_cast; field_simp
  rwa [e1, e2] at this

end GlobalTheory.CompRat.Acts
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ConjugationActsOnCmTorsionByMultiplicationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugation_acts_on_cm_torsion_by_multiplication : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (C : Curve H), ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ io : C.P.A.left ⟶ C.P.A.left, IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ n : ℕ, 0 < n → (∃ s, C.ActsBy τ io n s) ∧ ∀ s, C.ActsBy τ io n s → (∃ s' a, wC H s' * wC H s = 1 + n * wC H a) ∧ ∀ m : ℕ, m ∣ n → C.ActsBy τ io m s := by
  first | exact @GlobalTheory.CompRat.Acts.main | exact GlobalTheory.CompRat.Acts.main | (intros; apply GlobalTheory.CompRat.Acts.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDatumSumAndAllSignatures
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.DatumSum

noncomputable section

def blockEnd {U V W : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] (e : U ≃ₗ[ℝ] V × W) (f : V →ₗ[ℝ] V) (g : W →ₗ[ℝ] W) : U →ₗ[ℝ] U :=
  e.symm.toLinearMap ∘ₗ (f.prodMap g) ∘ₗ e.toLinearMap

theorem blockEnd_apply {U V W : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] (e : U ≃ₗ[ℝ] V × W) (f : V →ₗ[ℝ] V) (g : W →ₗ[ℝ] W) (x : U) :
    e (blockEnd e f g x) = (f (e x).1, g (e x).2) := by
  simp [blockEnd, Prod.map]

theorem blockEnd_comp {U V W : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] (e : U ≃ₗ[ℝ] V × W) (f f' : V →ₗ[ℝ] V) (g g' : W →ₗ[ℝ] W) :
    blockEnd e f g ∘ₗ blockEnd e f' g' = blockEnd e (f ∘ₗ f') (g ∘ₗ g') := by
  ext x
  apply e.injective
  simp [blockEnd_apply]

theorem trace_blockEnd {U V W : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] [Module.Finite ℝ V] [Module.Finite ℝ W] (e : U ≃ₗ[ℝ] V × W) (f : V →ₗ[ℝ] V) (g : W →ₗ[ℝ] W) :
    LinearMap.trace ℝ U (blockEnd e f g) = LinearMap.trace ℝ V f + LinearMap.trace ℝ W g := by
  have h1 : blockEnd e f g = e.symm.conj (f.prodMap g) := by
    ext x; simp [blockEnd, LinearEquiv.conj_apply]
  rw [h1, LinearMap.trace_conj', LinearMap.trace_prodMap']

def sumForm {L M : Type} [AddCommGroup L] [AddCommGroup M] (B : LinearMap.BilinForm ℤ L)
    (C : LinearMap.BilinForm ℤ M) : LinearMap.BilinForm ℤ (L × M) :=
  B.compl₁₂ (LinearMap.fst ℤ L M) (LinearMap.fst ℤ L M) + C.compl₁₂ (LinearMap.snd ℤ L M) (LinearMap.snd ℤ L M)

theorem sumForm_apply {L M : Type} [AddCommGroup L] [AddCommGroup M] (B : LinearMap.BilinForm ℤ L)
    (C : LinearMap.BilinForm ℤ M) (x y : L × M) : sumForm B C x y = B x.1 y.1 + C x.2 y.2 := by
  simp [sumForm]

theorem sumForm_bijective {L M : Type} [AddCommGroup L] [AddCommGroup M] (B : LinearMap.BilinForm ℤ L)
    (C : LinearMap.BilinForm ℤ M) (hB : Function.Bijective B) (hC : Function.Bijective C) :
    Function.Bijective (sumForm B C) := by
  constructor
  · intro x y h
    refine Prod.ext (hB.1 ?_) (hC.1 ?_)
    · ext z
      have := LinearMap.congr_fun h (z, 0)
      simpa [sumForm_apply] using this
    · ext z
      have := LinearMap.congr_fun h (0, z)
      simpa [sumForm_apply] using this
  · intro φ
    obtain ⟨x, hx⟩ := hB.2 (φ ∘ₗ LinearMap.inl ℤ L M)
    obtain ⟨y, hy⟩ := hC.2 (φ ∘ₗ LinearMap.inr ℤ L M)
    refine ⟨(x, y), LinearMap.ext fun z => ?_⟩
    rw [sumForm_apply, hx, hy]
    simp [← map_add (f := _)]

theorem sumForm_baseChange {L M : Type} [AddCommGroup L] [AddCommGroup M] (B : LinearMap.BilinForm ℤ L)
    (C : LinearMap.BilinForm ℤ M) (x y : ℝ ⊗[ℤ] (L × M)) :
    (sumForm B C).baseChange ℝ x y =
      B.baseChange ℝ (TensorProduct.prodRight ℤ ℝ ℝ L M x).1 (TensorProduct.prodRight ℤ ℝ ℝ L M y).1 +
      C.baseChange ℝ (TensorProduct.prodRight ℤ ℝ ℝ L M x).2 (TensorProduct.prodRight ℤ ℝ ℝ L M y).2 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, Prod.fst_add, Prod.snd_add, ha, hb]; ring
  | tmul r u =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), Prod.fst_add, Prod.snd_add, ha, hb]; ring
    | tmul s v => simp [sumForm_apply, add_smul, add_mul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def sumDatum (D D' : Datum H) : Datum H where
  La := D.La × D'.La
  fin := by haveI := D.fin; haveI := D'.fin; infer_instance
  proj := by haveI := D.proj; haveI := D'.proj; infer_instance
  EF := sumForm D.EF D'.EF
  alt := fun x => by simp [sumForm_apply, D.alt, D'.alt]
  unimod := sumForm_bijective D.EF D'.EF D.unimod D'.unimod
  adj := fun a x y => by simp [sumForm_apply, D.adj, D'.adj]
  p := D.p + D'.p
  q := D.q + D'.q
  rank := by
    haveI := D.fin
    haveI := D.proj
    haveI := D'.fin
    haveI := D'.proj
    have h1 := (TensorProduct.isBaseChange (𝓞 E) (D.La × D'.La) E).finrank_eq
    have h2 := (TensorProduct.isBaseChange (𝓞 E) D.La E).finrank_eq
    have h2' := (TensorProduct.isBaseChange (𝓞 E) D'.La E).finrank_eq
    have h3 := (TensorProduct.prodRight (𝓞 E) E E D.La D'.La).finrank_eq
    rw [← h1, h3, Module.finrank_prod, h2, h2', D.rank, D'.rank]
    ring
  dom := by
    haveI := D.fin
    haveI := D'.fin
    haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
    haveI : Module.Finite ℤ D'.La := Module.Finite.trans (𝓞 E) D'.La
    obtain ⟨J, h1, h2, h3, h4⟩ := D.dom
    obtain ⟨J', h1', h2', h3', h4'⟩ := D'.dom
    set e := TensorProduct.prodRight ℤ ℝ ℝ D.La D'.La with he
    refine ⟨blockEnd e J J', ?_, ?_, ?_, ?_⟩
    · intro x
      apply e.injective
      simp [blockEnd_apply, h1, h1', Prod.ext_iff]
    · intro x y
      simp only [sumForm_baseChange, ← he, blockEnd_apply, h2, h2']
    · intro x hx
      simp only [sumForm_baseChange, ← he, blockEnd_apply]
      have hne : e x ≠ 0 := fun hc => hx (e.injective (by rw [map_zero]; exact hc))
      by_cases ha : (e x).1 = 0
      · have hb : (e x).2 ≠ 0 := fun hb => hne (Prod.ext ha hb)
        simpa [ha] using h3' _ hb
      · by_cases hb : (e x).2 = 0
        · simpa [hb] using h3 _ ha
        · exact add_pos (h3 _ ha) (h3' _ hb)
    · intro a A t hA ht
      let A0 : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La :=
        ((DistribSMul.toAddMonoidHom D.La a).toIntLinearMap).baseChange ℝ
      let A1 : ℝ ⊗[ℤ] D'.La →ₗ[ℝ] ℝ ⊗[ℤ] D'.La :=
        ((DistribSMul.toAddMonoidHom D'.La a).toIntLinearMap).baseChange ℝ
      obtain ⟨k1, k2, k3⟩ := h4 a A0 _ (fun x => by simp [A0]) rfl
      obtain ⟨k1', k2', k3'⟩ := h4' a A1 _ (fun x => by simp [A1]) rfl
      have hAA : A = blockEnd e A0 A1 := by
        apply LinearMap.ext
        intro x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add a b ha hb => simp only [map_add (f := _), ha, hb]
        | tmul r u =>
          have : r ⊗ₜ[ℤ] u = r • ((1 : ℝ) ⊗ₜ[ℤ] u) := by simp [TensorProduct.smul_tmul']
          rw [this, map_smul, map_smul, hA]
          congr 1
          apply e.injective
          rw [blockEnd_apply]
          simp [he, A0, A1]
      have ht' : t = ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
          ((D.p : ℂ) * τ (a : E) + (D.q : ℂ) * starRingEnd ℂ (τ (a : E))) +
          ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
          ((D'.p : ℂ) * τ (a : E) + (D'.q : ℂ) * starRingEnd ℂ (τ (a : E))) := by
        rw [ht, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun τ _ => ?_
        push_cast; ring
      rw [hAA, blockEnd_comp, blockEnd_comp, trace_blockEnd, trace_blockEnd, k1, ← k1, k1', ← k1', k2, k3, k2', k3',
        ht']
      refine ⟨rfl, ?_, ?_⟩
      · rw [Complex.add_re]; ring
      · rw [Complex.add_im]; ring

end

end GlobalTheory.DatumSum

namespace GlobalTheory

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReindexUnitary
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.MarkUnit

theorem infMat_unitary {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (τ : E →+* ℂ)
    (hτ : ∀ x, τ (σ x) = starRingEnd ℂ (τ x)) (θ : Ainf F ⊗[F] E →+* ℂ) (hθ : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ)
    (h : HA (AF F) σ J) :
    ((Formalism.MainNotions.StandardLattice.infMat σ J θ h).map (starRingEnd ℂ)).transpose * J.map τ * Formalism.MainNotions.StandardLattice.infMat σ J θ h =
      J.map τ := by
  let φ : AF F ⊗[F] E →+* ℂ :=
    θ.comp (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  have hφ : ∀ (a : AF F) (x : E), φ (a ⊗ₜ x) =
      GlobalTheory.InfAdeleCM.ext (τ.comp (algebraMap F E)) (fstA F a) * τ x := fun a x =>
    GlobalTheory.InfAdeleCM.hom_tmul τ θ hθ.1 hθ.2 (fstA F a) x
  have h1 : ∀ z, φ (sigR (AF F) σ z) = starRingEnd ℂ (φ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      have : sigR (AF F) σ (a ⊗ₜ x) = a ⊗ₜ σ x := rfl
      rw [this, hφ, hφ, map_mul, GlobalTheory.InfAdeleCM.conj_ext, hτ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have h2 : ∀ x, φ (inclR (AF F) x) = τ x := by
    intro x
    have : inclR (F := F) (AF F) x = (1 : AF F) ⊗ₜ x := rfl
    rw [this, hφ, map_one, map_one, one_mul]
  have hu : Formalism.UG.cT (sigR (AF F) σ) (HA.mat (AF F) σ J h).1 * JR (AF F) J * (HA.mat (AF F) σ J h).1 =
      JR (AF F) J := (show HR (AF F) σ J from h).2
  have hm : Formalism.MainNotions.StandardLattice.infMat σ J θ h = (HA.mat (AF F) σ J h).1.map φ := rfl
  have hJ : (JR (AF F) J).map φ = J.map τ := by
    ext a b
    exact h2 _
  have hc : (Formalism.UG.cT (sigR (AF F) σ) (HA.mat (AF F) σ J h).1).map φ =
      (((HA.mat (AF F) σ J h).1.map φ).map (starRingEnd ℂ)).transpose := by
    ext a b
    exact h1 _
  have := congrArg (fun m => Matrix.map m φ) hu
  simp only [Matrix.map_mul] at this
  rw [hJ, hc] at this
  rw [hm]
  exact this


end GlobalTheory.MarkUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsModelPushInvertibleOverCompleteDVR
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsModelPushInvertibleOverCompleteDVR
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem exists_model_pushInvertible_under_cdvr : PartI → N1ab → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ (T : CDVR) (io : c.F →+* T.Fr) (p : ℕ), p.Prime → (p : T.V) ∈ IsLocalRing.maximalIdeal T.V → l.GoodAt p → ∃ (O : Type) (_ : CommRing O) (β : O →+* c.F) (Y : Model Xo c β), PushInvertible Y.t.G Y.t.PP.L ∧ ∃ b : O →+* T.V, (algebraMap T.V T.Fr).comp b = io.comp β := by
  intro hI hN E _ _ _ H Dw l Xo c hpos T io p hp hpT hg
  classical
  obtain ⟨Xf, hXf⟩ : ∃ Xf : ∀ l' : Level H, Moduli Dw l', Xf l = Xo :=
    ⟨Function.update (fun l' => (hN E H Dw l' hpos).some) l Xo, Function.update_self ..⟩
  subst hXf
  let U₀ : ValuationSubring T.Fr := (ValuationRing.valuation T.V T.Fr).valuationSubring
  have hU₀ : ∀ x : T.Fr, x ∈ U₀ ↔ ∃ a : T.V, algebraMap T.V T.Fr a = x := fun x =>
    ValuationRing.mem_integer_iff T.V T.Fr x
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  have hpU : (p : c.F) ∈ (U₀.comap io).nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or]
    right
    intro h
    rw [ValuationSubring.mem_comap, hU₀] at h
    obtain ⟨a, ha⟩ := h
    have hp0 : (p : c.F) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have h1 : a * (p : T.V) = 1 := by
      apply hinj
      rw [map_mul, ha, map_natCast, map_one, ← map_natCast io p, ← map_mul, inv_mul_cancel₀ hp0, map_one]
    exact (IsLocalRing.mem_maximalIdeal _).1 hpT (IsUnit.of_mul_eq_one_right a h1)
  obtain ⟨W, hW, hWU⟩ := GlobalTheory.T.exists_valuationSubring_complex_comap_eq c.F (U₀.comap io) p hpU
  obtain ⟨Y, hY, -⟩ := hI.2 E H Dw hpos Xf
  have hmem : ∀ x : c.V W, ∃ a : T.V, algebraMap T.V T.Fr a = io x := by
    intro x
    have hx : (x : c.F) ∈ U₀.comap io := hWU ▸ x.2
    exact (hU₀ _).1 (ValuationSubring.mem_comap.1 hx)
  choose f hf using hmem
  refine ⟨c.V W, inferInstance, (c.V W).subtype, Y p W hp hW ⟨l, c, hg⟩,
    ((hY p W hp hW).1.1 ⟨l, c, hg⟩).2.2.1, ?_⟩
  refine ⟨{ toFun := f
            map_one' := hinj (by simp [hf])
            map_mul' := fun x y => hinj (by simp [hf])
            map_zero' := hinj (by simp [hf])
            map_add' := fun x y => hinj (by simp [hf]) }, ?_⟩
  ext x
  exact hf x

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsModelPushInvertibleOverCompleteDVRStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_model_pushInvertible_over_completeDVR : PartI → N1ab → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ (T : CDVR) (io : c.F →+* T.Fr) (p : ℕ), p.Prime → (p : T.V) ∈ IsLocalRing.maximalIdeal T.V → l.GoodAt p → ∃ (O : Type) (_ : CommRing O) (β : O →+* c.F) (Y : Model Xo c β), PushInvertible Y.t.G Y.t.PP.L ∧ ∃ b : O →+* T.V, (algebraMap T.V T.Fr).comp b = io.comp β := by
  first | exact @GlobalTheory.exists_model_pushInvertible_under_cdvr | exact GlobalTheory.exists_model_pushInvertible_under_cdvr | (intros; apply GlobalTheory.exists_model_pushInvertible_under_cdvr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AlgebraicPointsModuliEveryPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NumberFieldFinitePlaceCompletionEmbeddingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.numberField_finitePlace_completion_embedding : Formalism.L2.PjFree.LocFld := by
  first | exact @GlobalTheory.locFld | exact GlobalTheory.locFld | (intros; apply GlobalTheory.locFld <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AlgebraicPointsModuliEveryPlace
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem algPtLa_moduli : N1c → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → AlgPtLa Xo c :=
  fun h E _ _ _ H Dw l Xo c hpq =>
    Formalism.L2.PjFree.algPtLa_of (GlobalTheory.T.xoNumPt_of_p_add_q_pos h E H Dw l Xo c hpq) GlobalTheory.T.numberField_finitePlace_completion_embedding

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AlgebraicPointsModuliEveryPlaceStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicPoints_moduli_every_place : N1c → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → AlgPtLa Xo c := by
  first | exact @GlobalTheory.algPtLa_moduli | exact GlobalTheory.algPtLa_moduli | (intros; apply GlobalTheory.algPtLa_moduli <;> assumption)
end
end
