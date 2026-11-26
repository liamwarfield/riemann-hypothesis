module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfRangeSubset
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NatCastMemMaximalIdealOfOverLa

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.UnitarySplit

section Gen

open Formalism.UG

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]

theorem val_bc (p : R →+* A) (g : GL n R) : ((bc p g : GL n A) : Matrix n n A) = (g : Matrix n n R).map p := rfl

theorem mat_ext (p : R →+* A) (q : R →+* B) (hi : ∀ x y, p x = p y → q x = q y → x = y) {M N : Matrix n n R}
    (h1 : M.map p = N.map p) (h2 : M.map q = N.map q) : M = N := by
  ext i j
  exact hi _ _ (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

theorem gl_ext (p : R →+* A) (q : R →+* B) (hi : ∀ x y, p x = p y → q x = q y → x = y) {g h : GL n R}
    (h1 : bc p g = bc p h) (h2 : bc q g = bc q h) : g = h :=
  Units.ext (mat_ext p q hi (congrArg Units.val h1) (congrArg Units.val h2))

theorem gl_glue (p : R →+* A) (q : R →+* B) (hi : ∀ x y, p x = p y → q x = q y → x = y)
    (hs : ∀ a b, ∃ x, p x = a ∧ q x = b) (a : GL n A) (b : GL n B) : ∃ g : GL n R, bc p g = a ∧ bc q g = b := by
  choose f hp hq using hs
  let G : Matrix n n A → Matrix n n B → Matrix n n R := fun M N => Matrix.of fun i j => f (M i j) (N i j)
  have Gp : ∀ M N, (G M N).map p = M := fun M N => by ext i j; simp [G, hp]
  have Gq : ∀ M N, (G M N).map q = N := fun M N => by ext i j; simp [G, hq]
  refine ⟨⟨G a.1 b.1, G (a⁻¹).1 (b⁻¹).1, ?_, ?_⟩, Units.ext (Gp _ _), Units.ext (Gq _ _)⟩ <;>
    apply mat_ext p q hi <;> simp [Matrix.map_mul, Gp, Gq]

theorem map_cond (p : R →+* A) (s : R →+* R) (t : A →+* A) (hc : ∀ x, p (s x) = t (p x)) (J g : Matrix n n R) :
    (cT s g * J * g).map p = cT t (g.map p) * J.map p * g.map p := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2
  ext i j
  simp [cT, hc]

theorem mem_iff (p : R →+* A) (q : R →+* B) (hi : ∀ x y, p x = p y → q x = q y → x = y)
    (s : R →+* R) (t : A →+* A) (u : B →+* B) (hp : ∀ x, p (s x) = t (p x)) (hq : ∀ x, q (s x) = u (q x))
    (J : Matrix n n R) (g : GL n R) :
    g ∈ UJ s J ↔ bc p g ∈ UJ t (J.map p) ∧ bc q g ∈ UJ u (J.map q) := by
  change cT s g.1 * J * g.1 = J ↔ cT t (g.1.map p) * J.map p * g.1.map p = J.map p ∧
    cT u (g.1.map q) * J.map q * g.1.map q = J.map q
  rw [← map_cond p s t hp, ← map_cond q s u hq]
  exact ⟨fun h => by rw [h]; exact ⟨rfl, rfl⟩, fun h => mat_ext p q hi h.1 h.2⟩

theorem mem_of_form (t : A →+* A) (J : Matrix n n A) (g : GL n A)
    (h : ∀ x y, hform t J (g.1 *ᵥ x) (g.1 *ᵥ y) = hform t J x y) : g ∈ UJ t J := by
  change cT t g.1 * J * g.1 = J
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simp only [hform, Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply] at this
  rw [Finset.sum_comm] at this
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [this, Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp
  · intro b _ hb; simp [hb]
  · simp

end Gen

section Tens

variable {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']

theorem map_sig (f : R →ₐ[F] R') (σ : E →ₐ[F] E) (x : R ⊗[F] E) :
    (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom (sigR R σ x) =
      sigR R' σ ((Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_JR (f : R →ₐ[F] R') {m : ℕ} (J : Matrix (Fin m) (Fin m) E) :
    (JR R J).map (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom = JR R' J := by
  ext i j
  simp [JR, inclR]

end Tens

variable {D : D7}

theorem parts_inj (D : D7) (x y : AE D) (h1 : infPart D x = infPart D y) (h2 : finPart D x = finPart D y) : x = y := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  exact e.injective (Prod.ext (((he x).1.trans h1).trans (he y).1.symm) (((he x).2.trans h2).trans (he y).2.symm))

theorem parts_surj (D : D7) (a : Ainf D.host.F ⊗[D.host.F] D.host.E) (b : Af D.host.F ⊗[D.host.F] D.host.E) :
    ∃ x : AE D, infPart D x = a ∧ finPart D x = b := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨e.symm (a, b), (he _).1.symm.trans ?_, (he _).2.symm.trans ?_⟩ <;> simp

theorem mem_parts (V : HSp D) (g : GL (Fin V.rank) (AE D)) :
    g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram ↔
      Formalism.UG.bc (infPart D) g ∈ HR (Ainf D.host.F) D.sp.cm.sig V.gram ∧
        Formalism.UG.bc (finPart D) g ∈ HR (Af D.host.F) D.sp.cm.sig V.gram := by
  have := mem_iff (infPart D) (finPart D) (parts_inj D) (sigR _ D.sp.cm.sig) (sigR _ D.sp.cm.sig)
    (sigR _ D.sp.cm.sig) (map_sig _ _) (map_sig _ _) (JR _ V.gram) g
  rw [show (JR _ V.gram).map (infPart D) = JR _ V.gram from map_JR _ _,
    show (JR _ V.gram).map (finPart D) = JR _ V.gram from map_JR _ _] at this
  exact this

theorem ga_ext (V : HSp D) {g h : GA D V} (h1 : infHom V g = infHom V h) (h2 : finHom V g = finHom V h) : g = h :=
  Subtype.ext (gl_ext (infPart D) (finPart D) (parts_inj D) h1 h2)

theorem ga_glue (V : HSp D) (a : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E))
    (b : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) (ha : a ∈ HR (Ainf D.host.F) D.sp.cm.sig V.gram)
    (hb : b ∈ HR (Af D.host.F) D.sp.cm.sig V.gram) : ∃ g : GA D V, infHom V g = a ∧ finHom V g = b := by
  obtain ⟨g, h1, h2⟩ := gl_glue (infPart D) (finPart D) (parts_inj D) (parts_surj D) a b
  exact ⟨⟨g, (mem_parts V g).2 ⟨h1 ▸ ha, h2 ▸ hb⟩⟩, h1, h2⟩

theorem infHom_mem (V : HSp D) (g : GA D V) : infHom V g ∈ HR (Ainf D.host.F) D.sp.cm.sig V.gram :=
  ((mem_parts V (matHom V g)).1 (Subtype.property (p := fun x => x ∈ HR (AF D.host.F) D.sp.cm.sig V.gram) g)).1

theorem finHom_mem (V : HSp D) (g : GA D V) : finHom V g ∈ HR (Af D.host.F) D.sp.cm.sig V.gram :=
  ((mem_parts V (matHom V g)).1 (Subtype.property (p := fun x => x ∈ HR (AF D.host.F) D.sp.cm.sig V.gram) g)).2

theorem hermA_eq (V : HSp D) (x y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    GlobalTheory.AdLat.hermA (cF D) V.gramᵀ x y =
      Formalism.UG.hform (sigR (Af D.host.F) D.sp.cm.sig) (JR (Af D.host.F) V.gram) y x := by
  unfold GlobalTheory.AdLat.hermA Formalism.UG.hform
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  change x b * (JR (Af D.host.F) V.gram a b) * sigR (Af D.host.F) D.sp.cm.sig (y a) = _
  ring

theorem real_finite_split : ∀ (D : D7) (V : HSp D), (∀ h : GA D V, ∃ a ∈ GinfC V, ∃ k ∈ GfC V, h = a * k) ∧ (∀ a ∈ GinfC V, ∀ k ∈ GfC V, a * k = k * a) ∧ (∀ h : GA D V, h ∈ GinfC V → h ∈ GfC V → h = 1) ∧ (∀ g : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E), (∀ x y, GlobalTheory.AdLat.hermA (cF D) V.gramᵀ (g.1 *ᵥ x) (g.1 *ᵥ y) = GlobalTheory.AdLat.hermA (cF D) V.gramᵀ x y) → ∃ k ∈ GfC V, finHom V k = g) ∧ ∀ g : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E), g ∈ HR (Ainf D.host.F) D.sp.cm.sig V.gram → ∃ a ∈ GinfC V, infHom V a = g := by
  intro D V
  refine ⟨fun h => ?_, fun a ha k hk => ?_, fun h h1 h2 => ?_, fun g hg => ?_, fun g hg => ?_⟩
  · obtain ⟨a, a1, a2⟩ := ga_glue V _ 1 (infHom_mem V h) (one_mem _)
    obtain ⟨k, k1, k2⟩ := ga_glue V 1 _ (one_mem _) (finHom_mem V h)
    refine ⟨a, a2, k, k1, ga_ext V ?_ ?_⟩
    · rw [map_mul, a1, k1, mul_one]
    · rw [map_mul, a2, k2, one_mul]
  · have a2 : finHom V a = 1 := ha
    have k1 : infHom V k = 1 := hk
    refine ga_ext V ?_ ?_
    · rw [map_mul, map_mul, k1, mul_one, one_mul]
    · rw [map_mul, map_mul, a2, mul_one, one_mul]
  · have a2 : finHom V h = 1 := h1
    have k1 : infHom V h = 1 := h2
    exact ga_ext V (by rw [k1, map_one]) (by rw [a2, map_one])
  · have hm : g ∈ HR (Af D.host.F) D.sp.cm.sig V.gram :=
      mem_of_form _ _ g fun x y => by rw [← hermA_eq, ← hermA_eq, hg]
    obtain ⟨k, k1, k2⟩ := ga_glue V 1 g (one_mem _) hm
    exact ⟨k, k1, k2⟩
  · obtain ⟨a, a1, a2⟩ := ga_glue V g 1 hg (one_mem _)
    exact ⟨a, a2, a1⟩

end GlobalTheory.UnitarySplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplitStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicUnitary_eq_real_mul_finite_split : ∀ (D : D7) (V : HSp D), (∀ h : GA D V, ∃ a ∈ GinfC V, ∃ k ∈ GfC V, h = a * k) ∧ (∀ a ∈ GinfC V, ∀ k ∈ GfC V, a * k = k * a) ∧ (∀ h : GA D V, h ∈ GinfC V → h ∈ GfC V → h = 1) ∧ (∀ g : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E), (∀ x y, GlobalTheory.AdLat.hermA (cF D) V.gramᵀ (g.1 *ᵥ x) (g.1 *ᵥ y) = GlobalTheory.AdLat.hermA (cF D) V.gramᵀ x y) → ∃ k ∈ GfC V, finHom V k = g) ∧ ∀ g : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E), g ∈ HR (Ainf D.host.F) D.sp.cm.sig V.gram → ∃ a ∈ GinfC V, infHom V a = g := by
  first | exact @GlobalTheory.UnitarySplit.real_finite_split | exact GlobalTheory.UnitarySplit.real_finite_split | (intros; apply GlobalTheory.UnitarySplit.real_finite_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem hT_symm_equivFun {D : D7} (V : HSp D) (x y : Fin V.rank → D.host.E) :
    V.hT (V.frame.equivFun.symm x) (V.frame.equivFun.symm y) =
      ∑ a, ∑ b, y a * V.gramᵀ a b * star (x b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply, map_smulₛₗ,
    LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, Finset.mul_sum, RingHom.id_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Matrix.transpose_apply, HSpace.gram]
  ring

theorem mem_latC {D : D7} (V : HSp D) (v : Fin V.rank → D.host.E) :
    v ∈ latC V ↔ V.frame.equivFun.symm v ∈ V.L0 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨_, h, V.frame.equivFun.apply_symm_apply v⟩

theorem gram_transpose_det_ne_zero {D : D7} (V : HSp D) : V.gramᵀ.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
  apply hv
  have h1 : V.frame.equivFun.symm v = 0 := by
    apply V.nondeg.2
    intro x
    obtain ⟨x, rfl⟩ := V.frame.equivFun.symm.surjective x
    rw [hT_symm_equivFun, Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [← Finset.sum_mul]
    have : ∑ a, v a * V.gramᵀ a b = 0 := congrFun h0 b
    rw [this, zero_mul]
  exact V.frame.equivFun.symm.map_eq_zero_iff.1 h1

theorem latHat_eq_hat_and_gram :
    ∀ (D : D7) (V : HSp D), latHat V = GlobalTheory.AdLat.hat D.host.F (latC V : Set (Fin V.rank → D.host.E)) ∧ (∀ v, finVec V v = GlobalTheory.AdLat.fv D.host.F v) ∧ (latC V).FG ∧ Submodule.span D.host.E (latC V : Set (Fin V.rank → D.host.E)) = ⊤ ∧ (∀ x, cF D (cF D x) = x) ∧ (∀ x, cF D x = cc x) ∧ cF D ≠ 1 ∧ (∀ a b, cF D (V.gramᵀ a b) = V.gramᵀ b a) ∧ V.gramᵀ.det ≠ 0 ∧ (∀ x y, V.hT (V.frame.equivFun.symm x) (V.frame.equivFun.symm y) = -herm (-V.gramᵀ) y x) ∧ ∀ v : Fin V.rank → D.host.E, (∀ y ∈ latC V, (∑ a, ∑ b, v a * V.gramᵀ a b * cF D (y b)) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ↔ v ∈ latC V := by
  intro D V
  refine ⟨?_, fun v => rfl, ?_, ?_, fun x => star_star x, fun x => rfl, ?_, ?_,
    gram_transpose_det_ne_zero V, ?_, ?_⟩
  · unfold latHat GlobalTheory.AdLat.hat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
  · exact V.standardTuple_isLattice.fg.map _
  · rw [eq_top_iff]
    intro v _
    obtain ⟨x, rfl⟩ := V.frame.equivFun.surjective v
    have hspan : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) <
          Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨z, hz, hz₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e z ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
          Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
        intro y hy
        have hzy : V.hT (e z) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩)
            (LinearMap.mem_ker.mp hz)
        have hyz : V.hT y (e z) = 0 := by
          have hh := V.herm.eq (e z) y
          simpa [hzy] using hh.symm
        simp [hyz]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e z)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hz₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
    have hx : x ∈ Submodule.span D.host.E (V.L0 : Set V.V) := by
      rw [hspan]; trivial
    have := Submodule.mem_map_of_mem (f := V.frame.equivFun.toLinearMap) hx
    rw [Submodule.map_span] at this
    exact this
  · intro h
    apply IsCMField.complexConj_ne_one D.host.E
    refine AlgEquiv.ext fun x => ?_
    have hx : cF D x = x := by rw [h]; rfl
    exact hx
  · intro a b
    exact V.herm.eq _ _
  · intro x y
    rw [hT_symm_equivFun]
    simp only [herm, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib, neg_neg]
    rfl
  · intro v
    rw [mem_latC]
    conv_rhs => rw [← V.baseLattice_isUnimodular]
    have key : V.frame.equivFun.symm v ∈ Formalism.HermitianLatticesTheory.dual V.hT V.L0 ↔
        ∀ y ∈ V.L0, V.hT y (V.frame.equivFun.symm v) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
      rfl
    rw [key]
    constructor
    · intro h y hy
      obtain ⟨y, rfl⟩ := V.frame.equivFun.symm.surjective y
      rw [hT_symm_equivFun, Submodule.mem_one]
      exact (FractionalIdeal.mem_one_iff _).1 (h y ((mem_latC V y).2 hy))
    · intro h y hy
      have := h _ ((mem_latC V y).1 hy)
      rw [hT_symm_equivFun, Submodule.mem_one] at this
      exact (FractionalIdeal.mem_one_iff _).2 this

end GlobalTheory.Member
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGramStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram : ∀ (D : D7) (V : HSp D), latHat V = GlobalTheory.AdLat.hat D.host.F (latC V : Set (Fin V.rank → D.host.E)) ∧ (∀ v, finVec V v = GlobalTheory.AdLat.fv D.host.F v) ∧ (latC V).FG ∧ Submodule.span D.host.E (latC V : Set (Fin V.rank → D.host.E)) = ⊤ ∧ (∀ x, cF D (cF D x) = x) ∧ (∀ x, cF D x = cc x) ∧ cF D ≠ 1 ∧ (∀ a b, cF D (V.gramᵀ a b) = V.gramᵀ b a) ∧ V.gramᵀ.det ≠ 0 ∧ (∀ x y, V.hT (V.frame.equivFun.symm x) (V.frame.equivFun.symm y) = -herm (-V.gramᵀ) y x) ∧ ∀ v : Fin V.rank → D.host.E, (∀ y ∈ latC V, (∑ a, ∑ b, v a * V.gramᵀ a b * cF D (y b)) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ↔ v ∈ latC V := by
  first | exact @GlobalTheory.Member.latHat_eq_hat_and_gram | exact GlobalTheory.Member.latHat_eq_hat_and_gram | (intros; apply GlobalTheory.Member.latHat_eq_hat_and_gram <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem exists_algebraMap_of_sigR_fixed {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    (htr : ∀ x : E, ∃ t : F, algebraMap F E t = x + σ x) (z : R ⊗[F] E) (hz : sigR R σ z = z) :
    ∃ a : R, algebraMap R (R ⊗[F] E) a = z := by
  have hT : ∀ z : R ⊗[F] E, ∃ t : R, z + sigR R σ z = t ⊗ₜ 1 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a x =>
      obtain ⟨t, ht⟩ := htr x
      refine ⟨t • a, ?_⟩
      have h : sigR R σ (a ⊗ₜ x) = a ⊗ₜ σ x := by simp [sigR]
      rw [h, ← TensorProduct.tmul_add, ← ht, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨t, ht⟩ := hx
      obtain ⟨t', ht'⟩ := hy
      refine ⟨t + t', ?_⟩
      rw [map_add (f := _), TensorProduct.add_tmul, ← ht, ← ht']; ring
  obtain ⟨t, ht⟩ := hT z
  refine ⟨(2 : F)⁻¹ • t, ?_⟩
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    ← TensorProduct.smul_tmul', ← ht, hz, ← two_smul F z, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

theorem exists_unit_of_sigR_fixed {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    (htr : ∀ x : E, ∃ t : F, algebraMap F E t = x + σ x) (z : (R ⊗[F] E)ˣ)
    (hz : sigR R σ (z : R ⊗[F] E) = z) :
    ∃ a : Rˣ, Units.map (algebraMap R (R ⊗[F] E)).toMonoidHom a = z := by
  have hz' : sigR R σ ((z⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E) = (z⁻¹ : (R ⊗[F] E)ˣ) := by
    apply z.isUnit.mul_left_cancel
    conv_lhs => rw [← hz, ← map_mul]
    simp
  obtain ⟨a, ha⟩ := exists_algebraMap_of_sigR_fixed R σ htr _ hz
  obtain ⟨b, hb⟩ := exists_algebraMap_of_sigR_fixed R σ htr _ hz'
  have hinj : Function.Injective (algebraMap R (R ⊗[F] E)) :=
    Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective
  have hab : a * b = 1 := hinj (by rw [map_mul, ha, hb, map_one]; simp)
  exact ⟨⟨a, b, hab, by rw [mul_comm, hab]⟩, Units.ext ha⟩

theorem exists_root_of_norm_one {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x)
    (hne : ∃ y, σ y ≠ y) (u : E) (hu : σ u * u = 1) : ∃ x : Eˣ, (x : E) = u * σ x := by
  by_cases h : 1 + u = 0
  · obtain ⟨y, hy⟩ := hne
    refine ⟨Units.mk0 (y - σ y) (sub_ne_zero.2 hy.symm), ?_⟩
    rw [Units.val_mk0, map_sub, hσ]
    linear_combination (y - σ y) * h
  · refine ⟨Units.mk0 (1 + u) h, ?_⟩
    rw [Units.val_mk0, map_add (f := _), map_one]
    linear_combination - hu

theorem isDetRoot_mul {D : D7} (V : HSp D) (g g' : GA D V) (x x' : (AE D)ˣ) (hx : IsDetRoot V g x)
    (hx' : IsDetRoot V g' x') : IsDetRoot V (g * g') (x * x') := by
  unfold IsDetRoot at *
  rw [Units.val_mul, (matHom V).map_mul, Units.val_mul, Matrix.det_mul, RingHom.map_mul]
  conv_lhs => rw [hx, hx']
  ring

theorem isDetRoot_laws : ∀ (D : D7) (V : HSp D), (∀ g : GA D V, ∃ x, IsDetRoot V g x) ∧ (∀ g x x', IsDetRoot V g x → IsDetRoot V g x' → ∃ a, x' = x * idF D a) ∧ (∀ γ ∈ GQ V, ∃ x : D.host.Eˣ, IsDetRoot V γ (Units.map (incA D).toMonoidHom x)) ∧ ∀ g g' x x', IsDetRoot V g x → IsDetRoot V g' x' → IsDetRoot V (g * g') (x * x') := by
  intro D V
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  refine ⟨GlobalTheory.RecDict.exists_isDetRoot D V, ?_, ?_, ?_⟩
  · intro g x x' hx hx'
    have htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
      intro x
      apply (D.sp.cm.fixed _).1
      change D.sp.cm.sig _ = _
      rw [map_add (f := _), hσ, add_comm]
    unfold IsDetRoot at hx hx'
    obtain ⟨a, ha⟩ := exists_unit_of_sigR_fixed (AF D.host.F) D.sp.cm.sig htr (x⁻¹ * x') (by
      apply (x.isUnit.map (sigR (AF D.host.F) D.sp.cm.sig)).mul_left_cancel
      apply x.isUnit.mul_left_cancel
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel_left, mul_left_comm, ← Units.val_mul, mul_inv_cancel_left]
      linear_combination (sigR (AF D.host.F) D.sp.cm.sig (x' : AE D)) * hx -
        (sigR (AF D.host.F) D.sp.cm.sig (x : AE D)) * hx')
    refine ⟨a, ?_⟩
    unfold idF
    rw [ha, mul_inv_cancel_left]
  · intro γ hγ
    obtain ⟨γ', -, hγ'⟩ := hγ
    have hdet : (Formalism.L2.Theta.mt V γ).det = incA D (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det := by
      rw [RingHom.map_det]
      congr 1
      exact congrArg Units.val hγ'.symm
    have hc : ∀ y, cA D (incA D y) = incA D (D.sp.cm.sig y) := by
      intro y; simp [cA, sigR, inclR]
    have hinj : Function.Injective (incA D) :=
      Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
    have hu := det_conj_mul V γ
    rw [hdet, hc, ← map_mul, ← map_one (incA D)] at hu
    obtain ⟨x, hx⟩ := exists_root_of_norm_one (D.sp.cm.sig : D.host.E →+* D.host.E) hσ
      (GlobalTheory.RecDict.cmData_sig_ne_id D.sp.cm) _ (hinj hu)
    refine ⟨x, ?_⟩
    have key : incA D (x : D.host.E) = (Formalism.L2.Theta.mt V γ).det * cA D (incA D (x : D.host.E)) := by
      rw [hdet, hc, ← map_mul]
      exact congrArg _ hx
    unfold IsDetRoot
    rw [Units.coe_map]
    exact key
  · exact isDetRoot_mul V

end GlobalTheory.Member
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePartPreservesFormDetNormOne
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePartPreservesFormDetNormOne
namespace GlobalTheory.Member

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem unit_form_inv {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J g : Matrix (Fin n) (Fin n) A)
    (h : Formalism.UG.cT σ g * J * g = J) (x y : Fin n → A) :
    ∑ a, ∑ b, (g *ᵥ x) a * J b a * σ ((g *ᵥ y) b) = ∑ a, ∑ b, x a * J b a * σ (y b) := by
  have key : ∀ (u v : Fin n → A), ∑ a, ∑ b, u a * J b a * σ (v b) = (σ ∘ v) ⬝ᵥ (J *ᵥ u) := by
    intro u v
    rw [Finset.sum_comm]
    simp only [dotProduct, Matrix.mulVec, Function.comp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
  have h2 : σ ∘ (g *ᵥ y) = (σ ∘ y) ᵥ* Formalism.UG.cT σ g := by
    funext b
    simp [Formalism.UG.cT, Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]
  rw [key, key, h2, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem unit_det_norm {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J g : Matrix (Fin n) (Fin n) A)
    (hJ : IsUnit J.det) (h : Formalism.UG.cT σ g * J * g = J) : g.det * σ g.det = 1 := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose] at h1
  have h2 : (g.map σ).det = σ g.det := (σ.map_det g).symm
  rw [h2] at h1
  apply hJ.mul_left_cancel
  linear_combination h1

theorem unitary_map {F E R S : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing S]
    [Algebra F S] (φ : R →ₐ[F] S) (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (h : Formalism.UG.cT (sigR R σ) g * JR R J * g = JR R J) :
    Formalism.UG.cT (sigR S σ) (g.map (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom) * JR S J *
      g.map (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom = JR S J := by
  set π : R ⊗[F] E →+* S ⊗[F] E := (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom with hπ
  have hs : ∀ z, π (sigR R σ z) = sigR S σ (π z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [hπ, sigR]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hJ : (JR R J).map π = JR S J := by
    ext i j
    simp [hπ, JR, inclR]
  have hc : (Formalism.UG.cT (sigR R σ) g).map π = Formalism.UG.cT (sigR S σ) (g.map π) := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, hs]
  have h2 := congrArg (fun M => Matrix.map M π) h
  simp only [Matrix.map_mul] at h2
  rw [hJ, hc] at h2
  exact h2

theorem finHom_unitary {D : D7} (V : HSp D) (g : GA D V) :
    Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) (finHom V g).1 * JR (F := D.host.F) (Af D.host.F) V.gram * (finHom V g).1 =
      JR (F := D.host.F) (Af D.host.F) V.gram :=
  unitary_map (sndA D.host.F) D.sp.cm.sig V.gram (matHom V g).1
    (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2

theorem finHom_herm_det : ∀ (D : D7) (V : HSp D), ∀ g : GA D V, (∀ x y, GlobalTheory.AdLat.hermA (cF D) V.gramᵀ ((finHom V g).1 *ᵥ x) ((finHom V g).1 *ᵥ y) = GlobalTheory.AdLat.hermA (cF D) V.gramᵀ x y) ∧ (finHom V g).1.det * GlobalTheory.AdLat.sg (Af D.host.F) (cF D) (finHom V g).1.det = 1 ∧ ((matHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det * sigR (AF D.host.F) D.sp.cm.sig ((matHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det = 1 := by
  intro D V g
  have hu : ∀ (R : Type) [CommRing R] [Algebra D.host.F R], IsUnit (JR (F := D.host.F) R V.gram).det := by
    intro R _ _
    have e : (JR (F := D.host.F) R V.gram).det = inclR (F := D.host.F) R V.gram.det := ((inclR (F := D.host.F) R).map_det V.gram).symm
    rw [e]
    exact (isUnit_iff_ne_zero.2 (gram_det_ne V)).map _
  refine ⟨fun x y => ?_, ?_, ?_⟩
  · exact unit_form_inv _ _ _ (finHom_unitary V g) x y
  · exact unit_det_norm _ _ _ (hu _) (finHom_unitary V g)
  · exact unit_det_norm _ _ _ (hu _) (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2

end GlobalTheory.Member
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePartPreservesFormDetNormOneStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePart_preserves_form_det_norm_one : ∀ (D : D7) (V : HSp D), ∀ g : GA D V, (∀ x y, GlobalTheory.AdLat.hermA (cF D) V.gramᵀ ((finHom V g).1 *ᵥ x) ((finHom V g).1 *ᵥ y) = GlobalTheory.AdLat.hermA (cF D) V.gramᵀ x y) ∧ (finHom V g).1.det * GlobalTheory.AdLat.sg (Af D.host.F) (cF D) (finHom V g).1.det = 1 ∧ ((matHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det * sigR (AF D.host.F) D.sp.cm.sig ((matHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det = 1 := by
  first | exact @GlobalTheory.Member.finHom_herm_det | exact GlobalTheory.Member.finHom_herm_det | (intros; apply GlobalTheory.Member.finHom_herm_det <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RealAdelesCmFieldEquivComplexCmType
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RealAdelesCmFieldEquivComplexCmType
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem infiniteAdele_bijective : ∀ (D : D7), (∃ θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ))) ∧ ∀ (θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ)) → (∀ τ, Continuous (θ τ)) ∧ (∀ τ z, θ τ (sigR (Ainf D.host.F) D.sp.cm.sig z) = starRingEnd ℂ (θ τ z)) ∧ Function.Bijective (fun (z : Ainf D.host.F ⊗[D.host.F] D.host.E) (τ : {τ : D.host.E →+* ℂ // τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD}) => θ τ.1 z) := by
  intro D
  have hτ : ∀ (τ : D.host.E →+* ℂ) (x : D.host.E), τ (cF D x) = starRingEnd ℂ (τ x) :=
    fun τ x => IsCMField.complexEmbedding_complexConj D.host.E τ x
  have hc : cF D ≠ 1 := by
    intro h
    have h0 := conj_of_sq (d_pos D) (sq_emb D D.host.φ₀)
    have h1 := hτ D.host.φ₀ D.host.sqrtMinusD
    rw [h, AlgEquiv.one_apply] at h1
    have h2 := congrArg Complex.im h1
    rw [Complex.conj_im] at h2
    exact h0.2.2 (by linarith)
  have H := GlobalTheory.InfAdeleCM.infAdele_tensor_bijective D.host.F D.host.E (cF D) D.sp.cm.deg2 hc D.sp.cm.totReal hτ
  refine ⟨?_, fun θ hθ => ?_⟩
  · choose θ hθ using H.1
    exact ⟨θ, hθ⟩
  · obtain ⟨h1, h2, h3⟩ := H.2 θ hθ
    refine ⟨h1, h2, h3 {τ | τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD} fun τ => ?_⟩
    have := cm_type_mem_iff_conj_not_mem D τ
    rw [mem_cm_type_iff, mem_cm_type_iff] at this
    exact this

end GlobalTheory.Member
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RealAdelesCmFieldEquivComplexCmTypeStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realAdeles_cmField_equiv_complex_cmType : ∀ (D : D7), (∃ θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ))) ∧ ∀ (θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ)) → (∀ τ, Continuous (θ τ)) ∧ (∀ τ z, θ τ (sigR (Ainf D.host.F) D.sp.cm.sig z) = starRingEnd ℂ (θ τ z)) ∧ Function.Bijective (fun (z : Ainf D.host.F ⊗[D.host.F] D.host.E) (τ : {τ : D.host.E →+* ℂ // τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD}) => θ τ.1 z) := by
  first | exact @GlobalTheory.Member.infiniteAdele_bijective | exact GlobalTheory.Member.infiniteAdele_bijective | (intros; apply GlobalTheory.Member.infiniteAdele_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOpenChartFramedPointTestRing
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOpenChartFramedPointTestRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem isTypeFn_of_enum {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : IsTypeFn H Dw.p Dw.q (fun j => (e j).1) := by
  intro τ
  have hcard : Nat.card {i // (e i).1 = τ} = Dw.mult τ := by
    have e2 : {i // (e i).1 = τ} ≃ {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ} :=
      e.subtypeEquiv (fun _ => Iff.rfl)
    have e3 : {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ} ≃ Fin (Dw.mult τ) := Equiv.sigmaSubtype τ
    rw [Nat.card_congr (e2.trans e3), Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine hcard.trans ?_
    unfold Datum.mult
    rw [if_pos h]
  · refine hcard.trans ?_
    unfold Datum.mult
    rw [if_neg h]

theorem exists_openChart_testRing : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (z : Xo.XF c), ∃ (p : TRing c.F) (j : Sp p.R ⟶ Xo.XF c) (y₀ : FrPt Xo c p.R), OpenChart j y₀ ∧ z ∈ Set.range j := by
  intro hS E _ _ _ H Dw l Xo c z
  classical
  let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (Dw.mult τ))).symm
  obtain ⟨R, _, _, jR, o, v, th, hft, hred, hjR, ⟨q, hq⟩, hs, ⟨m⟩, hv, hev, hth, -⟩ :=
    GlobalTheory.ModuliChart.exists_chart_eigenframe hS E H Dw l Xo c _ _ (isTypeFn_of_enum Dw e) z
  let x : Sp R ⟶ Xo.X := jR ≫ pullback.fst _ _
  have hb : TanBasis x (fun i => (v i).left ≫ m.cm.F) :=
    ((GlobalTheory.T.lieBasis_iff_tangentBasis_pullback_universal E H Dw l Xo R x o.t.G m.cm.F m.cart).2 _ v).1 hv
  let u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left) :=
    fun τ i => (v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F
  have htan : ∀ τ i, IsTanAt x (u τ i) := fun τ i => hb.1 _
  have heig : ∀ τ i, IsEigAt c τ (u τ i) := by
    intro τ i a
    have h := hev (e.symm ⟨τ, i⟩) a
    simp only [Equiv.apply_symm_apply] at h
    have h' : (v (e.symm ⟨τ, i⟩)).left ≫ (o.t.act.act a).left =
      spMap (epsMul (algebraMap c.F R (embK c τ a))) ≫ (v (e.symm ⟨τ, i⟩)).left := h
    show ((v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F) ≫ _ = _ ≫ (v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F
    rw [Category.assoc, ← m.act a, ← Category.assoc, h', Category.assoc]
  have hb' : TanBasis x (fun j => u (e j).1 (e j).2) := by
    have : (fun j => u (e j).1 (e j).2) = fun i => (v i).left ≫ m.cm.F := by
      funext j
      show (v (e.symm (e j))).left ≫ m.cm.F = _
      rw [Equiv.symm_apply_apply]
    rw [this]; exact hb
  have hbasis := (GlobalTheory.T.eigenBasis_iff_tangentBasis E H Dw l Xo c R x u _ e htan heig).2 hb'
  obtain ⟨s, hsn⟩ := GlobalTheory.T.exists_fibreSection_nowhereZero_of_pullbackTriple E H Dw l Xo R x o.t m.toSABMap th hth
  have hgen := GlobalTheory.T.fibreSectionGenerates_of_nowhereZero hS E H Dw l Xo R x s hsn
  have hx : x ≫ Xo.s = sOf c R := by
    have h1 : x ≫ Xo.s = (jR ≫ pullback.snd _ _) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
      rw [Category.assoc, Category.assoc]
      exact congrArg (jR ≫ ·) pullback.condition
    rw [h1, hs, sOf]
    exact (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)).symm
  let y : FrPt Xo c R := ⟨x, hx, u, htan, heig, hbasis, s, hgen⟩
  obtain ⟨p, ⟨f⟩⟩ := (GlobalTheory.reduced_finiteType_iff_testRing c.F).1 R hft hred
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hS E H Dw l Xo c R p.R f.symm.toAlgHom y
  have hiso : IsIso (spMap f.symm.toAlgHom.toRingHom) :=
    inferInstanceAs (IsIso (Spec.map f.symm.toRingEquiv.toCommRingCatIso.hom))
  refine ⟨p, spMap f.symm.toAlgHom.toRingHom ≫ jR, y₀, ⟨inferInstance, ?_, ?_⟩, ?_⟩
  · rw [hy₀.1, Category.assoc]
  · rw [Category.assoc, hs]
    refine (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)).symm.trans (congrArg Spec.map ?_)
    ext a
    exact f.symm.commutes a
  · obtain ⟨q', hq'⟩ := (spMap f.symm.toAlgHom.toRingHom).surjective q
    exact ⟨q', by rw [Scheme.Hom.comp_apply, hq', hq]⟩

end GlobalTheory.Frames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOpenChartFramedPointTestRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openChart_framedPoint_testRing : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (z : Xo.XF c), ∃ (p : TRing c.F) (j : Sp p.R ⟶ Xo.XF c) (y₀ : FrPt Xo c p.R), OpenChart j y₀ ∧ z ∈ Set.range j := by
  first | exact @GlobalTheory.Frames.exists_openChart_testRing | exact GlobalTheory.Frames.exists_openChart_testRing | (intros; apply GlobalTheory.Frames.exists_openChart_testRing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RationalPointsAdelicUnitaryEqUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RationalPointsAdelicUnitaryEqUnitary
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member.RatElt

theorem hform_eq {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (x y : Fin n → A) :
    Formalism.UG.hform σ J x y = (σ ∘ x) ⬝ᵥ (J *ᵥ y) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J g : Matrix (Fin n) (Fin n) A)
    (x y : Fin n → A) :
    Formalism.UG.hform σ J (g *ᵥ x) (g *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ g * J * g) x y := by
  have h : σ ∘ (g *ᵥ x) = (g.map σ) *ᵥ (σ ∘ x) := by
    funext i; exact RingHom.map_mulVec σ g x i
  rw [hform_eq, hform_eq, h, Formalism.UG.cT, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec (σ ∘ x) (g.map σ)ᵀ, Matrix.vecMul_transpose]

theorem hform_single {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    Formalism.UG.hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  have h : σ ∘ (Pi.single i 1 : Fin n → A) = Pi.single i 1 := by
    funext k; by_cases hk : k = i
    · subst hk; simp
    · simp [Pi.single_eq_of_ne hk]
  rw [hform_eq, h]; simp

theorem mem_UJ_iff {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A)
    (g : GL (Fin n) A) :
    g ∈ Formalism.UG.UJ σ J ↔ ∀ x y, Formalism.UG.hform σ J ((g : Matrix (Fin n) (Fin n) A) *ᵥ x)
      ((g : Matrix (Fin n) (Fin n) A) *ᵥ y) = Formalism.UG.hform σ J x y := by
  change Formalism.UG.cT σ (g : Matrix (Fin n) (Fin n) A) * J * (g : Matrix (Fin n) (Fin n) A) = J ↔ _
  constructor
  · intro h x y; rw [hform_mulVec, h]
  · intro h; ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    rwa [hform_mulVec, hform_single, hform_single] at this

theorem bc_mem_HR_iff {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    [Nontrivial R] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) E) :
    Formalism.UG.bc (inclR (F := F) R) g ∈ HR R σ J ↔ g ∈ Formalism.UG.UJ (σ : E →+* E) J := by
  have hinj : Function.Injective (inclR (F := F) (E := E) R) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F R).injective
  have hc : Formalism.UG.cT (sigR R σ) ((g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) R)) =
      (Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E)).map (inclR (F := F) R) := by
    ext i j; simp [Formalism.UG.cT, sigR, inclR]
  change Formalism.UG.cT (sigR R σ) ((g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) R)) * J.map (inclR (F := F) R) *
      (g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) R) = J.map (inclR (F := F) R) ↔
    Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E) * J * (g : Matrix (Fin n) (Fin n) E) = J
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul]
  exact (Matrix.map_injective hinj).eq_iff

theorem bc_map_incl {F E : Type} [Field F] [Field E] [Algebra F E] {R S : Type} [CommRing R] [Algebra F R]
    [CommRing S] [Algebra F S] (φ : R →ₐ[F] S) {n : ℕ} (g : GL (Fin n) E) :
    (Formalism.UG.bc (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom (Formalism.UG.bc (inclR (F := F) R) g)).1 =
      (g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) S) := by
  ext i j
  simp [Formalism.UG.bc, inclR]

variable {D : D7}

theorem herm_eq (V : HSp D) (x y : Fin V.rank → D.host.E) :
    herm (-V.gramᵀ) x y = - Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram y x := by
  unfold herm Formalism.UG.hform
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  change x b * (-V.gram a b) * cc (y a) = -(cc (y a) * V.gram a b * x b)
  ring

theorem herm_iff (V : HSp D) (g : GL (Fin V.rank) D.host.E) :
    (∀ u v, herm (-V.gramᵀ) ((g : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ u)
      ((g : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = herm (-V.gramᵀ) u v) ↔
    Formalism.UG.bc (incA D) g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
  have : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  rw [bc_mem_HR_iff, mem_UJ_iff]
  simp only [herm_eq, neg_inj]
  exact forall_comm

theorem fin_eq {V : HSp D} {γ : GA D V} {γ' : GL (Fin V.rank) D.host.E} (h : IsRat V γ γ') :
    (finHom V γ).1 = (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (Af D.host.F)) := by
  unfold finHom IsRat at *
  rw [MonoidHom.comp_apply, h]
  exact bc_map_incl _ _

theorem inf_eq {V : HSp D} {γ : GA D V} {γ' : GL (Fin V.rank) D.host.E} (h : IsRat V γ γ') :
    (infHom V γ).1 = (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (Ainf D.host.F)) := by
  unfold infHom IsRat at *
  rw [MonoidHom.comp_apply, h]
  exact bc_map_incl _ _

theorem rational_elements : ∀ (D : D7) (V : HSp D), (∀ γ, γ ∈ GQ V ↔ ∃ γ', IsRat V γ γ') ∧ (∀ γ γ', IsRat V γ γ' → (∀ u v, herm (-V.gramᵀ) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ u) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = herm (-V.gramᵀ) u v)) ∧ (∀ γ' : GL (Fin V.rank) D.host.E, (∀ u v, herm (-V.gramᵀ) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ u) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = herm (-V.gramᵀ) u v) → ∃ γ, IsRat V γ γ') ∧ (∀ γ γ' δ δ', IsRat V γ γ' → IsRat V δ δ' → IsRat V (γ * δ) (γ' * δ') ∧ IsRat V γ⁻¹ γ'⁻¹) ∧ ∀ γ γ', IsRat V γ γ' → (∀ v, (finHom V γ).1 *ᵥ finVec V v = finVec V ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v)) ∧ ∀ τ θ, Formalism.MainNotions.StandardLattice.IsInfEmb τ θ → archM V θ γ = (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ := by
  intro D V
  have hmem : ∀ γ γ', IsRat V γ γ' → Formalism.UG.bc (incA D) γ' ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    intro γ γ' h
    rw [← h]; exact γ.2
  have : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  refine ⟨fun γ => ⟨?_, ?_⟩, fun γ γ' h => (herm_iff V γ').2 (hmem γ γ' h),
    fun γ' h => ⟨⟨_, (herm_iff V γ').1 h⟩, rfl⟩, fun γ γ' δ δ' h k => ⟨?_, ?_⟩, fun γ γ' h => ⟨fun v => ?_, fun τ θ hθ => ?_⟩⟩
  · rintro ⟨γ', -, h⟩
    exact ⟨γ', h.symm⟩
  · rintro ⟨γ', h⟩
    exact ⟨γ', (bc_mem_HR_iff _ _ _ _).1 (hmem γ γ' h), h.symm⟩
  · unfold IsRat at *
    rw [map_mul, map_mul, h, k]
  · unfold IsRat at *
    rw [map_inv, map_inv, h]
  · rw [fin_eq h]
    funext i
    exact (RingHom.map_mulVec (inclR (F := D.host.F) (Af D.host.F))
      (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) v i).symm
  · unfold archM
    rw [inf_eq h]
    ext i j
    exact hθ.1 _

end GlobalTheory.Member.RatElt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RationalPointsAdelicUnitaryEqUnitaryStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_points_adelicUnitary_eq_unitary : ∀ (D : D7) (V : HSp D), (∀ γ, γ ∈ GQ V ↔ ∃ γ', IsRat V γ γ') ∧ (∀ γ γ', IsRat V γ γ' → (∀ u v, herm (-V.gramᵀ) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ u) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = herm (-V.gramᵀ) u v)) ∧ (∀ γ' : GL (Fin V.rank) D.host.E, (∀ u v, herm (-V.gramᵀ) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ u) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = herm (-V.gramᵀ) u v) → ∃ γ, IsRat V γ γ') ∧ (∀ γ γ' δ δ', IsRat V γ γ' → IsRat V δ δ' → IsRat V (γ * δ) (γ' * δ') ∧ IsRat V γ⁻¹ γ'⁻¹) ∧ ∀ γ γ', IsRat V γ γ' → (∀ v, (finHom V γ).1 *ᵥ finVec V v = finVec V ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v)) ∧ ∀ τ θ, Formalism.MainNotions.StandardLattice.IsInfEmb τ θ → archM V θ γ = (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ := by
  first | exact @GlobalTheory.Member.RatElt.rational_elements | exact GlobalTheory.Member.RatElt.rational_elements | (intros; apply GlobalTheory.Member.RatElt.rational_elements <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniversalFrameClassifiesFramedPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniversalFrameClassifiesFramedPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem univFrame_classifies : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [Algebra c.F R] (A : Type) [CommRing A] [Algebra c.F A] (y₀ : FrPt Xo c R) (π : R →ₐ[c.F] A) (X : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A)) (s : Aˣ) (u : FrPt Xo c A), UnivFrame y₀ π X s u → ∀ (T : Type) [CommRing T] [Algebra c.F T] (z : FrPt Xo c T) (ψ : R →ₐ[c.F] T), z.x = spMap ψ.toRingHom ≫ y₀.x → ∃! a : A →ₐ[c.F] T, a.comp π = ψ ∧ FrMap a u z := by
  intro hS E _ _ _ H Dw l Xo c R _ _ A _ _ y₀ π X s u hu T _ _ z ψ hz
  obtain ⟨⟨-, hring⟩, u₀, hu₀, hchg⟩ := hu
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hS E H Dw l Xo c R T ψ y₀
  have hx₀ : z₀.x = spMap ψ.toRingHom ≫ y₀.x :=
    (((GlobalTheory.T.framedPoint_baseChange_unique_refl_iff E H Dw l Xo c R T ψ y₀).2.2 z₀).1 hz₀).1
  obtain ⟨hex, huniq⟩ := GlobalTheory.T.frameChange_exists_unique_of_same_point E H Dw l Xo c T z₀ z
  obtain ⟨g, a₀, hg, hgz⟩ := hex (hz.trans hx₀.symm)
  have key : ∀ k : A →ₐ[c.F] T, k.comp π = ψ →
      (FrMap k u z ↔ FrChg (fun τ => (X τ).map k) (k (s : A)) z₀ z) := by
    intro k hk
    obtain ⟨w, hw⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hS E H Dw l Xo c A T k u₀
    have hw' : FrMap (k.comp π) y₀ w := frMap_trans (Xo := Xo) (c := c) _ _ _ π k y₀ u₀ w hu₀ hw
    rw [hk] at hw'
    obtain rfl : w = z₀ := (GlobalTheory.T.framedPoint_baseChange_unique_refl_iff E H Dw l Xo c R T ψ y₀).1 w z₀ hw' hz₀
    exact GlobalTheory.T.frameChange_comm_baseChange E H Dw l Xo c A T k u₀ u w z X (s : A) hchg hw
  obtain ⟨k, ⟨hk, hkX, hks⟩, hku⟩ := hring T ψ g a₀ hg
  refine ⟨k, ⟨hk, (key k hk).2 ?_⟩, ?_⟩
  · have h1 : (fun τ => (X τ).map k) = g := funext hkX
    rw [h1, hks]
    exact hgz
  · rintro k' ⟨hk', hm⟩
    obtain ⟨h1, h2⟩ := huniq _ _ _ _ ((key k' hk').1 hm) hgz
    exact hku k' ⟨hk', fun τ => congrFun h1 τ, h2⟩

end GlobalTheory.Frames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniversalFrameClassifiesFramedPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universalFrame_classifies_framedPoints : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [Algebra c.F R] (A : Type) [CommRing A] [Algebra c.F A] (y₀ : FrPt Xo c R) (π : R →ₐ[c.F] A) (X : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A)) (s : Aˣ) (u : FrPt Xo c A), UnivFrame y₀ π X s u → ∀ (T : Type) [CommRing T] [Algebra c.F T] (z : FrPt Xo c T) (ψ : R →ₐ[c.F] T), z.x = spMap ψ.toRingHom ≫ y₀.x → ∃! a : A →ₐ[c.F] T, a.comp π = ψ ∧ FrMap a u z := by
  first | exact @GlobalTheory.Frames.univFrame_classifies | exact GlobalTheory.Frames.univFrame_classifies | (intros; apply GlobalTheory.Frames.univFrame_classifies <;> assumption)
end
end
