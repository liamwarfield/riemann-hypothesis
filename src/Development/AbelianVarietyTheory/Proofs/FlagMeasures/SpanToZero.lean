module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactUnitaryFiniteInvariantSubspace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommensurableCosetUnionContentIndependentNonneg

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordUnip

private lemma flag_iff_lemma {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] (A : ℕ → Submodule E V)
    (h0 : A 0 = ⊥) (hm : ∀ j, A j ≤ A (j + 1)) (r : ℕ) (g : V ≃ₗ[E] V)
    (hg : ∀ j, j < r → ∀ v ∈ A (j + 1), g v - v ∈ A j) :
    ∀ j, j ≤ r → ∀ u ∈ A j, ∃ w ∈ A j, g w = u := by
  intro j
  induction j with
  | zero =>
    intro _ u hu
    rw [h0, Submodule.mem_bot] at hu
    exact ⟨0, by rw [h0]; exact Submodule.zero_mem _, by rw [hu, map_zero]⟩
  | succ i ih =>
    intro hi u hu
    obtain ⟨w, hw, hgw⟩ := ih (by omega) (g u - u) (hg i (by omega) u hu)
    refine ⟨u - w, Submodule.sub_mem _ hu (hm i hw), ?_⟩
    rw [map_sub, hgw]
    abel

lemma flag_iff {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] (A : ℕ → Submodule E V)
    (h0 : A 0 = ⊥) (hm : ∀ j, A j ≤ A (j + 1)) (r : ℕ) (g : V ≃ₗ[E] V)
    (hg : ∀ j, j < r → ∀ v ∈ A (j + 1), g v - v ∈ A j) :
    ∀ j, j ≤ r → ∀ v, g v ∈ A j ↔ v ∈ A j := by
  intro j hj v
  constructor
  · intro hv
    obtain ⟨w, hw, hgw⟩ := flag_iff_lemma A h0 hm r g hg j hj (g v) hv
    rw [← g.injective hgw]
    exact hw
  · intro hv
    cases j with
    | zero =>
      rw [h0, Submodule.mem_bot] at hv ⊢
      rw [hv, map_zero]
    | succ i =>
      have hd := hg i (by omega) v hv
      have h2 : g v = (g v - v) + v := by abel
      rw [h2]
      exact Submodule.add_mem _ (hm i hd) hv

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}

lemma spanTo_zero (S : Frames M.L r k) (f : Fin (r + 1) → S.V) : S.spanTo f 0 = ⊥ := by
  simp [Frames.spanTo]

lemma spanTo_mono (S : Frames M.L r k) (f : Fin (r + 1) → S.V) (j : ℕ) :
    S.spanTo f j ≤ S.spanTo f (j + 1) := by
  unfold Frames.spanTo
  apply Submodule.span_mono
  apply Set.image_mono
  intro i hi
  simp only [Set.mem_ofPred_eq] at hi ⊢
  omega

lemma mem_Nof (S : Frames M.L r k) (f : Fin (r + 1) → S.V) (g : S.GLV) :
    g ∈ S.Nof f ↔ (∀ x y, S.h (g x) (g y) = S.h x y) ∧
      (∀ j, j < r → ∀ v ∈ S.spanTo f (j + 1), g v - v ∈ S.spanTo f j) ∧
      ∀ v ∈ perp M.L S.Hm (S.spanTo f r), g v - v ∈ S.spanTo f r := by
  have mu : ∀ (A B : Submodule E S.V) (g : S.GLV),
      g ∈ unipOn A B ↔ (∀ v, g v ∈ A ↔ v ∈ A) ∧ ∀ v ∈ A, g v - v ∈ B := fun _ _ _ => Iff.rfl
  have mi : g ∈ isomG M.L S.Hm ↔ ∀ x y, S.h (g x) (g y) = S.h x y := Iff.rfl
  have mp : ∀ (Y : Submodule E S.V) (v : S.V), v ∈ perp M.L S.Hm Y ↔ ∀ y ∈ Y, S.h v y = 0 :=
    fun _ _ => Iff.rfl
  simp only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf, mu, mi]
  constructor
  · rintro ⟨⟨hiso, hu⟩, hp⟩
    exact ⟨hiso, fun j hj v hv => (hu ⟨j, hj⟩).2 v hv, hp.2⟩
  · rintro ⟨hiso, hu, hp⟩
    have hfl := flag_iff (S.spanTo f) (spanTo_zero S f) (spanTo_mono S f) r g hu
    refine ⟨⟨hiso, fun j => ⟨hfl (j + 1) j.isLt, hu j j.isLt⟩⟩, ?_, hp⟩
    have hX := hfl r le_rfl
    intro v
    rw [mp, mp]
    constructor
    · intro hv y hy
      rw [← hiso v y]
      exact hv (g y) ((hX y).2 hy)
    · intro hv y hy
      have hy' : g.symm y ∈ S.spanTo f r := (hX _).1 (by simpa using hy)
      have := hv (g.symm y) hy'
      rw [← hiso v (g.symm y), LinearEquiv.apply_symm_apply] at this
      exact this

section Frame

variable (S : Frames M.L r k) (e : V ≃ₗ[E] S.V) (Fr : LocNG.FrameD H r) (f : Fin (r + 1) → S.V)

lemma Fj_r : Fr.Fj r = H.X Fr.f := by
  unfold LocNG.FrameD.Fj HermSp.X
  congr 1
  ext v
  simp [LocNG.FrameD.e]

lemma mem_Fj (hf : ∀ a, f a = e (Fr.f a)) (j : ℕ) (hj : j ≤ r) (x : V) :
    x ∈ Fr.Fj j ↔ e x ∈ S.spanTo f j := by
  have hs : S.spanTo f j = (Fr.Fj j).map (e : V →ₗ[E] S.V) := by
    unfold Frames.spanTo LocNG.FrameD.Fj
    rw [Submodule.map_span]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_ofPred_eq, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨Fr.e ⟨i, by omega⟩, ⟨⟨i, by omega⟩, hi, rfl⟩, ?_⟩
      rw [hf]
      rfl
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a.castSucc, by simpa using ha, by rw [hf]; rfl⟩
  rw [hs, Submodule.mem_map_equiv]
  simp

lemma mem_X (hf : ∀ a, f a = e (Fr.f a)) (x : V) : x ∈ H.X Fr.f ↔ e x ∈ S.spanTo f r := by
  rw [← Fj_r Fr]
  exact mem_Fj S e Fr f hf r le_rfl x

lemma mem_perp (he : ∀ x y, S.h (e x) (e y) = H.h x y) (hf : ∀ a, f a = e (Fr.f a)) (x : V) :
    x ∈ H.perp (H.X Fr.f) ↔ e x ∈ perp M.L S.Hm (S.spanTo f r) := by
  have hX := mem_X S e Fr f hf
  change (∀ y ∈ H.X Fr.f, H.h x y = 0) ↔ ∀ y ∈ S.spanTo f r, S.h (e x) y = 0
  constructor
  · intro h y hy
    have := h (e.symm y) ((hX _).2 (by simpa using hy))
    rw [← he, e.apply_symm_apply] at this
    exact this
  · intro h y hy
    rw [← he]
    exact h (e y) ((hX y).1 hy)

lemma mem_NSet (he : ∀ x y, S.h (e x) (e y) = H.h x y) (hf : ∀ a, f a = e (Fr.f a))
    (g : V ≃ₗ[E] V) (g' : S.GLV) (hg : ∀ v, g' (e v) = e (g v)) :
    g ∈ Fr.NSet ↔ g' ∈ S.Nof f := by
  rw [mem_Nof]
  simp only [LocNG.FrameD.NSet, Set.mem_ofPred_eq, LocNG.IsUnitary]
  have hgS : ∀ v w, S.h (g' (e v)) (g' (e w)) = H.h (g v) (g w) := fun v w => by rw [hg, hg, he]
  have hsub : ∀ v, g' (e v) - e v = e (g v - v) := fun v => by rw [hg, map_sub]
  constructor
  · rintro ⟨hu, hfl, hp⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x y
      obtain ⟨v, rfl⟩ := e.surjective x
      obtain ⟨w, rfl⟩ := e.surjective y
      rw [hgS, he]
      exact hu v w
    · intro j hj x hx
      obtain ⟨v, rfl⟩ := e.surjective x
      rw [hsub, ← mem_Fj S e Fr f hf j (by omega)]
      have := hfl (j + 1) (by omega) v ((mem_Fj S e Fr f hf (j + 1) (by omega) v).2 hx)
      simpa using this
    · intro x hx
      obtain ⟨v, rfl⟩ := e.surjective x
      rw [hsub, ← mem_X S e Fr f hf]
      exact hp v ((mem_perp S e Fr f he hf v).2 hx)
  · rintro ⟨hu, hfl, hp⟩
    refine ⟨fun v w => ?_, ?_, ?_⟩
    · rw [← hgS, ← he]
      exact hu _ _
    · intro j hj v hv
      cases j with
      | zero =>
        have h0 := (mem_Fj S e Fr f hf 0 (Nat.zero_le _) v).1 hv
        rw [spanTo_zero, Submodule.mem_bot] at h0
        have hv0 : v = 0 := e.injective (by rw [h0, map_zero])
        subst hv0
        simp
      | succ i =>
        rw [Nat.add_sub_cancel, mem_Fj S e Fr f hf i (by omega), ← hsub]
        exact hfl i (by omega) (e v) ((mem_Fj S e Fr f hf (i + 1) hj v).1 hv)
    · intro v hv
      rw [mem_X S e Fr f hf, ← hsub]
      exact hp (e v) ((mem_perp S e Fr f he hf v).1 hv)

end Frame

variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)

lemma grp_apply (g : V ≃ₗ[E] V) (v : V) : c.grp g (c.e v) = c.e (g v) := by
  simp [Coord.grp]

lemma mem_N (Fr : LocNG.FrameD H r) (f : Fin (r + 1) → S.V) (hf : ∀ a, f a = c.e (Fr.f a))
    (g : V ≃ₗ[E] V) : g ∈ Fr.N ↔ c.grp g ∈ S.Nof f := by
  have hset : Fr.NSet = {g | c.grp g ∈ S.Nof f} := by
    ext g
    exact mem_NSet S c.e Fr f c.h_eq hf g (c.grp g) (grp_apply c g)
  have hsub : Fr.N = (S.Nof f).comap c.grp.toMonoidHom := by
    rw [LocNG.FrameD.N, hset]
    exact Subgroup.closure_eq ((S.Nof f).comap c.grp.toMonoidHom)
  rw [hsub]
  rfl

lemma theta_eq (c : Coord P S) : LocNG.theta M = S.th := by
  unfold LocNG.theta Frames.th
  rcases hs : M.split with _ | g
  · simp [c.gg_none hs]
  · obtain ⟨h1, h2⟩ := c.gg_some g hs
    simp [h1, h2]

lemma psi_eq (Fr : LocNG.FrameD H r) (f : Fin (r + 1) → S.V) (es : Fin r → S.V)
    (hf : ∀ a, f a = c.e (Fr.f a)) (hes : ∀ a, es a = c.e (Fr.es a)) (g : V ≃ₗ[E] V) :
    Fr.psiN (LocNG.theta M) g = S.psiOf f es (c.grp g) := by
  unfold LocNG.FrameD.psiN LocNG.FrameD.psiOf LocNG.FrameD.coefSum Frames.psiOf Frames.coef
  simp only [hf, hes, grp_apply, c.h_eq, theta_eq c]

theorem transport : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), LocNG.theta M = S.th ∧ (∀ g, g ∈ P.A.N ↔ c.grp g ∈ S.N) ∧ (∀ g, g ∈ P.B.N ↔ c.grp g ∈ S.N') ∧ (∀ g, g ∈ P.St ↔ c.grp g ∈ S.St) ∧ (∀ g, P.A.psiN (LocNG.theta M) g = S.psi (c.grp g) ∧ P.B.psiN (LocNG.theta M) g = S.psi' (c.grp g)) ∧ (∀ x, x ∈ H.X P.A.f ↔ c.e x ∈ S.X) ∧ (∀ x, x ∈ H.X P.B.f ↔ c.e x ∈ S.X') ∧ (∀ x, x ∈ H.perp (H.X P.A.f) ↔ c.e x ∈ perp M.L S.Hm S.X) ∧ ∀ x, x ∈ H.perp (H.X P.B.f) ↔ c.e x ∈ perp M.L S.Hm S.X' := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ H r k P S c
  refine ⟨theta_eq c, fun g => mem_N c P.A S.f c.f_eq g, fun g => mem_N c P.B S.f' c.f'_eq g, ?_,
    fun g => ⟨psi_eq c P.A S.f S.es c.f_eq c.es_eq g, psi_eq c P.B S.f' S.es' c.f'_eq c.es'_eq g⟩,
    fun x => mem_X S c.e P.A S.f c.f_eq x, fun x => mem_X S c.e P.B S.f' c.f'_eq x,
    fun x => mem_perp S c.e P.A S.f c.h_eq c.f_eq x, fun x => mem_perp S c.e P.B S.f' c.h_eq c.f'_eq x⟩
  intro g
  rw [LocNG.FPair.St, Frames.St, Subgroup.mem_inf, Subgroup.mem_inf, mem_N c P.A S.f c.f_eq,
    mem_N c P.B S.f' c.f'_eq]
  rfl

end GlobalTheory.HL.CoordUnip
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexMulMeasure
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical NNReal

namespace GlobalTheory.BaseModule

@[to_additive addRelIndex_mul_measure
]
theorem relIndex_mul_measure' {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (H L : Subgroup G) (hHL : H ≤ L) [(H.subgroupOf L).FiniteIndex]
    (hH : MeasurableSet (H : Set G)) (μ : Measure G) [μ.IsMulLeftInvariant] :
    (H.relIndex L : ENNReal) * μ H = μ L := by
  classical
  obtain ⟨s, hs, -⟩ := (H.subgroupOf L).exists_isComplement_left 1
  have hfin : Finite s := hs.finite_left_iff.mpr inferInstance
  have hU : (L : Set G) = ⋃ a : s, ((a : L) : G) • (H : Set G) := by
    ext x
    simp only [Set.mem_iUnion, SetLike.mem_coe]
    constructor
    · intro hx
      have hy : (⟨x, hx⟩ : L) ∈ s * ((H.subgroupOf L : Subgroup L) : Set L) := by
        rw [hs.mul_eq]; exact Set.mem_univ _
      obtain ⟨a, ha, h, hh, hah⟩ := hy
      refine ⟨⟨a, ha⟩, (h : G), Subgroup.mem_subgroupOf.mp hh, ?_⟩
      have := congrArg Subtype.val hah
      simpa using this
    · rintro ⟨a, z, hz, rfl⟩
      exact L.mul_mem (a : L).2 (hHL hz)
  have hdisj : Pairwise (Function.onFun Disjoint fun a : s => ((a : L) : G) • (H : Set G)) := by
    intro a b hab
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, he⟩
    apply hab
    have key := hs.1 (a₁ := (a, ⟨⟨z₁, hHL hz₁⟩, Subgroup.mem_subgroupOf.mpr hz₁⟩))
      (a₂ := (b, ⟨⟨z₂, hHL hz₂⟩, Subgroup.mem_subgroupOf.mpr hz₂⟩)) (Subtype.ext (by simpa using he.symm))
    exact congrArg Prod.fst key
  calc (H.relIndex L : ENNReal) * μ H = ∑' a : s, μ (((a : L) : G) • (H : Set G)) := by
        simp [measure_smul, hs.encard_left, Subgroup.relIndex]
    _ = μ L := by
        rw [hU, measure_iUnion hdisj (fun _ => hH.const_smul _)]

theorem modK_algebraMap : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ ϖ : 𝒪[F], Irreducible ϖ → Nat.card 𝓀[F] = resQ ϖ ∧ ∀ x : F, x ≠ 0 → M.modK (algebraMap F E x) = (resQ ϖ : ℝ) ^ (-(2 * vE M.L ϖ (algebraMap F E x))) := by
  intro F _ _ _ E _ _ _ _ M hM ϖ hϖ
  have := hM.loc
  have := hM.char0
  have := hM.borel
  have := hM.haar.haar
  obtain ⟨hTR, hT2, hLC, hSC, hCS, -, -, hOc, hOo, -⟩ := GlobalTheory.SgLoc.Top.model_topology M hM
  have hq2 : 2 ≤ resQ ϖ := (GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ).2.2.2.2.2.2.1
  refine ⟨?_, ?_⟩
  · unfold GlobalTheory.HL.resQ
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
    rfl
  intro x hx
  have : IsTopologicalAddGroup E := inferInstance
  have : M.mu.Regular := inferInstance
  have hsmul : ∀ (a : F) (y : E), a ∈ 𝒪[F] → y ∈ M.L.O → a • y ∈ M.L.O := fun a y ha hy => by
    rw [Algebra.smul_def]
    exact M.L.O.mul_mem ((GlobalTheory.UnramOrder.algebraMap_mem_iff M.L a).mpr ha) hy
  have hO0 : M.mu (M.L.O : Set E) ≠ 0 := hOo.measure_ne_zero M.mu ⟨0, M.L.O.zero_mem⟩
  have hOT : M.mu (M.L.O : Set E) ≠ ⊤ := hOc.measure_lt_top.ne

  have hunit : ∀ u : (𝒪[F])ˣ, distribHaarChar E (Units.mk0 ((u : 𝒪[F]) : F) (by simp)) = 1 := by
    intro u
    apply distribHaarChar_eq_of_measure_smul_eq_mul hO0 hOT
    have hinv : (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) = ((u : 𝒪[F]) : F)⁻¹ := by
      have h1 : ((((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * (u : 𝒪[F]) : 𝒪[F]) : F) = ((1 : 𝒪[F]) : F) := by
        rw [u.inv_mul]
      rw [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
      exact eq_inv_of_mul_eq_one_left h1
    have hset : Units.mk0 ((u : 𝒪[F]) : F) (by simp) • (M.L.O : Set E) = M.L.O := by
      ext y
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      constructor
      · intro hy
        have h2 := hsmul ((u : 𝒪[F]) : F) _ (u : 𝒪[F]).2 hy
        rw [Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, smul_inv_smul₀ (by simp)] at h2
        exact h2
      · intro hy
        have h2 := hsmul (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) y (u⁻¹ : (𝒪[F])ˣ).1.2 hy
        rw [Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, ← hinv]
        exact h2
    rw [hset]
    simp

  have hϖ0 : (ϖ : F) ≠ 0 := by
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  have hwO : algebraMap F E (ϖ : F) ∈ M.L.O := (GlobalTheory.UnramOrder.algebraMap_mem_iff M.L _).mpr ϖ.2
  have hI : Ideal.span {y : M.L.O | (y : E) = algebraMap F E ((ϖ : F) ^ 1)} =
      Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)} := by
    congr 1
    ext y
    simp [Subtype.ext_iff]
  have hcard : Nat.card (M.L.O ⧸ Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}) = resQ ϖ ^ 2 := by
    have h := (GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ).2.2.2.2.2.1 1
    rw [hI, mul_one] at h
    exact h
  have hfinj : Function.Injective (M.L.O.subtype.toAddMonoidHom) := Subtype.val_injective
  have hrange : (⊤ : AddSubgroup M.L.O).map M.L.O.subtype.toAddMonoidHom = M.L.O.toAddSubgroup := by
    ext z
    simp
  have hrel : ((Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}).toAddSubgroup.map
      M.L.O.subtype.toAddMonoidHom).relIndex M.L.O.toAddSubgroup = resQ ϖ ^ 2 := by
    rw [← hrange, AddSubgroup.relIndex_map_map_of_injective _ _ hfinj, AddSubgroup.relIndex_top_right]
    exact hcard
  have hHK : (Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}).toAddSubgroup.map
      M.L.O.subtype.toAddMonoidHom ≤ M.L.O.toAddSubgroup := by
    rintro z ⟨y, -, rfl⟩
    exact y.2
  have hHset : (((Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}).toAddSubgroup.map
      M.L.O.subtype.toAddMonoidHom : AddSubgroup E) : Set E) = Units.mk0 (ϖ : F) hϖ0 • (M.L.O : Set E) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      refine ⟨(a : E), a.2, ?_⟩
      simp [Algebra.smul_def, mul_comm]
    · rintro ⟨b, hb, rfl⟩
      refine ⟨⟨b, hb⟩ * ⟨algebraMap F E (ϖ : F), hwO⟩,
        Ideal.mul_mem_left _ _ (Ideal.subset_span rfl), ?_⟩
      simp [Algebra.smul_def, mul_comm]
  have hHm : MeasurableSet (((Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}).toAddSubgroup.map
      M.L.O.subtype.toAddMonoidHom : AddSubgroup E) : Set E) := by
    rw [hHset]
    exact (hOo.smul _).measurableSet
  have : (((Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}).toAddSubgroup.map
      M.L.O.subtype.toAddMonoidHom).addSubgroupOf M.L.O.toAddSubgroup).FiniteIndex := by
    refine ⟨?_⟩
    change AddSubgroup.relIndex _ _ ≠ 0
    rw [hrel]
    exact pow_ne_zero _ (by omega)
  have key := addRelIndex_mul_measure _ _ hHK hHm M.mu
  rw [hrel, hHset] at key
  have key2 : ((resQ ϖ ^ 2 : ℕ) : ENNReal) * M.mu (Units.mk0 (ϖ : F) hϖ0 • (M.L.O : Set E)) =
      M.mu (M.L.O : Set E) := key
  have hΔp : distribHaarChar E (Units.mk0 (ϖ : F) hϖ0) = ((resQ ϖ : NNReal) ^ 2)⁻¹ := by
    apply distribHaarChar_eq_of_measure_smul_eq_mul hO0 hOT
    have h0 : ((resQ ϖ ^ 2 : ℕ) : ENNReal) ≠ 0 := by
      exact_mod_cast pow_ne_zero _ (by omega)
    have hT : ((resQ ϖ ^ 2 : ℕ) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hc : (((((resQ ϖ : NNReal) ^ 2)⁻¹ : NNReal)) : ENNReal) = ((resQ ϖ ^ 2 : ℕ) : ENNReal)⁻¹ := by
      rw [ENNReal.coe_inv (by exact_mod_cast pow_ne_zero _ (by omega))]
      push_cast
      rfl
    rw [hc]
    rw [← key2, ← mul_assoc, ENNReal.inv_mul_cancel h0 hT, one_mul]

  obtain ⟨u, hu⟩ := (GlobalTheory.UnramVal.vE_valuation M.L ϖ hϖ).2.2.2 x hx
  have hgx : Units.mk0 x hx = Units.mk0 (ϖ : F) hϖ0 ^ (vE M.L ϖ (algebraMap F E x)) *
      Units.mk0 ((u : 𝒪[F]) : F) (by simp) := by
    ext
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, Units.val_mk0, Units.val_mk0]
    exact hu
  have himg : (fun y => algebraMap F E x * y) '' (M.R : Set E) = Units.mk0 x hx • (M.R : Set E) := by
    rw [← Set.image_smul]
    congr 1
    funext y
    rw [Units.smul_def, Units.val_mk0, Algebra.smul_def]
  unfold Formalism.MainNotions.S.Loc.Model.modK
  rw [himg, ← distribHaarChar_mul M.mu, hM.haar.volR, mul_one, hgx, map_mul, map_zpow, hunit u, mul_one,
    hΔp, ENNReal.coe_toReal]
  push_cast
  rw [← zpow_natCast, ← zpow_neg, ← zpow_mul]
  congr 1
  push_cast
  ring

end GlobalTheory.BaseModule
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCharactersAgreeCommonStabiliser
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCharactersAgreeCommonStabiliser
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CharAgree
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto

theorem exists_invol {E : Type} [CommRing E] (bs : List (Eˣ × ℕ+)) :
    ∃ (σ : ℕ → ℕ) (t : ℕ → Eˣ),
      (∀ a, a < (bs.map (fun b => (b.2 : ℕ))).sum → σ a < (bs.map (fun b => (b.2 : ℕ))).sum ∧ σ (σ a) = a) ∧
      (∀ a b, a < (bs.map (fun b => (b.2 : ℕ))).sum → b < (bs.map (fun b => (b.2 : ℕ))).sum →
        ptEntryL bs a b = if b = σ a then (t a : E) else 0) ∧
      (∀ c, c + 1 < (bs.map (fun b => (b.2 : ℕ))).sum →
        (σ c = σ (c + 1) + 1 ∧ t (c + 1) = t c) ∨ σ c < σ (c + 1)) := by
  induction bs with
  | nil => exact ⟨id, 1, by simp, by simp, by simp⟩
  | cons p bs ih =>
    obtain ⟨u, s⟩ := p
    obtain ⟨σ, t, h1, h2, h3⟩ := ih
    simp only [List.map_cons, List.sum_cons]
    generalize (bs.map (fun b => (b.2 : ℕ))).sum = m at h1 h2 h3 ⊢
    refine ⟨fun a => if a < s then s - 1 - a else s + σ (a - s),
      fun a => if a < s then u else t (a - s), fun a ha => ?_, fun a b ha hb => ?_, fun c hc => ?_⟩
    · by_cases h : a < s
      · have h' : (s : ℕ) - 1 - a < s := by omega
        simp only [if_pos h, if_pos h']
        omega
      · obtain ⟨h4, h5⟩ := h1 (a - s) (by omega)
        have h' : ¬ (s : ℕ) + σ (a - s) < s := by omega
        simp only [if_neg h, if_neg h', Nat.add_sub_cancel_left, h5]
        omega
    · simp only [ptEntryL]
      by_cases h : a < s
      · simp only [if_pos h]
        by_cases h' : b < s
        · rw [if_pos ⟨h, h'⟩]
          exact if_congr (by omega) rfl rfl
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      · simp only [if_neg h]
        rw [if_neg (by omega)]
        by_cases h' : b < s
        · rw [if_neg (by omega), if_neg (by omega)]
        · rw [if_pos (by omega), h2 _ _ (by omega) (by omega)]
          exact if_congr (by omega) rfl rfl
    · by_cases h : c + 1 < s
      · have h' : c < s := by omega
        simp only [if_pos h, if_pos h']
        exact Or.inl ⟨by omega, trivial⟩
      · by_cases h' : c < s
        · simp only [if_neg h, if_pos h']
          exact Or.inr (by omega)
        · simp only [if_neg h, if_neg h']
          have e : c + 1 - s = c - s + 1 := by omega
          rw [e]
          rcases h3 (c - s) (by omega) with ⟨h4, h5⟩ | h4
          · exact Or.inl ⟨by omega, h5⟩
          · exact Or.inr (by omega)

theorem simple_sum {E : Type} [CommRing E] {r : ℕ} (w : Pt E (r + 1))
    (Z A C : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hZ : ∀ a b, Z a b = w.mat a b * (-1) ^ (r - (b : ℕ)))
    (hA : ∀ i j, i < j → A i j = 0) (hC : ∀ i j, j < i → C i j = 0)
    (h : ∀ a b, ∑ i, A a i * Z i b = ∑ i, Z a i * C i b) :
    ∑ j : Fin r, A j.succ j.castSucc = -∑ j : Fin r, C j.castSucc j.succ := by
  obtain ⟨σ₀, t, h1, h2, h3⟩ := exists_invol w.blocks
  rw [w.size] at h1 h2 h3
  let σ' : Fin (r + 1) → Fin (r + 1) := fun a => ⟨σ₀ a, (h1 a a.2).1⟩
  have hinv : Function.Involutive σ' := fun a => Fin.ext (h1 a a.2).2
  let σ : Fin (r + 1) ≃ Fin (r + 1) := hinv.toPerm
  have hσ : ∀ a, (σ a : ℕ) = σ₀ a := fun a => rfl
  have hσσ : ∀ a, σ (σ a) = a := hinv
  let z : Fin (r + 1) → Eˣ := fun a => t a * (-1) ^ (r - (σ a : ℕ))
  have hZ' : ∀ a b, Z a b = if b = σ a then (z a : E) else 0 := by
    intro a b
    rw [hZ, Pt.mat, h2 _ _ a.2 b.2]
    by_cases hb : b = σ a
    · rw [if_pos hb, if_pos (by rw [hb, hσ]), hb]; simp [z]
    · rw [if_neg hb, if_neg (fun e : (b : ℕ) = σ₀ a => hb (Fin.ext e)), zero_mul]
  have key : ∀ a c, A a c * z c = z a * C (σ a) (σ c) := by
    intro a c
    have := h a (σ c)
    simpa [hZ'] using this
  have term : ∀ a c : Fin (r + 1), (if (a : ℕ) = c + 1 then A a c else 0) =
      -(if (σ c : ℕ) = σ a + 1 then C (σ a) (σ c) else 0) := by
    intro a c
    by_cases hac : (a : ℕ) = c + 1
    · rw [if_pos hac]
      rcases h3 c (hac ▸ a.2) with ⟨h4, h5⟩ | h4
      · rw [← hac, ← hσ, ← hσ] at h4
        rw [← hac] at h5
        rw [if_pos h4]
        have hz : z a = -z c := by
          have := (σ c).2
          have e : r - (σ a : ℕ) = r - (σ c : ℕ) + 1 := by omega
          simp only [z, e, h5, pow_succ]
          simp
        have := key a c
        rw [hz, Units.val_neg, mul_comm, neg_mul, ← mul_neg] at this
        exact (Units.mul_right_inj _).1 this
      · rw [← hac, ← hσ, ← hσ] at h4
        rw [if_neg (by omega), neg_zero]
        have := key a c
        rw [hC _ _ h4, mul_zero] at this
        exact (Units.mul_left_eq_zero _).1 this
    · rw [if_neg hac]
      by_cases h4 : (σ c : ℕ) = σ a + 1
      · rw [if_pos h4]
        have h5 := h3 (σ a) (h4 ▸ (σ c).2)
        rw [← h4, ← hσ, ← hσ, hσσ, hσσ] at h5
        have h6 : a < c := by
          rcases h5 with ⟨h5, -⟩ | h5
          · exact absurd h5 hac
          · exact h5
        have := key a c
        rw [hA _ _ h6, zero_mul] at this
        rw [(Units.mul_right_eq_zero _).1 this.symm, neg_zero]
      · rw [if_neg h4, neg_zero]
  have hs : ∀ M : Fin (r + 1) → Fin (r + 1) → E,
      ∑ a : Fin (r + 1), ∑ c : Fin (r + 1), (if (a : ℕ) = c + 1 then M a c else 0) =
        ∑ j : Fin r, M j.succ j.castSucc := by
    intro M
    rw [Fin.sum_univ_succ]
    rw [Finset.sum_eq_zero (s := Finset.univ) (fun (c : Fin (r + 1)) _ =>
      if_neg (show ¬ ((0 : Fin (r + 1)) : ℕ) = c + 1 by simp)), zero_add]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j.castSucc]
    · simp
    · intro b _ hb
      exact if_neg fun e => hb (Fin.ext (Nat.add_right_cancel e).symm)
    · simp
  rw [← hs A, ← hs (fun a c => C c a)]
  simp only [term, Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_comm, ← σ.sum_comp]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← σ.sum_comp]
  simp only [hσσ]

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem hf_sum_l {ι : Type} [Fintype ι] (c : ι → E) (v : ι → S.V) (y : S.V) :
    hf L S.Hm (∑ i, c i • v i) y = ∑ i, c i * hf L S.Hm (v i) y := by
  classical
  refine Finset.induction_on Finset.univ (by simp [hf]) fun i s hi ih => ?_
  rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_l, hf_smul_l, ih]

theorem hf_sum_r {ι : Type} [Fintype ι] (c : ι → E) (v : ι → S.V) (y : S.V) :
    hf L S.Hm y (∑ i, c i • v i) = ∑ i, L.cj (c i) * hf L S.Hm y (v i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hf_cj L S.herm.1, hf_sum_l, map_sum]
  simp only [map_mul, hf_cj L S.herm.1]

theorem coef_eq (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
    (dual : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0) (n : S.GLV)
    (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hs : ∀ j, n (g j) = ∑ i, s i j • g i) (j : Fin r) :
    S.coef g gs n j = s j.castSucc j.succ := by
  simp [Frames.coef, Frames.h, hs, hf_sum_l, dual]

end

theorem psi_eq_psi' : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ h ∈ S.St, S.psi h = S.psi' h := by
  intro F _ _ _ _ _ E _ _ _ L r k S h hh
  obtain ⟨s, ⟨hs0, -⟩, hs⟩ := exists_matrix S S.f S.T S.gram h hh.1
  obtain ⟨s', ⟨hs0', hs1'⟩, hs'⟩ := exists_matrix S S.f' S.T' S.gram' h hh.2
  obtain ⟨C, ⟨hC0, hC1⟩, hC⟩ := exists_matrix S S.f' S.T' S.gram' h⁻¹ (inv_mem hh.2)
  have hiso : ∀ x y, hf L S.Hm (h x) (h y) = hf L S.Hm x y := hh.1.1.1
  have hcan : ∀ x, h (h⁻¹ x) = x := fun x => h.apply_symm_apply x
  have hneg : ∀ j : Fin r, s' j.castSucc j.succ = -C j.castSucc j.succ := by
    intro j
    have e : hf L S.Hm (h (h⁻¹ (S.f' j.succ))) (S.es' j) = 0 := by
      rw [hcan, S.dual', if_neg (Fin.castSucc_lt_succ (i := j)).ne']
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hC, map_sum] at e
    simp only [map_smul, hf_sum_l] at e
    simp only [hs', hf_sum_l, S.dual', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at e
    rw [Finset.sum_eq_add j.castSucc j.succ (Fin.castSucc_lt_succ (i := j)).ne, hs1', hC1] at e
    · linear_combination e
    · rintro i - ⟨h1, h2⟩
      by_cases hi : i < j.castSucc
      · rw [hs0' _ _ hi, mul_zero]
      · rw [hC0, zero_mul]
        have h1' : (i : ℕ) ≠ j := fun e => h1 (Fin.ext e)
        have h2' : (i : ℕ) ≠ j + 1 := fun e => h2 (Fin.ext e)
        have h3' : ¬ (i : ℕ) < j := hi
        change (j : ℕ) + 1 < i
        omega
    · simp
    · simp
  have main := simple_sum S.w S.Zh (cT L s) C S.relevant
    (fun i j hij => by rw [cT, hs0 _ _ hij, map_zero]) hC0 (fun a b => by
      have e := hiso (h⁻¹ (S.f' b)) (S.f a)
      rw [hcan, hs, hC, hf_sum_l, hf_sum_r] at e
      simpa [cT, Frames.Zh, Frames.h, mul_comm] using e)
  have e : ∑ j, S.coef S.f' S.es' h j = L.cj (∑ j, S.coef S.f S.es h j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [coef_eq S _ _ S.dual h s hs, coef_eq S _ _ S.dual' h s' hs', hneg, map_sum,
      Finset.sum_neg_distrib]
    exact main.symm
  simp only [Frames.psi, Frames.psi', Frames.psiOf]
  rw [e, ← L.local_additive_char_conj, map_mul, AlgEquiv.commutes]

end GlobalTheory.HL.CharAgree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCharactersAgreeCommonStabiliserStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frames_characters_agree_commonStabiliser : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ h ∈ S.St, S.psi h = S.psi' h := by
  first | exact @GlobalTheory.HL.CharAgree.psi_eq_psi' | exact GlobalTheory.HL.CharAgree.psi_eq_psi' | (intros; apply GlobalTheory.HL.CharAgree.psi_eq_psi' <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexComapPairOfDenseImage
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexComapPairOfDenseImage
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem index_comap_of_dense_image {A B : Type} [Group A] [Group B] (f : A →* B) (H : Subgroup B)
    (hf : ∀ b, ∃ a, (f a)⁻¹ * b ∈ H) : (H.comap f).index = H.index := by
  first
  | exact @_root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit
  | exact _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit
  | (apply _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> assumption)
  | (intros; apply _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit ..)

theorem relIndex_comap_of_dense_image {Γ G : Type} [Group Γ] [Group G] (φ : Γ →* G)
    (K U : Subgroup G) (h : ∀ g ∈ U, ∃ γ, (φ γ)⁻¹ * g ∈ K ⊓ U) :
    (K.comap φ).relIndex (U.comap φ) = K.relIndex U := by
  let f : U.comap φ →* U := φ.subgroupComap U
  have hc : (K.comap φ).subgroupOf (U.comap φ) = (K.subgroupOf U).comap f := by
    ext x
    exact Iff.rfl
  have key := index_comap_of_dense_image f (K.subgroupOf U) (by
    rintro ⟨b, hb⟩
    obtain ⟨γ, hγK, hγU⟩ := h b hb
    have hγ : φ γ ∈ U := by
      have := U.mul_mem hb (U.inv_mem hγU)
      simpa using this
    refine ⟨⟨γ, hγ⟩, ?_⟩
    exact hγK)
  simp only [Subgroup.relIndex]
  rw [hc, key]

theorem relIndex_pair_comap_of_dense_image : ∀ {Γ G : Type} [Group Γ] [Group G] (φ : Γ →* G) (K U : Subgroup G), (∀ g, g ∈ K ∨ g ∈ U → ∃ γ, (φ γ)⁻¹ * g ∈ K ⊓ U) → (K.comap φ).relIndex (U.comap φ) = K.relIndex U ∧ (U.comap φ).relIndex (K.comap φ) = U.relIndex K := by
  intro Γ G _ _ φ K U h
  refine ⟨relIndex_comap_of_dense_image φ K U fun g hg => h g (Or.inr hg), ?_⟩
  refine relIndex_comap_of_dense_image φ U K fun g hg => ?_
  obtain ⟨γ, hγ⟩ := h g (Or.inl hg)
  exact ⟨γ, by rwa [inf_comm]⟩

end GlobalTheory.HL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexComapPairOfDenseImageStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_comap_pair_of_dense_image : ∀ {Γ G : Type} [Group Γ] [Group G] (φ : Γ →* G) (K U : Subgroup G), (∀ g, g ∈ K ∨ g ∈ U → ∃ γ, (φ γ)⁻¹ * g ∈ K ⊓ U) → (K.comap φ).relIndex (U.comap φ) = K.relIndex U ∧ (U.comap φ).relIndex (K.comap φ) = U.relIndex K := by
  first | exact @GlobalTheory.HL.relIndex_pair_comap_of_dense_image | exact GlobalTheory.HL.relIndex_pair_comap_of_dense_image | (intros; apply GlobalTheory.HL.relIndex_pair_comap_of_dense_image <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelVolMul
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ContAut

theorem relVol_mul {W : Type} [AddCommGroup W] {X Y B : AddSubgroup W}
    (hYX : Y.relIndex X ≠ 0) (hBY : B.relIndex Y ≠ 0) :
    relVol X B = relVol X Y * relVol Y B := by
  have hCY : (B ⊓ Y).relIndex Y ≠ 0 := by rwa [AddSubgroup.inf_relIndex_right]
  have hCX : (B ⊓ Y).relIndex X ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hCY hYX
  have e1 := ContModel.relVol_of_le (W0 := X) (inf_le_left : B ⊓ Y ≤ B) hCX
  have e2 := ContModel.relVol_of_le (W0 := X) (inf_le_right : B ⊓ Y ≤ Y) hCX
  have e3 := ContModel.relVol_of_le (W0 := Y) (inf_le_left : B ⊓ Y ≤ B) hCY
  have e4 : relVol Y (B ⊓ Y) = 1 / ((B ⊓ Y).relIndex Y : ℝ) := by
    unfold relVol
    rw [AddSubgroup.relIndex_eq_one.2 (inf_le_right : B ⊓ Y ≤ Y)]
    simp
  have c : ((B ⊓ Y).relIndex Y : ℝ) ≠ 0 := by exact_mod_cast hCY
  rw [e1, e2, e3, e4]
  field_simp

theorem image_mk {W : Type} [AddCommGroup W] (A : AddSubgroup W) (φ : W ≃+ W) (S : Set W) :
    ∃ f : W ⧸ A → W ⧸ A.map φ.toAddMonoidHom, Function.Injective f ∧
      (QuotientAddGroup.mk : W → W ⧸ A.map φ.toAddMonoidHom) '' (φ '' S)
        = f '' ((QuotientAddGroup.mk : W → W ⧸ A) '' S) := by
  refine ⟨QuotientAddGroup.map A (A.map φ.toAddMonoidHom) φ.toAddMonoidHom
    (AddSubgroup.le_comap_map _ _), ?_, ?_⟩
  · intro u v
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective u
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective v
    intro h
    rw [QuotientAddGroup.map_mk, QuotientAddGroup.map_mk, QuotientAddGroup.eq] at h
    obtain ⟨a, ha, hh⟩ := h
    rw [QuotientAddGroup.eq]
    have : a = -x + y := φ.injective (by simpa using hh)
    rwa [← this]
  · rw [Set.image_image, Set.image_image]
    rfl

theorem cont_image : ∀ {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) (φ : W ≃+ W), (W0.map φ.toAddMonoidHom).relIndex W0 ≠ 0 → W0.relIndex (W0.map φ.toAddMonoidHom) ≠ 0 → ∀ S, IsCO W0 S → IsCO W0 (φ '' S) ∧ cont W0 (φ '' S) = relVol W0 (W0.map φ.toAddMonoidHom) * cont W0 S := by
  intro W _ W0 φ h1 h2 S ⟨A, hA⟩
  have hi : Function.Injective φ.toAddMonoidHom := φ.injective
  have m1 := AddSubgroup.relIndex_map_map_of_injective A W0 hi
  have m2 := AddSubgroup.relIndex_map_map_of_injective W0 A hi
  obtain ⟨f, hf, him⟩ := image_mk A φ S
  have a1 : (A.map φ.toAddMonoidHom).relIndex (W0.map φ.toAddMonoidHom) ≠ 0 := m1 ▸ hA.1
  have a2 : (W0.map φ.toAddMonoidHom).relIndex (A.map φ.toAddMonoidHom) ≠ 0 := m2 ▸ hA.2.1
  have hG : GoodSub W0 (A.map φ.toAddMonoidHom) (φ '' S) := by
    refine ⟨AddSubgroup.relIndex_ne_zero_trans a1 h1, AddSubgroup.relIndex_ne_zero_trans h2 a2,
      ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨a, ha, rfl⟩
      exact ⟨x + a, hA.2.2.1 x hx a ha, by simp⟩
    · rw [him]; exact hA.2.2.2.image f
  refine ⟨⟨_, hG⟩, ?_⟩
  rw [ContModel.cont_eq hG, ContModel.cont_eq hA, him, Set.ncard_image_of_injective _ hf,
    relVol_mul h1 a1]
  have : relVol (W0.map φ.toAddMonoidHom) (A.map φ.toAddMonoidHom) = relVol W0 A := by
    unfold relVol; rw [m1, m2]
  rw [this]; ring

end GlobalTheory.HL.ContAut
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommensurableCosetUnionContentBiUnion
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommensurableCosetUnionContentBiUnion
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem exists_common_goodSub {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) {ι : Type}
    (s : Finset ι) (S : ι → Set W) (h : ∀ i ∈ s, IsCO W0 (S i)) :
    ∃ A, GoodSub W0 A ∅ ∧ ∀ i ∈ s, GoodSub W0 A (S i) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨W0, ⟨by simp, by simp, by simp, by simp⟩, by simp⟩
  | insert j s hj ih =>
    obtain ⟨A, hA0, hA⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨B, hB⟩ := h j (Finset.mem_insert_self _ _)
    have h1 : (A ⊓ B).relIndex A ≠ 0 := by
      rw [AddSubgroup.inf_relIndex_left]
      exact AddSubgroup.relIndex_ne_zero_trans hB.1 hA0.2.1
    have h2 : (A ⊓ B).relIndex B ≠ 0 := by
      rw [AddSubgroup.inf_relIndex_right]
      exact AddSubgroup.relIndex_ne_zero_trans hA0.1 hB.2.1
    refine ⟨A ⊓ B, (GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg W0 ∅).2.1 A _ hA0 inf_le_left h1, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact (GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg W0 _).2.1 B _ hB inf_le_right h2
    · exact (GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg W0 _).2.1 A _ (hA i hi) inf_le_left h1

theorem cont_biUnion : ∀ {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) {ι : Type} (s : Finset ι) (S : ι → Set W), (∀ i ∈ s, IsCO W0 (S i)) → IsCO W0 (⋃ i ∈ s, S i) ∧ ((∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (S i) (S j)) → cont W0 (⋃ i ∈ s, S i) = ∑ i ∈ s, cont W0 (S i)) := by
  intro W _ W0 ι s S h
  obtain ⟨A, hA0, hA⟩ := exists_common_goodSub W0 s S h
  have himg : (QuotientAddGroup.mk : W → W ⧸ A) '' (⋃ i ∈ s, S i) =
      ⋃ i ∈ s, (QuotientAddGroup.mk : W → W ⧸ A) '' S i := by
    simp only [Set.image_iUnion]
  have hU : GoodSub W0 A (⋃ i ∈ s, S i) := by
    refine ⟨hA0.1, hA0.2.1, ?_, ?_⟩
    · intro x hx a ha
      simp only [Set.mem_iUnion] at hx ⊢
      obtain ⟨i, hi, hx⟩ := hx
      exact ⟨i, hi, (hA i hi).2.2.1 x hx a ha⟩
    · rw [himg]
      exact Set.Finite.biUnion s.finite_toSet fun i hi => (hA i hi).2.2.2
  refine ⟨⟨A, hU⟩, fun hd => ?_⟩
  rw [(GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg W0 _).1 A hU,
    Finset.sum_congr rfl fun i hi => (GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg W0 (S i)).1 A (hA i hi), ← Finset.sum_mul, himg]
  congr 1
  have key := Set.Finite.ncard_biUnion (t := (s : Set ι))
    (s := fun i => (QuotientAddGroup.mk : W → W ⧸ A) '' S i) s.finite_toSet
    (fun i hi => (hA i hi).2.2.2) (by
      intro i hi j hj hij
      refine Set.disjoint_left.2 ?_
      rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
      have hm : -y + x ∈ A := QuotientAddGroup.eq.1 hxy
      have := (hA j hj).2.2.1 y hy _ hm
      rw [add_neg_cancel_left] at this
      exact Set.disjoint_left.1 (hd i hi j hj hij) hx this)
  rw [finsum_mem_coe_finset] at key
  exact_mod_cast key

end GlobalTheory.HL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommensurableCosetUnionContentBiUnionStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commensurableCosetUnionContent_biUnion : ∀ {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) {ι : Type} (s : Finset ι) (S : ι → Set W), (∀ i ∈ s, IsCO W0 (S i)) → IsCO W0 (⋃ i ∈ s, S i) ∧ ((∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (S i) (S j)) → cont W0 (⋃ i ∈ s, S i) = ∑ i ∈ s, cont W0 (S i)) := by
  first | exact @GlobalTheory.HL.cont_biUnion | exact GlobalTheory.HL.cont_biUnion | (intros; apply GlobalTheory.HL.cont_biUnion <;> assumption)
end
end
