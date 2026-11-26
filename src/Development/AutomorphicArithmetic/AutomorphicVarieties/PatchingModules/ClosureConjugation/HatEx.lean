module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.PhiFg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UnivDetMf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.LiftEq
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem lift_eq {n : ℕ} {B C G : Type} [CommRing B] [CommRing C] [Algebra B C] [Group G]
    (ρ : G →* Matrix (Fin n) (Fin n) C) (z : MonoidAlgebra B G) :
    MonoidAlgebra.lift B _ G ρ z = GDet.repAlg ρ C (MonoidAlgebra.mapRingHom G (algebraMap B C) z) := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g r => ext i j; simp [GDet.repAlg, Algebra.smul_def]

private theorem lift_CH {n : ℕ} {B C G : Type} [CommRing B] [CommRing C] [Algebra B C] [Group G]
    (D : GDet n B G) (ρ : G →* Matrix (Fin n) (Fin n) C) (h : D.map (algebraMap B C) = GDet.ofRep ρ)
    (z : MonoidAlgebra B G) (hz : z ∈ D.CH) : MonoidAlgebra.lift B _ G ρ z = 0 := by
  rw [lift_eq]
  refine (d_ofRep (Fintype.card_fin n) (GDet.repAlg ρ C) _).2.2.2 ?_
  rw [← d_toDet_ofRep.1 ρ, d_toDet_CH, ← h, g_chmap]
  exact TwoSidedIdeal.subset_span ⟨z, hz, rfl⟩

theorem UpperTheory.V.CA.f_rep :
    ∀ {n : ℕ} {B C G : Type} [CommRing B] [IsLocalRing B] [CommRing C] [Algebra B C] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (J : Ideal C) [IsHausdorff J C] (D : GDet n B G) (ρ : G →* Matrix (Fin n) (Fin n) C) (Z : Set (MonoidAlgebra B G)), maximalIdeal B ≤ J.comap (algebraMap B C) → (∀ a b, AdicCont J fun g => ρ g a b) → D.map (algebraMap B C) = GDet.ofRep ρ → (∀ z ∈ Z, MonoidAlgebra.lift B _ G ρ z = 0) → ∃ r : D.CHQuot Z →ₐ[B] Matrix (Fin n) (Fin n) C, ∀ g, r (D.toQuot Z (MonoidAlgebra.single g 1)) = ρ g := by
  intro n B C G _ _ _ _ _ _ _ _ _ J _ D ρ Z hm hc hD hZ
  have key : ∀ z ∈ D.chBar Z, MonoidAlgebra.lift B _ G ρ z = 0 := by
    intro z hz
    ext a b
    refine IsHausdorff.haus (I := J) inferInstance _ fun N => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    have hU : IsOpen (⋂ a, ⋂ b, {g : G | Ideal.Quotient.mk (J ^ N) (ρ g a b) = Ideal.Quotient.mk (J ^ N) (ρ 1 a b)}) :=
      isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => (hc a b N).isOpen_fiber _
    obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU (by simp)
    let φ : MonoidAlgebra B G →+* Matrix (Fin n) (Fin n) (C ⧸ J ^ N) :=
      (Ideal.Quotient.mk (J ^ N)).mapMatrix.comp (MonoidAlgebra.lift B _ G ρ).toRingHom
    have hφ : ∀ y, φ y = (MonoidAlgebra.lift B _ G ρ y).map (Ideal.Quotient.mk (J ^ N)) := fun _ => rfl
    have hle : D.chBar Z ≤ TwoSidedIdeal.ker φ := by
      refine (iInf₂_le N H).trans ?_
      rw [TwoSidedIdeal.span_le]
      intro y hy
      change _ ∈ TwoSidedIdeal.ker φ
      rw [TwoSidedIdeal.mem_ker]
      rcases hy with ((hy | hy) | ⟨x, hx, rfl⟩) | ⟨h, hh, rfl⟩
      · rw [hφ, lift_CH D ρ hD y hy]; simp
      · rw [hφ, hZ y hy]; simp
      · have hx' : algebraMap B C x ∈ J ^ N :=
          Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hm) N
            (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hx)
        ext i j
        rw [hφ, MonoidAlgebra.lift_single, Matrix.map_apply, Matrix.smul_apply, Algebra.smul_def, Matrix.zero_apply,
          Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mul_mem_right _ _ hx'
      · rw [map_sub, map_one, sub_eq_zero, ← φ.map_one]
        ext i j
        have := Set.mem_iInter.1 (Set.mem_iInter.1 (hH hh) i) j
        rw [hφ, hφ, map_one, MonoidAlgebra.lift_single, one_smul, ← ρ.map_one]
        exact this
    have := congrFun (congrFun ((TwoSidedIdeal.mem_ker φ).1 (hle hz)) a) b
    rw [hφ] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  refine ⟨RingCon.liftₐ _ (MonoidAlgebra.lift B _ G ρ) fun x y hxy => ?_, fun g => ?_⟩
  · have := key _ ((TwoSidedIdeal.rel_iff _ _ _).1 hxy)
    rwa [map_sub, sub_eq_zero] at this
  · change MonoidAlgebra.lift B _ G ρ _ = _
    simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TrinvBaseChange
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.trinv_baseChange :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) (B' : Type) [CommRing B'] [Algebra B B'], ∃ T' : TrInv B' (B' ⊗[B] E), (∀ y, T'.st (1 ⊗ₜ y) = 1 ⊗ₜ T.st y) ∧ ∀ y, T'.tr (1 ⊗ₜ y) = algebraMap B B' (T.tr y) := by
  intro B E _ _ _ T B' _ _
  let s : B' ⊗[B] E →ₗ[B'] B' ⊗[B] E := T.st.baseChange B'
  let t : B' ⊗[B] E →ₗ[B'] B' :=
    (AlgebraTensorModule.rid B B' B').toLinearMap ∘ₗ T.tr.baseChange B'
  have hs : ∀ (a : B') (y : E), s (a ⊗ₜ y) = a ⊗ₜ T.st y := fun a y => by simp [s]
  have ht : ∀ (a : B') (y : E), t (a ⊗ₜ y) = T.tr y • a := fun a y => by simp [t]
  refine ⟨⟨s, ?_, ?_, t, ?_, ?_⟩, fun y => hs 1 y, fun y => ?_⟩
  · intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [add_mul, mul_add, map_add (f := _), ha, hb]
    | tmul a u =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add c d hc hd => simp only [add_mul, mul_add, map_add (f := _), hc, hd]
      | tmul b v =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, hs, T.st_mul, mul_comm a b]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul a u => simp only [hs, T.st_st]
  · intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [add_mul, mul_add, map_add (f := _), ha, hb]
    | tmul a u =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add c d hc hd => simp only [add_mul, mul_add, map_add (f := _), hc, hd]
      | tmul b v =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, ht, T.tr_comm u v, mul_comm a b]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul a u => simp only [hs, ht, T.tr_st]
  · show t (1 ⊗ₜ y) = _
    rw [ht, Algebra.algebraMap_eq_smul_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.PairMf
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.pair_mf :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] {r : Resid F O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B), PhiCond F.G₀ l → Finite (ResidueField B) ∧ (l : B) ∈ maximalIdeal B ∧ ∃ (h : ℕ) (χ : Fin n → F.G₀ →* (ResidueField B)ˣ), u.D.map (residue B) = GDet.ofChars χ ∧ MultFree χ h := by
  intro l _ F n O _ _ _ hc _ r B _ _ _ u hΦ
  haveI := hc.finite
  haveI := hc.char
  let e : ResidueField O ≃+* ResidueField B := RingEquiv.ofBijective _ (resMap_bijective O B)
  haveI hfin : Finite (ResidueField B) := Finite.of_equiv _ e.toEquiv
  haveI hch : CharP (ResidueField B) l := charP_of_injective_ringHom (f := e.toRingHom) e.injective l
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.1 (F.η.ker.isClosed_of_isOpen F.η_open).isCompact
  let χ : Fin n → F.G₀ →* (ResidueField B)ˣ := fun i => pushCh e.toRingHom (r.chib i)
  have hU : Function.Injective (Units.map (e.toRingHom : ResidueField O →* ResidueField B)) :=
    Units.map_injective e.injective
  have hop : ∀ i, IsOpen ((χ i).ker : Set F.G₀) := fun i => by
    have : (χ i).ker = (r.chib i).ker := MonoidHom.ker_comp_of_injective _ _ hU
    rw [this]
    exact r.chib_open i
  have hinj : Function.Injective χ := fun i j hij =>
    r.chib_inj (MonoidHom.ext fun g => hU (DFunLike.congr_fun hij g))
  obtain ⟨h, hh⟩ := exists_multFree_of_phiCond_of_injective_chars l χ hΦ hop hinj
  refine ⟨hfin, ?_, h, χ, ?_, hh⟩
  · rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ l
  · have h1 : residue B = e.toRingHom.comp (res O B : B →+* ResidueField O) :=
      RingHom.ext fun b => (e.apply_symm_apply (residue B b)).symm
    rw [h1, ← (d_gmap u.D).2.1, u.red, Resid.Dbar, (d_gmap r.Dbar).2.2.2]
    unfold GDet.ofChars
    congr 1
    refine MonoidHom.ext fun g => ?_
    change (Matrix.diagonal fun i => ((r.chib i g : (ResidueField O)ˣ) : ResidueField O)).map e.toRingHom = _
    rw [Matrix.diagonal_map (map_zero _)]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.StarBasic
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem conj_conj_of_isQuad {l : ℕ} [Fact l.Prime] (F : GFrame l) (g : F.G₀) : F.conj (F.conj g) = g := by
  have h : F.c⁻¹ = F.c := (eq_inv_of_mul_eq_one_left F.c_sq).symm
  apply Subtype.ext
  simp only [GFrame.conj, MonoidHom.coe_mk, OneHom.coe_mk, h]
  simp only [← mul_assoc, F.c_sq, one_mul]
  rw [mul_assoc, F.c_sq, mul_one]

private theorem eps_conj_eq_eps {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (g : F.G₀) : F.eps O R (F.conj g) = F.eps O R g := by
  simp only [GFrame.eps, pushCh, MonoidHom.comp_apply, Subgroup.coe_subtype, GFrame.conj, MonoidHom.coe_mk, OneHom.coe_mk, map_mul, map_inv]
  rw [mul_right_comm, mul_inv_cancel, one_mul]

private theorem star_single_eq_single_conj_inv_mul_eps_zpow' {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (g : F.G₀) (b : R) : F.star O R n (MonoidAlgebra.single g b) = MonoidAlgebra.single (F.conj g)⁻¹ (b * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
  simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]

theorem UpperTheory.V.Pa.star_basic :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (n : ℕ) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R], (∀ y, F.star O R n (F.star O R n y) = y) ∧ (∀ y z, F.star O R n (y * z) = F.star O R n z * F.star O R n y) ∧ (∀ y z, F.star O R n (y + z) = F.star O R n y + F.star O R n z) ∧ (∀ (b : R) y, F.star O R n (b • y) = b • F.star O R n y) ∧ F.star O R n 1 = 1 ∧ (∀ y z, F.star O R n (y - z) = F.star O R n y - F.star O R n z) ∧ ∀ g b, F.star O R n (MonoidAlgebra.single g b) = MonoidAlgebra.single (F.conj g)⁻¹ (b * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
  intro l _ F n O _ _ R _ _
  have hadd : ∀ y z, F.star O R n (y + z) = F.star O R n y + F.star O R n z := by
    intro y z
    simp [GFrame.star, map_add (f := _)]
  refine ⟨?_, ?_, hadd, ?_, ?_, ?_, star_single_eq_single_conj_inv_mul_eps_zpow' F O R n⟩
  · intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp [GFrame.star]
    | add y z hy hz => rw [hadd, hadd, hy, hz]
    | single g b =>
      rw [star_single_eq_single_conj_inv_mul_eps_zpow', star_single_eq_single_conj_inv_mul_eps_zpow', map_inv, inv_inv, conj_conj_of_isQuad, map_inv, eps_conj_eq_eps, _root_.inv_zpow', mul_assoc, ← Units.val_mul, ← _root_.zpow_add]
      simp
  · intro y z
    simp [GFrame.star, map_mul]
  · intro b y
    simp [GFrame.star, map_smul]
  · simp [GFrame.star, map_one]
  · intro y z
    simp [GFrame.star, map_sub]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GensKill
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.gens_kill :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ z ∈ P.gens, u.D.Kills z ∧ G.frame.star O B n z ∈ P.gens := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P z hz
  haveI := IsCoef.complete (l := l) (O := O)
  haveI := IsCoef.finite (l := l) (O := O)
  haveI := IsCoef.char (l := l) (O := O)
  have hn : 1 ≤ n := x.a_pos.trans x.a_le
  have hPhi : PhiCond G.frame.G₀ l := phi_fg G.frame P.fg
  obtain ⟨-, hks, -, hoEl, hIp⟩ := pair_kills r u hPhi hn
  obtain ⟨hfin, -, e, χ, hχ, hmf⟩ := pair_mf u hPhi
  haveI := hfin
  haveI := IsCO.complete (O := O) (R := B)
  haveI : CompactSpace G.frame.G₀ := by
    haveI := G.frame.cpt
    show CompactSpace G.frame.η.ker
    exact isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ G.frame.η_open).isCompact
  obtain ⟨hss, -, -, -, h1, hsub, -⟩ := star_basic G.frame n O B
  have htr : ∀ y, u.D.Kills y ↔ ∀ g, u.D.tr (MonoidAlgebra.single g 1 * y) = 0 :=
    g_kills_tr u.D χ u.cont hχ hmf hn
  unfold OoPt.gens pairGens qGens at hz ⊢
  simp only [Set.mem_union, Set.mem_setOf_eq] at hz ⊢
  rcases hz with ((⟨v, g, rfl | rfl⟩ | ⟨w, g, hg, rfl | rfl⟩) | (⟨j, rfl | rfl⟩ | ⟨j, i, rfl | rfl⟩))
  · exact ⟨hoEl v g, Or.inl (Or.inl ⟨v, g, Or.inr rfl⟩)⟩
  · refine ⟨hks _ (hoEl v g), Or.inl (Or.inl ⟨v, g, Or.inl ?_⟩)⟩
    rw [hss]
  · exact ⟨hIp w g hg, Or.inl (Or.inr ⟨w, g, hg, Or.inr (by rw [hsub, h1])⟩)⟩
  · have hk := hks _ (hIp w g hg)
    rw [hsub, h1] at hk
    refine ⟨hk, Or.inl (Or.inr ⟨w, g, hg, Or.inl ?_⟩)⟩
    rw [hsub, hss, h1]
  · have hk := (htr _).2 (P.q1 j)
    exact ⟨hk, Or.inr (Or.inl ⟨j, Or.inr rfl⟩)⟩
  · have hk := hks _ ((htr _).2 (P.q1 j))
    refine ⟨hk, Or.inr (Or.inl ⟨j, Or.inl ?_⟩)⟩
    rw [hss]
  · have hk := (htr _).2 (P.q2 j i)
    exact ⟨hk, Or.inr (Or.inr ⟨j, i, Or.inr rfl⟩)⟩
  · have hk := hks _ ((htr _).2 (P.q2 j i))
    refine ⟨hk, Or.inr (Or.inr ⟨j, i, Or.inl ?_⟩)⟩
    rw [hss]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.RepQuot
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.RepGens
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.RepStar
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.rep_star :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ y, P.rep (G.frame.star O B n y) = (P.rep y)ᵀ := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P y
  have sb := star_basic G.frame n O B
  have hrep : ∀ (g : G.G₀) (b : B), P.rep (MonoidAlgebra.single g b) = P.f b • mat x.ρ (h.p₀ g) := by
    intro g b
    simp only [OoPt.rep, GDet.repAlg, RingHom.comp_apply, MonoidAlgebra.mapRingHom_single,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidHom.comp_apply,
      Algebra.algebraMap_self, RingHom.mapMatrix_id]
    rfl
  induction y using MonoidAlgebra.induction_linear with
  | zero =>
    have h0 : G.frame.star O B n 0 = 0 := by simpa using sb.2.2.2.2.2.1 0 0
    rw [h0, map_zero, Matrix.transpose_zero]
  | add p q hp hq => rw [sb.2.2.1, map_add (f := _), map_add (f := _), hp, hq, Matrix.transpose_add]
  | single g b =>
    rw [sb.2.2.2.2.2.2 g b]
    obtain ⟨he, hc⟩ := eps_eq P g
    have hform := x.form (h.p₀ g)
    rw [Units.val_one, mul_one] at hform
    have hci : mat x.ρ (G0.frame.conj (h.p₀ g)) * mat x.ρ (G0.frame.conj (h.p₀ g))⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have hT : (mat x.ρ (h.p₀ g))ᵀ =
        ((G0.frame.eps ℤ_[l] (PowerSeries x.K) (h.p₀ g) ^ (1 - (n : ℤ)) : (PowerSeries x.K)ˣ) : PowerSeries x.K) •
          mat x.ρ (G0.frame.conj (h.p₀ g))⁻¹ := by
      calc (mat x.ρ (h.p₀ g))ᵀ
          = (mat x.ρ (h.p₀ g))ᵀ * (mat x.ρ (G0.frame.conj (h.p₀ g)) * mat x.ρ (G0.frame.conj (h.p₀ g))⁻¹) := by
            rw [hci, mul_one]
        _ = _ := by rw [← mul_assoc, hform, Matrix.smul_mul, one_mul]
    have hu : Units.map (P.f.toRingHom : B →* x.A) (G.frame.eps O B g) = G0.frame.eps ℤ_[l] x.A (h.p₀ g) :=
      Units.ext he
    have hfu : P.f ((G.frame.eps O B g ^ (1 - (n : ℤ)) : Bˣ) : B) =
        ((G0.frame.eps ℤ_[l] x.A (h.p₀ g) ^ (1 - (n : ℤ)) : (x.A)ˣ) : x.A) := by
      calc P.f ((G.frame.eps O B g ^ (1 - (n : ℤ)) : Bˣ) : B)
          = ((Units.map (P.f.toRingHom : B →* x.A) (G.frame.eps O B g ^ (1 - (n : ℤ))) : (x.A)ˣ) : x.A) := rfl
        _ = _ := by rw [map_zpow, hu]
    rw [hrep, hrep, Matrix.transpose_smul, map_mul, hfu, hT, map_inv, hc, mul_smul]
end

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem conj_prod_zero {R : Type} [CommRing R] {n : ℕ} (w : GL (Fin n) R) (M : Fin n → GL (Fin n) R)
    (c : Fin n → R) (h1 : ∀ k i j, j < i → (w⁻¹ * M k * w : GL (Fin n) R) i j = 0)
    (h2 : ∀ k, (w⁻¹ * M k * w : GL (Fin n) R) k k = c k) :
    (List.ofFn fun k => (M k : Matrix (Fin n) (Fin n) R) - c k • (1 : Matrix (Fin n) (Fin n) R)).prod = 0 := by
  classical
  let f : Matrix (Fin n) (Fin n) R →* Matrix (Fin n) (Fin n) R :=
    { toFun := fun A => (↑w⁻¹ : Matrix (Fin n) (Fin n) R) * A * ↑w
      map_one' := by simp
      map_mul' := fun A B => by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (↑w : Matrix (Fin n) (Fin n) R) (↑w⁻¹ : Matrix (Fin n) (Fin n) R)]
        simp }
  have hf : ∀ k, f ((M k : Matrix (Fin n) (Fin n) R) - c k • (1 : Matrix (Fin n) (Fin n) R)) =
      ((w⁻¹ * M k * w : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) - c k • (1 : Matrix (Fin n) (Fin n) R) := by
    intro k
    simp [f, Matrix.mul_sub, Matrix.sub_mul, Units.val_mul]
  have key : f (List.ofFn fun k => (M k : Matrix (Fin n) (Fin n) R) - c k • (1 : Matrix (Fin n) (Fin n) R)).prod = 0 := by
    rw [map_list_prod, List.map_ofFn]
    apply tri_prod_zero
    · intro k i j hij
      simp only [Function.comp_apply, hf, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne (ne_of_lt hij).symm, smul_zero, sub_zero]
      exact h1 k i j hij
    · intro k
      simp only [Function.comp_apply, hf, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      rw [h2 k, sub_self]
  have back : ∀ A : Matrix (Fin n) (Fin n) R,
      A = (↑w : Matrix (Fin n) (Fin n) R) * f A * (↑w⁻¹ : Matrix (Fin n) (Fin n) R) := by
    intro A
    simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, ← Matrix.mul_assoc]
    simp [Matrix.mul_assoc]
  rw [back (List.ofFn _).prod, key]
  simp

private theorem ch_prod_zero {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (c : Fin n → R)
    (h : M.charpoly = ∏ i, (X - C (c i))) :
    (List.ofFn fun k => M - c k • (1 : Matrix (Fin n) (Fin n) R)).prod = 0 := by
  classical
  have e : (List.ofFn fun k => M - c k • (1 : Matrix (Fin n) (Fin n) R)).prod =
      aeval M (∏ i, (X - C (c i))) := by
    rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
    congr 1
    congr 1
    funext k
    simp [Algebra.algebraMap_eq_smul_one]
  rw [e, ← h, aeval_self_charpoly]

theorem UpperTheory.V.Pa.rep_gens :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ z ∈ P.gens, P.rep z = 0 := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P z hz
  have hs : ∀ (g : G.G₀) (b : B), P.rep (MonoidAlgebra.single g b) =
      P.f b • ((x.ρ (h.p₀ g) : GL (Fin n) x.A) : Matrix (Fin n) (Fin n) x.A) := by
    intro g b
    simp [OoPt.rep, GDet.repAlg, mat]
  have hfac : ∀ (g : G.G₀) (b : B), P.rep (MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 b) =
      ((x.ρ (h.p₀ g) : GL (Fin n) x.A) : Matrix (Fin n) (Fin n) x.A) - P.f b • (1 : Matrix (Fin n) (Fin n) x.A) := by
    intro g b
    rw [map_sub, hs, hs]
    simp
  have hst : ∀ y, P.rep y = 0 → P.rep (G.frame.star O B n y) = 0 := by
    intro y hy
    rw [rep_star, hy, Matrix.transpose_zero]
  have hL : ∀ (m : ℕ) (F : Fin m → MonoidAlgebra B G.G₀),
      P.rep (List.ofFn F).prod = (List.ofFn fun i => P.rep (F i)).prod := by
    intro m F
    rw [map_list_prod, List.map_ofFn]
    rfl
  have hφ : ∀ v (g : L.Gv v), h.p₀ (G.frame.φ v g) = G0.frame.φ v g := by
    intro v g
    exact Subtype.ext (h.φ v g)
  have kOrd : ∀ v g, P.rep (G.frame.oEl v (u.ψ v) g) = 0 := by
    intro v g
    rw [GFrame.oEl, hL]
    simp only [hfac]
    apply conj_prod_zero (x.w v) (fun i => x.ρ (h.p₀ (G.frame.φ v (g i)))) (fun i => P.f ↑(u.ψ v i (g i)))
    · intro k i j hij
      rw [hφ]
      exact (x.tri v (g k)).1 i j hij
    · intro k
      rw [hφ, (x.tri v (g k)).2 k, ← P.maps.2 v k]
      rfl
  have kI : ∀ w, ∀ g ∈ r.Ip w, P.rep (MonoidAlgebra.single g 1) = 1 := by
    intro w g hg
    rw [P.Ip w] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    have e : h.p₀ (G.φu w a) = G0.φu w a := Subtype.ext (h.φu w a)
    have hin : G0.φu w a ∈ G0.frame.Iu w := ⟨a, ha, rfl⟩
    rw [hs, e, x.ine w _ hin]
    simp
  have kq1 : ∀ j, P.rep (q1El (P.ph j) (P.U j)) = 0 := by
    intro j
    rw [q1El, hL]
    simp only [hfac]
    exact ch_prod_zero _ _ (P.eig j)
  have kq2 : ∀ j i, P.rep (q2El (P.ph j) (P.ta j) (P.U j) i (P.y j i)) = 0 := by
    intro j i
    rw [q2El, map_mul, map_sub, map_sub, hs, hs, P.p_ta j, P.f_y j i]
    simp
  rcases hz with hz | hz
  · rcases hz with ⟨v, g, rfl | rfl⟩ | ⟨w, g, hg, rfl | rfl⟩
    · exact kOrd v g
    · exact hst _ (kOrd v g)
    · rw [map_sub, kI w g hg, map_one, sub_self]
    · rw [map_sub, rep_star, kI w g hg, map_one, Matrix.transpose_one, sub_self]
  · rcases hz with ⟨j, rfl | rfl⟩ | ⟨j, i, rfl | rfl⟩
    · exact kq1 j
    · exact hst _ (kq1 j)
    · exact kq2 j i
    · exact hst _ (kq2 j i)
end

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem lift_eq' {n : ℕ} {B C G : Type} [CommRing B] [CommRing C] [Algebra B C] [Group G]
    (ρ : G →* Matrix (Fin n) (Fin n) C) (z : MonoidAlgebra B G) :
    MonoidAlgebra.lift B _ G ρ z = GDet.repAlg ρ C (MonoidAlgebra.mapRingHom G (algebraMap B C) z) := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add (f := _), hf, hg, map_add (f := _), map_add (f := _)]
  | single g b =>
    simp [GDet.repAlg, MonoidAlgebra.lift_single, algebraMap_smul]

theorem UpperTheory.V.Pa.rep_quot :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∃ ρ : u.D.CHQuot P.gens →+* Matrix (Fin n) (Fin n) x.A, ∀ y, ρ (u.D.toQuot P.gens y) = P.rep y := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P
  letI : Algebra B x.A := P.f.toRingHom.toAlgebra
  haveI : CompactSpace G.G₀ :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ G.η_open).isCompact
  have hp : Continuous h.p₀ := (h.cont.comp continuous_subtype_val).subtype_mk _
  have h1 : maximalIdeal B ≤ Ideal.comap (algebraMap B x.A) (maximalIdeal x.A) := by
    intro b hb
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    haveI := (f_surj P).2
    exact (mem_maximalIdeal _).mp hb (isUnit_of_map_unit P.f.toRingHom b hu)
  have h2 : ∀ a b : Fin n, AdicCont (maximalIdeal x.A) fun g ↦ (mat (x.ρ.comp h.p₀)) g a b := by
    intro a b N
    exact (x.cont a b N).comp_continuous hp
  have h3 : u.D.map (algebraMap B x.A) = GDet.ofRep (mat (x.ρ.comp h.p₀)) := P.maps.1
  have h4 : ∀ z ∈ P.gens,
      MonoidAlgebra.lift B (Matrix (Fin n) (Fin n) x.A) G.G₀ (mat (x.ρ.comp h.p₀)) z = 0 := by
    intro z hz
    rw [lift_eq']
    exact rep_gens P z hz
  obtain ⟨ρ, hρ⟩ := f_rep (maximalIdeal x.A) u.D (mat (x.ρ.comp h.p₀)) P.gens h1 h2 h3 h4
  refine ⟨ρ.toRingHom, fun y => ?_⟩
  have hext : ρ.comp (u.D.toQuot P.gens) = MonoidAlgebra.lift B _ G.G₀ (mat (x.ρ.comp h.p₀)) :=
    MonoidAlgebra.algHom_ext (fun g => by simp [hρ]) (Subsingleton.elim _ _)
  have hy := congrArg (fun φ => φ y) hext
  simp only [AlgHom.comp_apply] at hy
  change ρ (u.D.toQuot P.gens y) = _
  rw [hy, lift_eq']
  rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.Trinv
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.StarClosure
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

section
variable {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R]
  [Algebra O R] (n : ℕ)

private theorem star_closure_conj_cont : Continuous F.conj := by
  apply Continuous.subtype_mk
  fun_prop

end

private theorem exists_unit_valuation_le_subset_nhds {l : ℕ} [Fact l.Prime] (F : GFrame l) (N : ℕ) (H : OpenNormalSubgroup F.G₀) :
    ∃ H' : OpenNormalSubgroup F.G₀, ∀ h ∈ H', (F.conj h)⁻¹ ∈ H ∧ ((F.ε h : ℤ_[l]) - 1) ∈ Ideal.span {(l : ℤ_[l]) ^ N} := by
  let φ : F.G₀ →* (ZMod (l ^ N))ˣ :=
    (Units.map (PadicInt.toZModPow N : ℤ_[l] →+* ZMod (l ^ N)).toMonoidHom).comp (F.ε.comp F.η.ker.subtype)
  have hK : ∀ h : F.G₀, h ∈ φ.ker ↔ ((F.ε h : ℤ_[l]) - 1) ∈ Ideal.span {(l : ℤ_[l]) ^ N} := by
    intro h
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, sub_eq_zero, MonoidHom.mem_ker, Units.ext_iff]
    rfl
  let S0 : Subgroup F.G₀ := φ.ker ⊓ Subgroup.comap F.conj (H : Subgroup F.G₀)
  have hN : S0.Normal := by
    haveI : (Subgroup.comap F.conj (H : Subgroup F.G₀)).Normal := Subgroup.Normal.comap H.isNormal' F.conj
    exact Subgroup.normal_inf_normal _ _
  have hcont : Continuous (fun g : F.G₀ => ((F.ε g : ℤ_[l]ˣ) : ℤ_[l])) :=
    Units.continuous_val.comp (F.ε_cont.comp continuous_subtype_val)
  have hopen : IsOpen (S0 : Set F.G₀) := by
    apply Subgroup.isOpen_of_mem_nhds S0 (g := 1)
    apply Filter.inter_mem
    · have hb : (fun g : F.G₀ => ((F.ε g : ℤ_[l]ˣ) : ℤ_[l])) ⁻¹' Metric.ball 1 ((l : ℝ) ^ (-(N : ℤ))) ∈ nhds (1 : F.G₀) := by
        apply hcont.continuousAt.preimage_mem_nhds
        have h1 : ((F.ε ((1 : F.G₀) : F.Γ) : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by simp
        rw [h1]
        apply Metric.ball_mem_nhds
        have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
        positivity
      apply Filter.mem_of_superset hb
      intro g hg
      simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hg
      show g ∈ φ.ker
      rw [hK, ← PadicInt.norm_le_pow_iff_mem_span_pow]
      exact hg.le
    · apply (H.isOpen'.preimage (star_closure_conj_cont F)).mem_nhds
      show F.conj 1 ∈ (H : Subgroup F.G₀)
      rw [map_one]
      exact one_mem _
  refine ⟨⟨⟨S0, hopen⟩, hN⟩, ?_⟩
  intro h hh
  have hh' : h ∈ S0 := hh
  refine ⟨inv_mem hh'.2, (hK h).1 hh'.1⟩

theorem UpperTheory.V.Pa.star_closure :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (n : ℕ) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (I : Ideal R) (S : Set (MonoidAlgebra R F.G₀)), (l : R) ∈ I → (∀ z ∈ S, F.star O R n z ∈ TwoSidedIdeal.span S) → ∀ y ∈ closureIdeal I S, F.star O R n y ∈ closureIdeal I S := by
  intro l _ F n O _ _ R _ _ I S hl hS y hy
  have hadd : ∀ y z, F.star O R n (y + z) = F.star O R n y + F.star O R n z := by
    intro y z
    simp [GFrame.star, map_add (f := _)]
  have hneg : ∀ y, F.star O R n (-y) = -F.star O R n y := by
    intro y
    simp [GFrame.star, map_neg]
  have hsub : ∀ y z, F.star O R n (y - z) = F.star O R n y - F.star O R n z := by
    intro y z
    simp [GFrame.star, map_sub]
  have hzero : F.star O R n 0 = 0 := by simp [GFrame.star]
  have hmul : ∀ y z, F.star O R n (y * z) = F.star O R n z * F.star O R n y := by
    intro y z
    simp [GFrame.star, map_mul]
  have hsingle : ∀ (g : F.G₀) (b : R), F.star O R n (MonoidAlgebra.single g b) =
      MonoidAlgebra.single (F.conj g)⁻¹ (b * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
    intro g b
    simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]
  have h1 : F.star O R n 1 = 1 := by simp [GFrame.star, map_one]
  simp only [closureIdeal, TwoSidedIdeal.mem_iInf] at hy ⊢
  intro N H
  obtain ⟨H', hH'⟩ := exists_unit_valuation_le_subset_nhds F N H
  set T := TwoSidedIdeal.span (S ∪ {z : MonoidAlgebra R F.G₀ | ∃ a ∈ I ^ N, z = MonoidAlgebra.single 1 a} ∪
    {z : MonoidAlgebra R F.G₀ | ∃ h ∈ H, z = MonoidAlgebra.single h 1 - 1}) with hT
  have hJ : ∀ a ∈ I ^ N, MonoidAlgebra.single (1 : F.G₀) a ∈ T := by
    intro a ha
    apply TwoSidedIdeal.subset_span
    exact Or.inl (Or.inr ⟨a, ha, rfl⟩)
  have hKH : ∀ h ∈ H, MonoidAlgebra.single h (1 : R) - 1 ∈ T := by
    intro h hh
    apply TwoSidedIdeal.subset_span
    exact Or.inr ⟨h, hh, rfl⟩
  have hST : TwoSidedIdeal.span S ≤ T := by
    rw [TwoSidedIdeal.span_le]
    exact (Set.subset_union_left.trans Set.subset_union_left).trans TwoSidedIdeal.subset_span
  have heps : ∀ h ∈ H', ((F.eps O R h : Rˣ) : R) - 1 ∈ I ^ N := by
    intro h hh
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (hH' h hh).2
    have hv : ((F.eps O R h : Rˣ) : R) = algebraMap O R (algebraMap ℤ_[l] O ((F.ε h : ℤ_[l]ˣ) : ℤ_[l])) := by
      simp [GFrame.eps, pushCh]
    rw [hv, eq_add_of_sub_eq' ht.symm]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast, map_one, add_sub_cancel_left]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hl N)
  refine TwoSidedIdeal.span_induction (p := fun x _ => F.star O R n x ∈ T) ?_ ?_ ?_ ?_ ?_ ?_ (hy N H')
  · rintro x ((hx | ⟨a, ha, rfl⟩) | ⟨h, hh, rfl⟩)
    · exact hST (hS x hx)
    · rw [hsingle]
      simpa using hJ a ha
    · have hk : (h ^ (1 - (n : ℤ))) ∈ H' := zpow_mem hh _
      have hu := heps _ hk
      rw [map_zpow] at hu
      rw [hsub, hsingle, one_mul, h1]
      set u : R := ((F.eps O R h ^ (1 - (n : ℤ)) : Rˣ) : R)
      have hsplit : MonoidAlgebra.single (F.conj h)⁻¹ u - 1 =
          MonoidAlgebra.single (F.conj h)⁻¹ (1 : R) * MonoidAlgebra.single 1 (u - 1) +
            (MonoidAlgebra.single (F.conj h)⁻¹ (1 : R) - 1) := by
        rw [MonoidAlgebra.single_mul_single, mul_one, one_mul, MonoidAlgebra.single_sub]
        abel
      rw [hsplit]
      exact T.add_mem (T.mul_mem_left _ _ (hJ _ hu)) (hKH _ (hH' h hh).1)
  · rw [hzero]
    exact T.zero_mem
  · intro x z _ _ hx hz
    rw [hadd]
    exact T.add_mem hx hz
  · intro x _ hx
    rw [hneg]
    exact T.neg_mem hx
  · intro a x _ hx
    rw [hmul]
    exact T.mul_mem_right _ _ hx
  · intro b x _ hx
    rw [hmul]
    exact T.mul_mem_left _ _ hx
end

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.trinv :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] {r : Resid F O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B), PhiCond F.G₀ l → 1 ≤ n → ∀ Z : Set (MonoidAlgebra B F.G₀), (∀ z ∈ Z, u.D.Kills z ∧ F.star O B n z ∈ Z) → ∃ (DE : Det n B (u.D.CHQuot Z)) (T : TrInv B (u.D.CHQuot Z)), DE.IsCH ∧ DE.pull (u.D.toQuot Z) = u.D.toDet ∧ (∀ y, T.st (u.D.toQuot Z y) = u.D.toQuot Z (F.star O B n y)) ∧ ∀ y, T.tr y = DE.tr y := by
  intro l _ F n O _ _ _ _ _ r B _ _ _ u hΦ hn Z hZ
  letI := F.grp
  letI := F.top
  haveI := F.tgrp
  haveI := F.cpt
  haveI := F.tdisc
  haveI : CompactSpace F.G₀ := by
    have hc : IsClosed (F.η.ker : Set F.Γ) := Subgroup.isClosed_of_isOpen _ F.η_open
    exact isCompact_iff_compactSpace.mp hc.isCompact
  obtain ⟨DE, hCH, hpull⟩ := d_quotDet u.D u.cont Z (fun z hz => (hZ z hz).1)
  have hl : ((l : ℕ) : B) ∈ maximalIdeal B := by
    have h1 : ((l : ℕ) : O) ∈ maximalIdeal O := by
      haveI := (IsCoef.char (l := l) (O := O))
      rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
      exact CharP.cast_eq_zero _ l
    rw [← map_natCast (algebraMap O B), IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => ((IsLocalRing.mem_maximalIdeal _).mp h1) (isUnit_of_map_unit (algebraMap O B) _ hu)
  have hM : Submodule.span B
      ((MonoidHom.mrange (MonoidAlgebra.of B F.G₀) : Submonoid (MonoidAlgebra B F.G₀)) :
        Set (MonoidAlgebra B F.G₀)) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    refine MonoidAlgebra.induction_on x ?_ ?_ ?_
    · intro m
      exact Submodule.subset_span ⟨m, rfl⟩
    · intro x y hx hy
      exact Submodule.add_mem _ hx hy
    · intro b x hx
      exact Submodule.smul_mem _ b hx
  have hlam : ∀ x ∈ MonoidHom.mrange (MonoidAlgebra.of B F.G₀), ∀ i : ℕ, 1 ≤ i → i ≤ n →
      u.D.toDet.lam i (MulOpposite.unop (F.starOp O B n x)) = u.D.toDet.lam i x := by
    rintro _ ⟨g, rfl⟩ i _ _
    rw [(d_toDet u.D _).2.1, (d_toDet u.D _).2.1]
    exact u.P i g
  obtain ⟨hop, hCHs, -⟩ := d_star u.D.toDet (F.starOp O B n) _ hM hlam
  have hstarCH : ∀ z ∈ u.D.CH, F.star O B n z ∈ TwoSidedIdeal.span (u.D.CH ∪ Z) := by
    intro z hz
    have hz' : z ∈ u.D.toDet.CH := by
      rw [d_toDet_CH]
      exact TwoSidedIdeal.subset_span hz
    have h2 := hCHs z hz'
    rw [d_toDet_CH] at h2
    exact TwoSidedIdeal.span_mono Set.subset_union_left h2
  have hI : ∀ y, y ∈ u.D.chBar Z → F.star O B n y ∈ u.D.chBar Z := by
    unfold GDet.chBar
    refine star_closure F n O B (maximalIdeal B) (u.D.CH ∪ Z) hl ?_
    rintro z (hz | hz)
    · exact hstarCH z hz
    · exact TwoSidedIdeal.subset_span (Or.inr (hZ z hz).2)
  have hq : ∀ a b, u.D.toQuot Z a = u.D.toQuot Z b ↔ a - b ∈ u.D.chBar Z := by
    intro a b
    unfold GDet.toQuot
    exact Iff.trans (RingCon.eq _) (TwoSidedIdeal.rel_iff _ _ _)
  have hsurj : Function.Surjective (u.D.toQuot Z) := RingCon.mkₐ_surjective _
  let ψ : u.D.CHQuot Z →ₐ[B] (u.D.CHQuot Z)ᵐᵒᵖ :=
    RingCon.liftₐ (u.D.chBar Z).ringCon ((AlgHom.op (u.D.toQuot Z)).comp (F.starOp O B n)) (by
      intro a b hab
      rw [TwoSidedIdeal.rel_iff] at hab
      show MulOpposite.op (u.D.toQuot Z (F.star O B n a)) = MulOpposite.op (u.D.toQuot Z (F.star O B n b))
      congr 1
      rw [hq, ← (star_basic F n O B).2.2.2.2.2.1]
      exact hI _ hab)
  have hψ : ∀ y, MulOpposite.unop (ψ (u.D.toQuot Z y)) = u.D.toQuot Z (F.star O B n y) := fun y => rfl
  obtain ⟨t, ht⟩ := (d_tr DE).1 hn
  have htq : ∀ w, DE.tr (u.D.toQuot Z w) = u.D.toDet.tr w := by
    intro w
    show (-1) ^ 1 * (DE.chi _).coeff (n - 1) = (-1) ^ 1 * (u.D.toDet.chi w).coeff (n - 1)
    rw [← hpull, (d_pull DE (u.D.toQuot Z)).1 w]
  have hinv : ∀ w, u.D.toDet.chi (F.star O B n w) = u.D.toDet.chi w := by
    intro w
    conv_rhs => rw [← hop]
    rw [(d_pull _ (F.starOp O B n)).1 w]
    exact ((d_op _).1 (F.star O B n w)).symm
  refine ⟨DE,
    { st := { toFun := fun x => MulOpposite.unop (ψ x)
              map_add' := fun x y => by simp
              map_smul' := fun b x => by simp }
      st_mul := fun x y => by simp
      st_st := ?_
      tr := t
      tr_comm := ?_
      tr_st := ?_ }, hCH, hpull, fun y => hψ y, fun y => ht y⟩
  · intro x
    obtain ⟨y, rfl⟩ := hsurj x
    change MulOpposite.unop (ψ (MulOpposite.unop (ψ (u.D.toQuot Z y)))) = u.D.toQuot Z y
    rw [hψ, hψ, (star_basic F n O B).1]
  · intro x y
    rw [ht, ht]
    exact (d_tr DE).2.1 1 x y
  · intro x
    obtain ⟨y, rfl⟩ := hsurj x
    change t (MulOpposite.unop (ψ (u.D.toQuot Z y))) = t (u.D.toQuot Z y)
    rw [hψ, ht, ht, htq, htq]
    show (-1) ^ 1 * (u.D.toDet.chi _).coeff (n - 1) = (-1) ^ 1 * (u.D.toDet.chi y).coeff (n - 1)
    rw [hinv]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.ToTMap
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem toT_map {B G : Type} [CommRing B] [Group G] (C : Type) [CommRing C] [Algebra B C]
    (y : MonoidAlgebra B G) : toT B G C (MonoidAlgebra.mapRingHom G (algebraMap B C) y) = 1 ⊗ₜ y := by
  have h := toT_ofT (A := B) (S := C) (1 ⊗ₜ y)
  rwa [ofT_tmul, one_smul] at h

theorem UpperTheory.V.Pa.tens :
    ∀ {n : ℕ} {B G E : Type} [CommRing B] [Group G] [Ring E] [Algebra B E] (D : GDet n B G) (DE : Det n B E) (π : MonoidAlgebra B G →ₐ[B] E) (C : Type) [CommRing C] [Algebra B C], Function.Surjective π → DE.pull π = D.toDet → ∃ ι : MonoidAlgebra C G →ₐ[C] C ⊗[B] E, Function.Surjective ι ∧ (∀ y, ι (MonoidAlgebra.mapRingHom G (algebraMap B C) y) = 1 ⊗ₜ π y) ∧ (∀ y, ι y = 0 ↔ y ∈ TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G (algebraMap B C) '' {z | π z = 0})) ∧ (DE.baseChange C).pull ι = (D.map (algebraMap B C)).toDet := by
  intro n B G E _ _ _ _ D DE π C _ _ hπ hD
  let m : C ⊗[B] MonoidAlgebra B G →ₐ[C] C ⊗[B] E := Algebra.TensorProduct.map (AlgHom.id C C) π
  have hm : ∀ x, m x = π.toLinearMap.lTensor C x := fun x => by
    induction x with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul s y => rfl
  have h2 : ∀ y, m (toT B G C (MonoidAlgebra.mapRingHom G (algebraMap B C) y)) = 1 ⊗ₜ π y := fun y => by
    rw [toT_map]; rfl
  refine ⟨m.comp (toT B G C), fun w => ?_, h2, fun y => ⟨fun hy => ?_, fun hy => ?_⟩, ?_⟩
  · obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective C (g := π.toLinearMap) hπ w
    exact ⟨ofT B G C x, by rw [AlgHom.comp_apply, toT_ofT, hm, hx]⟩
  · rw [AlgHom.comp_apply, hm] at hy
    obtain ⟨x, hx⟩ := (lTensor_exact C (LinearMap.exact_subtype_ker_map π.toLinearMap) hπ _).1 hy
    rw [← ofT_toT (A := B) y, ← hx]
    clear hx
    induction x with
    | add a b ha hb => rw [map_add (f := _), map_add (f := _)]; exact add_mem ha hb
    | tmul s z =>
      rw [LinearMap.lTensor_tmul, ofT_tmul, Algebra.smul_def]
      exact TwoSidedIdeal.mul_mem_left _ _ _ (TwoSidedIdeal.subset_span ⟨z, z.2, rfl⟩)
  · have hle : TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G (algebraMap B C) '' {z | π z = 0}) ≤
        TwoSidedIdeal.ker (m.comp (toT B G C)) := by
      rw [TwoSidedIdeal.span_le]
      rintro _ ⟨z, hz, rfl⟩
      refine (TwoSidedIdeal.mem_ker _).2 ((h2 z).trans ?_)
      rw [show π z = 0 from hz, TensorProduct.tmul_zero]
    exact (TwoSidedIdeal.mem_ker _).1 (hle hy)
  · rw [d_toDet_map, ← hD]
    refine Det.ext' fun S _ _ x => ?_
    letI : Algebra B S := ((algebraMap C S).comp (algebraMap B C)).toAlgebra
    haveI : IsScalarTower B C S := .of_algebraMap_eq fun _ => rfl
    have h : Det.cancel B E C S (Algebra.TensorProduct.map (AlgHom.id S S) (m.comp (toT B G C)) x) =
        Algebra.TensorProduct.map (AlgHom.id S S) π (Det.cancel B (MonoidAlgebra B G) C S
          (Algebra.TensorProduct.map (AlgHom.id S S) (toT B G C) x)) := by
      induction x with
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
      | tmul s y =>
        rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.comp_apply]
        generalize toT B G C y = w
        induction w with
        | add a b ha hb => simp only [TensorProduct.tmul_add, map_add (f := _), ha, hb]
        | tmul c z => simp [m, Det.cancel_tmul]
    exact congrArg (DE.D S) h
end

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem lift_ex {B C E M : Type} [CommRing B] [CommRing C] [Algebra B C] [Ring E] [Algebra B E] [Ring M]
    [Algebra C M] (ρ : E →+* M) (hρ : ∀ b, ρ (algebraMap B E b) = algebraMap C M (algebraMap B C b)) :
    ∃ r : C ⊗[B] E →ₐ[C] M, ∀ y, r (1 ⊗ₜ y) = ρ y := by
  letI : Algebra B M := Algebra.compHom M (algebraMap B C)
  haveI : IsScalarTower B C M := .of_algebraMap_eq' rfl
  let ρ' : E →ₐ[B] M := { ρ with commutes' := hρ }
  refine ⟨Algebra.TensorProduct.lift (Algebra.ofId C M) ρ' fun s _ => Algebra.commute_algebraMap_left s _, fun y => ?_⟩
  refine (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans ?_
  rw [map_one, one_mul]
  rfl

private theorem tr_bc {n : ℕ} {B E : Type} [CommRing B] [Ring E] [Algebra B E] (D : Det n B E) (hn : 1 ≤ n)
    (C : Type) [CommRing C] [Algebra B C] (t : C ⊗[B] E →ₗ[C] C) (ht : ∀ y, t (1 ⊗ₜ y) = algebraMap B C (D.tr y))
    (y : C ⊗[B] E) : t y = (D.baseChange C).tr y := by
  obtain ⟨t', ht'⟩ := (d_tr (D.baseChange C)).1 hn
  rw [← ht']
  induction y with
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul c z =>
    have : c ⊗ₜ[B] z = c • ((1 : C) ⊗ₜ[B] z) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul, map_smul, ht, ht']
    congr 1
    exact (((d_bc D C).2.2.2 z).2 1).symm

theorem UpperTheory.V.Pa.hat_ex :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)], (∀ b, algebraMap Bh (FractionRing x.A) (algebraMap B Bh b) = algebraMap x.A (FractionRing x.A) (P.f b)) → Nonempty (Hat h x u.D P.ker Bh (G.frame.eps O B)) := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P Bh _ _ _ _ hB
  have hrep : ∀ (g : G.G₀) (b : B), P.rep (MonoidAlgebra.single g b) = P.f b • mat x.ρ (h.p₀ g) := by
    clear hB
    intro g b
    simp only [OoPt.rep, GDet.repAlg, RingHom.comp_apply, MonoidAlgebra.mapRingHom_single,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidHom.coe_comp,
      Function.comp_apply, RingHom.mapMatrix_apply, Algebra.algebraMap_self]
    rfl
  have hρv : ∀ (b : B) (i j : Fin n), (algebraMap x.A (FractionRing x.A)) ((P.rep (MonoidAlgebra.single 1 b)) i j) =
      algebraMap Bh (Matrix (Fin n) (Fin n) (FractionRing x.A)) (algebraMap B Bh b) i j := by
    intro b i j
    rw [hrep, map_one, map_one, Matrix.smul_apply, Matrix.algebraMap_matrix_apply]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, if_pos rfl, hB, smul_eq_mul, mul_one]
    · rw [Matrix.one_apply_ne hij, if_neg hij, smul_zero, map_zero]
  have hφ : PhiCond G.frame.G₀ l := phi_fg _ P.fg
  have hn : 1 ≤ n := le_trans x.a_pos x.a_le
  haveI : IsAdicComplete (maximalIdeal B) B := IsCO.complete (O := O)
  haveI : CompactSpace G.frame.G₀ :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ G.frame.η_open).isCompact
  obtain ⟨DE, T, hCH, hpull, hst, htr⟩ := trinv u hφ hn P.gens (gens_kill P)
  obtain ⟨hres, -, hh, χ, hred, hmf⟩ := pair_mf u hφ
  obtain ⟨-, hfinB, hcont⟩ := finE u.D χ u.cont hred hmf P.gens
  have hπs : Function.Surjective (u.D.toQuot P.gens) := fun q =>
    Quotient.inductionOn' q fun z => ⟨z, rfl⟩
  obtain ⟨ι, hιs, hιmap, hιker, hιpull⟩ := tens u.D DE (u.D.toQuot P.gens) Bh hπs hpull
  have hker : {z | u.D.toQuot P.gens z = 0} = P.ker := by
    ext z
    change ((z : (u.D.chBar P.gens).ringCon.Quotient) = ((0 : MonoidAlgebra B G.G₀) : _)) ↔ _
    rw [RingCon.eq, TwoSidedIdeal.rel_iff, sub_zero]
    rfl
  rw [hker] at hιker
  have hs : ∀ g : G.G₀, ι (MonoidAlgebra.single g 1) = 1 ⊗ₜ[B] u.D.toQuot P.gens (MonoidAlgebra.single g 1) := by
    intro g
    have := hιmap (MonoidAlgebra.single g 1)
    rwa [MonoidAlgebra.mapRingHom_single, map_one] at this
  haveI : Module.Finite B (u.D.CHQuot P.gens) := hfinB
  obtain ⟨T', hT'st, hT'tr⟩ := trinv_baseChange T Bh
  obtain ⟨ρ0, hρ0⟩ := rep_quot P
  have hρ : ∀ b : B, ((algebraMap x.A (FractionRing x.A)).mapMatrix.comp ρ0)
      (algebraMap B (u.D.CHQuot P.gens) b) =
      algebraMap Bh (Matrix (Fin n) (Fin n) (FractionRing x.A)) (algebraMap B Bh b) := by
    intro b
    have e1 : algebraMap B (u.D.CHQuot P.gens) b = u.D.toQuot P.gens (MonoidAlgebra.single 1 b) :=
      ((u.D.toQuot P.gens).commutes b).symm
    ext i j
    rw [RingHom.comp_apply, e1, hρ0, RingHom.mapMatrix_apply, Matrix.map_apply, hρv]
  obtain ⟨rr, hrr⟩ := lift_ex ((algebraMap x.A (FractionRing x.A)).mapMatrix.comp ρ0) hρ
  have hπg : ∀ (g : G.G₀) (c : B), u.D.toQuot P.gens (MonoidAlgebra.single g c) =
      c • u.D.toQuot P.gens (MonoidAlgebra.single g 1) := by
    intro g c
    rw [← map_smul, MonoidAlgebra.smul_single', mul_one]
  refine ⟨Hat.mk (Bh ⊗[B] u.D.CHQuot P.gens) inferInstance ι hιs hιker (DE.baseChange Bh)
    ((d_chS DE Bh).2.2 hCH).1 hιpull T' (fun y => tr_bc DE hn Bh T'.tr (fun z => by rw [hT'tr, htr]) y)
    (fun g => ?_) rr (fun g => ?_) (Submodule.map (TensorProduct.mk B Bh (u.D.CHQuot P.gens) 1) ⊤)
    (Module.Finite.fg_top.map _) (fun g => ⟨_, trivial, (hs g).symm⟩) (fun j => ?_)⟩
  · rw [hs, hs, hT'st, hst, (star_basic G.frame n O B).2.2.2.2.2.2 g 1, one_mul, hπg,
      TensorProduct.tmul_smul, algebraMap_smul]
  · rw [hs, hrr, RingHom.comp_apply, hρ0, hrep, map_one, one_smul, RingHom.mapMatrix_apply]
  · obtain ⟨U, hU⟩ := hcont j
    refine ⟨U, fun g v hv => ?_⟩
    have hl : u.D.toQuot P.gens (MonoidAlgebra.single g 1) * (u.D.toQuot P.gens (MonoidAlgebra.single v 1) - 1) ∈
        (maximalIdeal B ^ j • ⊤ : Submodule B (u.D.CHQuot P.gens)) := by
      have := Submodule.mem_map_of_mem
        (f := LinearMap.mulLeft B (u.D.toQuot P.gens (MonoidAlgebra.single g 1))) (hU v hv)
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    have key := Submodule.mem_map_of_mem (f := TensorProduct.mk B Bh (u.D.CHQuot P.gens) 1) hl
    rw [Submodule.map_smul''] at key
    convert key using 1
    have e : MonoidAlgebra.single (g * v) (1 : B) = MonoidAlgebra.single g 1 * MonoidAlgebra.single v 1 := by
      rw [MonoidAlgebra.single_mul_single, mul_one]
    rw [hs, hs, TensorProduct.mk_apply, e, map_mul, mul_sub, mul_one, TensorProduct.tmul_sub]
