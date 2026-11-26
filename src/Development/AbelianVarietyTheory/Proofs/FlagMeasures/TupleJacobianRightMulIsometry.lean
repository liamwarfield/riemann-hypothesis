module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelativeLatticeVolumeOfDetValuation
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TupleJacobianRightMulIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TupleJacobianRightMulIsometry
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TupleJac

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem exists_int_basis [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) :
    ∃ c : Module.Basis (Fin 2) F E, (∀ x, x ∈ L.O ↔ ∀ i, c.repr x i ∈ 𝒪[F]) ∧
      ∀ x, algebraMap F E (Algebra.norm F x) = x * L.cj x := by
  obtain ⟨ω, hω, e, he, hωe⟩ := GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L
  have hinj := GlobalTheory.UnramOrder.algebraMap_inj L
  have hu : IsUnit (ω - L.cj ω) := IsUnit.of_mul_eq_one e hωe
  have hli : LinearIndependent F ![(1 : E), ω] := by
    rw [LinearIndependent.pair_iff]
    intro a b h
    simp only [Algebra.smul_def, mul_one] at h
    have h' := congrArg L.cj h
    simp only [map_add (f := _), map_mul, AlgEquiv.commutes, map_zero] at h'
    have hb : algebraMap F E b = 0 := hu.mul_left_eq_zero.1 (by linear_combination h - h')
    have ha : algebraMap F E a = 0 := by rw [hb] at h; simpa using h
    exact ⟨hinj (by simpa using ha), hinj (by simpa using hb)⟩
  let c : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [L.rank])
  have hc0 : c 0 = 1 := by simp [c]
  have hc1 : c 1 = ω := by simp [c]
  have hx : ∀ x, x = algebraMap F E (c.repr x 0) + algebraMap F E (c.repr x 1) * ω := by
    intro x
    have := c.sum_repr x
    simp only [Fin.sum_univ_two, hc0, hc1, Algebra.smul_def, mul_one] at this
    exact this.symm
  have hr : ∀ a b : F, c.repr (algebraMap F E a + algebraMap F E b * ω) 0 = a ∧
      c.repr (algebraMap F E a + algebraMap F E b * ω) 1 = b := by
    intro a b
    have : algebraMap F E a + algebraMap F E b * ω = a • c 0 + b • c 1 := by
      simp [hc0, hc1, Algebra.smul_def]
    rw [this]
    simp
  refine ⟨c, fun x => ⟨fun h => ?_, fun h => ?_⟩, fun x => ?_⟩
  · have h1 := congrArg L.cj (hx x)
    simp only [map_add (f := _), map_mul, AlgEquiv.commutes] at h1
    have hb : algebraMap F E (c.repr x 1) ∈ L.O := by
      have : algebraMap F E (c.repr x 1) = (x - L.cj x) * e := by
        linear_combination (-e) * hx x + e * h1 - algebraMap F E (c.repr x 1) * hωe
      rw [this]
      exact L.O.mul_mem (L.O.sub_mem h (GlobalTheory.UnramOrder.cj_mem L h)) he
    have ha : algebraMap F E (c.repr x 0) ∈ L.O := by
      have : algebraMap F E (c.repr x 0) = x - algebraMap F E (c.repr x 1) * ω := by
        linear_combination - hx x
      rw [this]
      exact L.O.sub_mem h (L.O.mul_mem hb hω)
    intro i
    fin_cases i
    · exact (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 ha
    · exact (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 hb
  · rw [hx x]
    exact L.O.add_mem ((GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (h 0))
      (L.O.mul_mem ((GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (h 1)) hω)
  · obtain ⟨t, ht⟩ := (L.cj_fix (ω + L.cj ω)).1 (by simp [L.cj_cj, add_comm])
    obtain ⟨N, hN⟩ := (L.cj_fix (ω * L.cj ω)).1 (by simp [L.cj_cj, mul_comm])
    obtain ⟨a, b, rfl⟩ : ∃ a b : F, x = algebraMap F E a + algebraMap F E b * ω := ⟨_, _, hx x⟩
    have h2 : (algebraMap F E a + algebraMap F E b * ω) * ω
        = algebraMap F E (-(b * N)) + algebraMap F E (a + b * t) * ω := by
      simp only [map_add (f := _), map_mul, map_neg, ht, hN]; ring
    rw [Algebra.norm_eq_matrix_det c, Matrix.det_fin_two]
    simp only [Algebra.leftMulMatrix_eq_repr_mul, hc0, hc1, mul_one, h2, (hr _ _).1, (hr _ _).2]
    simp only [map_add (f := _), map_mul, map_neg, map_sub, ht, hN, AlgEquiv.commutes]
    ring

theorem exists_lat_basis [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (hH : IsHermND L Hm) (Λ : Submodule L.O (Fin n → E))
    (hΛ : IsSD L Hm Λ) :
    ∃ B : Module.Basis (Fin n) E (Fin n → E), ∀ x, x ∈ Λ ↔ ∀ i, B.repr x i ∈ L.O := by
  obtain ⟨b, hb, rfl⟩ := (GlobalTheory.HL.SelfDual.orthonormal_basis_and_one_orbit L Hm hH).1 Λ hΛ
  have hli : LinearIndependent E b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    let f : (Fin n → E) →ₗ[E] E :=
      { toFun := fun x => hf L Hm x (b j)
        map_add' := fun x y => by simp [hf, add_mul, Finset.sum_add_distrib]
        map_smul' := fun c x => by simp [hf, Finset.mul_sum, mul_assoc] }
    have hfb : ∀ i, f (b i) = if i = j then 1 else 0 := fun i => hb i j
    have := congrArg f hg
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, hfb] using this
  have hsp : ⊤ ≤ Submodule.span E (Set.range b) := by
    rw [← hΛ.1.2, Submodule.span_span_of_tower]
  refine ⟨Module.Basis.mk hli hsp, fun x => ?_⟩
  set B := Module.Basis.mk hli hsp with hB
  have hBb : ∀ i, B i = b i := fun i => by simp [hB]
  constructor
  · intro hx i
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    have : ∑ j, c j • b j = ∑ j, (c j : E) • B j := by simp only [hBb]; rfl
    rw [this, B.repr_sum_self]
    exact (c i).2
  · intro hx
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun i => ⟨_, hx i⟩, ?_⟩
    conv_rhs => rw [← B.sum_repr x]
    simp only [hBb]; rfl

theorem cont_linearEquiv [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) (ϖ : 𝒪[F])
    (hϖ : Irreducible ϖ) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (hH : IsHermND L Hm) (Λ : Submodule L.O (Fin n → E))
    (hΛ : IsSD L Hm Λ) (m : ℕ) (φ : (Fin m → Fin n → E) ≃ₗ[E] (Fin m → Fin n → E))
    (a : ℤ) (u : (𝒪[F])ˣ)
    (hd : LinearMap.det φ.toLinearMap * L.cj (LinearMap.det φ.toLinearMap)
      = algebraMap F E ((ϖ : F) ^ a * ((u : 𝒪[F]) : F))) :
    ∀ T, IsCO (tupLat L Λ m) T → IsCO (tupLat L Λ m) (φ '' T) ∧
      cont (tupLat L Λ m) (φ '' T) = (resQ ϖ : ℝ) ^ (-a) * cont (tupLat L Λ m) T := by
  obtain ⟨c, hc, hN⟩ := exists_int_basis L
  obtain ⟨B, hB⟩ := exists_lat_basis L Hm hH Λ hΛ
  have := L.free
  have h := GlobalTheory.T.relative_lattice_volume_of_det_valuation ϖ hϖ (Pi.basis fun _ : Fin m => c.smulTower B) (φ.restrictScalars F) a u
    (by
      apply GlobalTheory.UnramOrder.algebraMap_inj L
      rw [← hd, ← hN, ← LinearMap.det_restrictScalars]
      rfl) (tupLat L Λ m) (by
      intro x
      simp only [tupLat, AddSubgroup.mem_pi, Set.mem_univ, true_imp_iff,
        Submodule.mem_toAddSubgroup, hB, hc, Pi.basis_repr, Module.Basis.smulTower_repr]
      exact ⟨fun h i => h _ _ _, fun h j i k => h ⟨j, (k, i)⟩⟩)
  intro T hT
  have h2 := GlobalTheory.HL.ContAut.cont_image (tupLat L Λ m) (φ.restrictScalars F).toAddEquiv h.1 h.2.1 T hT
  rw [h.2.2] at h2
  exact h2

def rmulL {n m : ℕ} (A : Matrix (Fin m) (Fin m) E) :
    (Fin m → Fin n → E) →ₗ[E] (Fin m → Fin n → E) where
  toFun x := rmul x A
  map_add' x y := by ext j k; simp [rmul, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by ext j k; simp [rmul, Finset.mul_sum, mul_left_comm]

def swapL (n m : ℕ) : (Fin n → Fin m → E) ≃ₗ[E] (Fin m → Fin n → E) where
  toFun x := fun j k => x k j
  invFun x := fun j k => x k j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [TopologicalSpace E] in
theorem det_rmulL {n m : ℕ} (A : Matrix (Fin m) (Fin m) E) :
    LinearMap.det (rmulL (n := n) A) = A.det ^ n := by
  have h : rmulL (n := n) A = (swapL n m).toLinearMap ∘ₗ
      (LinearMap.pi fun i : Fin n => (Matrix.toLin' A.transpose) ∘ₗ LinearMap.proj i) ∘ₗ
      (swapL n m).symm.toLinearMap := by
    refine LinearMap.ext fun x => ?_
    ext j k
    simp [rmulL, rmul, swapL, Matrix.mulVec, dotProduct]
  rw [h, LinearMap.det_conj, LinearMap.det_pi]
  simp [LinearMap.det_toLin']

theorem det_isom (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (hH : IsUnit Hm.det)
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (hg : g ∈ isomG L Hm) :
    LinearMap.det g.toLinearMap * L.cj (LinearMap.det g.toLinearMap) = 1 := by
  set M := LinearMap.toMatrix' g.toLinearMap with hM
  have h : M.transpose * Hm * (L.cj.toRingEquiv.toRingHom.mapMatrix M) = Hm := by
    ext i j
    have h1 := hg (Pi.single i 1) (Pi.single j 1)
    have h2 : hf L Hm (Pi.single i 1) (Pi.single j 1) = Hm i j := by
      simp [hf, Pi.single_apply, apply_ite L.cj]
    rw [h2] at h1
    rw [← h1, hf, Finset.sum_comm]
    simp [hM, Matrix.mul_apply, Finset.sum_mul, LinearMap.toMatrix'_apply]
  have h3 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det, hM,
    LinearMap.det_toMatrix'] at h3
  refine hH.mul_left_cancel ?_
  rw [mul_one]
  conv_rhs => rw [← h3]
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv,
    AlgEquiv.coe_toRingEquiv]
  ring

end GlobalTheory.HL.TupleJac

theorem GlobalTheory.HL.TupleJac.tuple_jacobian : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ m : ℕ, (∀ A : Matrix (Fin m) (Fin m) E, IsUnit A.det → ∀ T, IsCO (tupLat L Λ m) T → IsCO (tupLat L Λ m) ((fun x => rmul x A) '' T) ∧ cont (tupLat L Λ m) ((fun x => rmul x A) '' T) = (resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * n)) * cont (tupLat L Λ m) T) ∧ ∀ g ∈ isomG L Hm, ∀ T, IsCO (tupLat L Λ m) T → IsCO (tupLat L Λ m) ((fun x a => g (x a)) '' T) ∧ cont (tupLat L Λ m) ((fun x a => g (x a)) '' T) = cont (tupLat L Λ m) T := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λ hΛ m
  refine ⟨fun A hA => ?_, fun g hg T hT => ?_⟩
  · obtain ⟨N, hN⟩ := (L.cj_fix (A.det * L.cj A.det)).1 (by simp [L.cj_cj, mul_comm])
    have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; omega)
    have hN0 : N ≠ 0 := by
      rintro rfl
      rw [map_zero] at hN
      exact (hA.mul (hA.map L.cj)).ne_zero hN.symm
    obtain ⟨u, hu⟩ := (GlobalTheory.UnramVal.vE_valuation L ϖ hϖ).2.2.2 N hN0
    have hdet : IsUnit (LinearMap.det (TupleJac.rmulL (n := n) A)) := by
      rw [TupleJac.det_rmulL]; exact hA.pow n
    have hφ : (LinearMap.equivOfIsUnitDet hdet).toLinearMap = TupleJac.rmulL (n := n) A :=
      LinearMap.coe_equivOfIsUnitDet hdet
    have key := TupleJac.cont_linearEquiv L ϖ hϖ Hm hH Λ hΛ m (LinearMap.equivOfIsUnitDet hdet)
      (vE L ϖ (A.det * L.cj A.det) * n) (u ^ n) (by
        rw [hφ, TupleJac.det_rmulL, map_pow, ← mul_pow, ← hN, ← map_pow]
        congr 1
        conv_lhs => rw [hu]
        rw [mul_pow, zpow_mul, zpow_natCast]
        simp)
    have hfun : (LinearMap.equivOfIsUnitDet hdet : _ → _) = fun x => rmul x A :=
      funext fun x => LinearMap.congr_fun hφ x
    rw [hfun] at key
    exact key
  · have key := TupleJac.cont_linearEquiv L ϖ hϖ Hm hH Λ hΛ m
      (LinearEquiv.piCongrRight fun _ => g) 0 1 (by
        have h : (LinearEquiv.piCongrRight fun _ : Fin m => g).toLinearMap =
            LinearMap.pi fun i : Fin m => g.toLinearMap ∘ₗ LinearMap.proj i := rfl
        rw [h, LinearMap.det_pi, Finset.prod_const, map_pow, ← mul_pow,
          TupleJac.det_isom L Hm hH.2 g hg]
        simp) T hT
    rw [neg_zero, zpow_zero, one_mul] at key
    exact key
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TupleJacobianRightMulIsometryStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tuple_jacobian_rightMul_isometry : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ m : ℕ, (∀ A : Matrix (Fin m) (Fin m) E, IsUnit A.det → ∀ T, IsCO (tupLat L Λ m) T → IsCO (tupLat L Λ m) ((fun x => rmul x A) '' T) ∧ cont (tupLat L Λ m) ((fun x => rmul x A) '' T) = (resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * n)) * cont (tupLat L Λ m) T) ∧ ∀ g ∈ isomG L Hm, ∀ T, IsCO (tupLat L Λ m) T → IsCO (tupLat L Λ m) ((fun x a => g (x a)) '' T) ∧ cont (tupLat L Λ m) ((fun x a => g (x a)) '' T) = cont (tupLat L Λ m) T := by
  first | exact @GlobalTheory.HL.TupleJac.tuple_jacobian | exact GlobalTheory.HL.TupleJac.tuple_jacobian | (intros; apply GlobalTheory.HL.TupleJac.tuple_jacobian <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalFramesJointGramInvMulSelf
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalFramesJointGramInvMulSelf
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GamInv

theorem hf_add_right {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) {n : ℕ}
    (H : Matrix (Fin n) (Fin n) E) (x y z : Fin n → E) :
    hf L H x (y + z) = hf L H x y + hf L H x z := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_smul_right {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) {n : ℕ}
    (H : Matrix (Fin n) (Fin n) E) (x z : Fin n → E) (c : E) :
    hf L H x (c • z) = L.cj c * hf L H x z := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem main : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k), (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j))⁻¹ * (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j)) = 1 := by
  intro F E _ _ _ _ _ sig A r k G
  classical
  set g : Fin (r + 1) ⊕ Fin (r + 1) → Fin (k + 2 * r + 1) → E := Sum.elim G.f G.f' with hg
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  let p : HeightOneSpectrum (𝓞 F) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩
  obtain ⟨hinj, -, -, -, hform, hind⟩ := GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  obtain ⟨hli, hco, -⟩ := GlobalTheory.FrameBasic.main (A.L p) r k (G.S p)
  set S := G.S p with hS
  set Ep := (A.loc p).Ep
  let s : Fin (r + 1) ⊕ Fin (r + 1) → Epˣ := fun q =>
    Units.map (algebraMap (A.loc p).Fp Ep).toMonoidHom (G.c p ^ (r - (Sum.elim (fun a : Fin (r + 1) => (a : ℕ)) (fun a => (a : ℕ)) q)))
  have hu : ∀ q, A.bc p (g q) = ((s q : Epˣ) : Ep) • Sum.elim S.f S.f' q := by
    intro q
    rcases q with a | a
    · simp only [hg, Sum.elim_inl, s, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]
      exact (G.f_eq p a).symm
    · simp only [hg, Sum.elim_inr, s, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]
      exact (G.f'_eq p a).symm
  have hgli : LinearIndependent E g := by
    let e := (finSumFinEquiv (m := r + 1) (n := r + 1))
    refine (linearIndependent_equiv e.symm).1 ((hind _ (g ∘ e.symm)).2 ?_)
    have : (fun q => A.bc p (g q)) = s • Sum.elim S.f S.f' := by
      funext q; rw [hu]; rfl
    have h2 : LinearIndependent Ep (fun q => A.bc p (g q)) := by
      rw [this]; exact hli.units_smul s
    exact (linearIndependent_equiv e.symm).2 h2
  have hME : S.ME = Submodule.span Ep (Set.range (Sum.elim S.f S.f')) := by
    have h1 : ∀ v : Fin (r + 1) → S.V, S.spanTo v (r + 1) = Submodule.span Ep (Set.range v) := by
      intro v
      unfold Frames.spanTo
      congr 1
      ext y
      simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
      exact ⟨fun ⟨a, _, h⟩ => ⟨a, h⟩, fun ⟨a, h⟩ => ⟨a, a.isLt, h⟩⟩
    rw [Frames.ME, h1, h1, Set.Sum.elim_range, Submodule.span_union]
  set Γ : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
    Matrix.of fun k l => ∑ i, ∑ j, g k i * G.Hm i j * sig (g l j) with hΓ
  have key : ∀ v : Fin (r + 1) ⊕ Fin (r + 1) → E, Matrix.vecMul v Γ = 0 → v = 0 := by
    intro v hv
    set x : Fin (k + 2 * r + 1) → E := ∑ q, v q • g q with hx
    have hx0 : ∀ l, ∑ i, ∑ j, x i * G.Hm i j * sig (g l j) = 0 := by
      intro l
      have h : Matrix.vecMul v Γ l = 0 := congrFun hv l
      rw [← h]
      simp only [Matrix.vecMul, dotProduct, hΓ, Matrix.of_apply, hx, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Finset.sum_mul, Finset.mul_sum, Pi.zero_apply]
      symm
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => by ring
    have hloc : ∀ q, hf (A.L p) S.Hm (A.bc p x) (A.bc p (g q)) = 0 := by
      intro q
      rw [G.Hm_eq p, hform, hx0, map_zero]
    have hbcx : A.bc p x = ∑ q, (A.loc p).ιE (v q) • A.bc p (g q) := by
      funext i
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Places.bc, hx, Finset.sum_apply, map_sum]
    have hmem : A.bc p x ∈ S.ME := by
      rw [hbcx, hME]
      refine Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ ?_
      rw [hu]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
    have hperp : A.bc p x ∈ S.W0 := by
      show ∀ y ∈ S.ME, hf (A.L p) S.Hm (A.bc p x) y = 0
      intro y hy
      rw [hME] at hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨q, rfl⟩ := hy
        have e1 : Sum.elim S.f S.f' q = ((s q)⁻¹ : Epˣ) • A.bc p (g q) := by
          rw [hu, ← Units.smul_def, inv_smul_smul]
        rw [e1, Units.smul_def, hf_smul_right, hloc q, mul_zero]
      | zero => simp [hf]
      | add y z _ _ hy hz => rw [hf_add_right, hy, hz, add_zero]
      | smul c y _ hy => rw [hf_smul_right, hy, mul_zero]
    have hbot : A.bc p x = 0 := by
      have h : A.bc p x ∈ S.ME ⊓ S.W0 := ⟨hmem, hperp⟩
      rw [hco.inf_eq_bot] at h
      exact (Submodule.mem_bot _).1 h
    have hx00 : x = 0 := hinj (by rw [hbot]; funext i; simp [Places.bc])
    funext q
    exact Fintype.linearIndependent_iff.1 hgli v (by rw [← hx]; exact hx00) q
  have hU : IsUnit Γ := Matrix.vecMul_injective_iff_isUnit.1 fun a b h =>
    sub_eq_zero.1 (key _ (by rw [Matrix.sub_vecMul]; exact sub_eq_zero.2 h))
  exact Matrix.nonsing_inv_mul Γ ((Matrix.isUnit_iff_isUnit_det Γ).1 hU)

end GlobalTheory.HL.GamInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalFramesJointGramInvMulSelfStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalFrames_joint_gram_inv_mul_self : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k), (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j))⁻¹ * (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j)) = 1 := by
  first | exact @GlobalTheory.HL.GamInv.main | exact GlobalTheory.HL.GamInv.main | (intros; apply GlobalTheory.HL.GamInv.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameMoveCharacterNeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameMoveCharacterNeOne
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MoveChar

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem coords {g : Fin (r + 1) → S.V} {n : S.GLV} (hn : n ∈ S.Nof g) (j : Fin r) {x : S.V}
    (hx : x ∈ S.spanTo g (j + 1)) :
    ∃ c : Fin (r + 1) → E, (∀ i : Fin (r + 1), (j : ℕ) + 1 ≤ i → c i = 0) ∧ x = ∑ i, c i • n (g i) := by
  have h1 : ∀ v, n v ∈ S.spanTo g (j + 1) ↔ v ∈ S.spanTo g (j + 1) :=
    (Subgroup.mem_iInf.1 hn.1.2 j).1
  obtain ⟨y, rfl⟩ := n.surjective x
  have hy := (h1 y).1 hx
  clear hx
  induction hy using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, hi, rfl⟩ := hv
    refine ⟨Pi.single i 1, fun i' hi' => Pi.single_eq_of_ne ?_ _, ?_⟩
    · rintro rfl
      exact absurd hi (not_lt.2 hi')
    · simp [Pi.single_apply]
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨c, h, e⟩ := ha
    obtain ⟨c', h', e'⟩ := hb
    exact ⟨c + c', fun i hi => by simp [h i hi, h' i hi],
      by rw [map_add (f := _), e, e']; simp [add_smul, Finset.sum_add_distrib]⟩
  | smul t a _ ha =>
    obtain ⟨c, h, e⟩ := ha
    exact ⟨t • c, fun i hi => by simp [h i hi],
      by rw [map_smul, e]; simp [Finset.smul_sum, mul_smul]⟩

theorem uniq {g g' : Fin (r + 1) → S.V} (hl : LinearIndependent E (Sum.elim g g'))
    {a a' b b' : Fin (r + 1) → E}
    (h : ∑ i, a i • g i + ∑ i, a' i • g' i = ∑ i, b i • g i + ∑ i, b' i • g' i) :
    a = b ∧ a' = b' := by
  have := Fintype.linearIndependent_iffₛ.1 hl (Sum.elim a a') (Sum.elim b b')
    (by simpa [Fintype.sum_sum_type] using h)
  exact ⟨funext fun i => this (.inl i), funext fun i => this (.inr i)⟩

theorem lev_le_iff {g g' : Fin (r + 1) → S.V} (hl : LinearIndependent E (Sum.elim g g'))
    (a a' : Fin (r + 1) → E) (j : ℕ) :
    S.lev g g' (∑ i, a i • g i + ∑ i, a' i • g' i) ≤ j ↔
      ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (a i) (a' i) := by
  refine ⟨fun h i hi => ?_, fun h => Nat.sInf_le ⟨a, a', rfl, h⟩⟩
  have hne : {j : ℕ | ∃ al al' : Fin (r + 1) → E,
      ∑ i, a i • g i + ∑ i, a' i • g' i = ∑ i, al i • g i + ∑ i, al' i • g' i ∧
      ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (al i) (al' i)}.Nonempty :=
    ⟨r + 1, a, a', rfl, fun i hi => absurd i.2 (not_lt.2 hi)⟩
  obtain ⟨b, b', e, hb⟩ := Nat.sInf_mem hne
  obtain ⟨rfl, rfl⟩ := uniq S hl e
  exact hb i (le_trans h hi)

theorem exists_family {g g' : Fin (r + 1) → S.V} (hl : LinearIndependent E (Sum.elim g g'))
    {J : ℕ} (hJ : J ≤ r + 1) : ∃ y : Fin (J + J) → S.V, LinearIndependent E y ∧
      Submodule.span E (Set.range y) = S.spanTo g J ⊔ S.spanTo g' J := by
  refine ⟨Sum.elim g g' ∘ (Sum.map (Fin.castLE hJ) (Fin.castLE hJ) ∘ finSumFinEquiv.symm),
    hl.comp _ (((Fin.castLE_injective hJ).sumMap (Fin.castLE_injective hJ)).comp
      finSumFinEquiv.symm.injective), ?_⟩
  have e : ∀ g : Fin (r + 1) → S.V, Set.range (g ∘ Fin.castLE hJ) = g '' {i | (i : ℕ) < J} := by
    intro g
    rw [Set.range_comp, Fin.range_castLE]
  rw [← Function.comp_assoc, finSumFinEquiv.symm.surjective.range_comp, Sum.elim_comp_map,
    Set.Sum.elim_range, e, e, Submodule.span_union]
  rfl

end GlobalTheory.HL.MoveChar

theorem GlobalTheory.HL.MoveChar.chi_ne_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x ∈ S.spanTo S.f (j + 1), ∀ x' ∈ S.spanTo S.f' (j + 1), S.InTh Λ (x + x') → S.lev (S.fr d Λ) (S.fr' d Λ) (x + x') = j + 1 → ∀ al al' : Fin (r + 1) → E, x = ∑ i, al i • S.fr d Λ i → x' = ∑ i, al' i • S.fr' d Λ i → ∃ u ∈ Λ, u ∈ perp L S.Hm (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)) ∧ L.psi0 (-(algebraMap F E S.th⁻¹ * S.h (al j.castSucc • S.fr d Λ j.succ + al' j.castSucc • S.fr' d Λ j.succ) u)) ≠ 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hFF x hx x' hx' _ hlev al al' ex ex'
  obtain ⟨hSD, hW, -, h1, h2, hl, -⟩ := TermBasic.term_basic L r k S d Λ hT
  obtain ⟨hl0, -, -, -, -, hth, -⟩ := GlobalTheory.FrameBasic.main L r k S
  obtain ⟨-, -, hn, hn', -⟩ := hW

  have hRR : ¬ S.RR (al j.castSucc) (al' j.castSucc) := by
    intro hR
    obtain ⟨c, hc, e⟩ := MoveChar.coords S hn j hx
    obtain ⟨c', hc', e'⟩ := MoveChar.coords S hn' j hx'
    obtain ⟨rfl, rfl⟩ := MoveChar.uniq S hl (a := al) (a' := al') (b := c) (b' := c')
      (by rw [← ex, ← ex']; exact congrArg₂ (· + ·) e e')
    have : S.lev (S.fr d Λ) (S.fr' d Λ) (x + x') ≤ j := by
      rw [ex, ex', MoveChar.lev_le_iff S hl]
      intro i hi
      rcases hi.eq_or_lt with hi | hi
      · rwa [show i = j.castSucc from Fin.ext hi.symm]
      · rw [hc i hi, hc' i hi]
        exact ⟨L.O.zero_mem, 0, L.O.zero_mem, by simp⟩
    omega
  by_contra hcon
  push Not at hcon
  set z := al j.castSucc • S.fr d Λ j.succ + al' j.castSucc • S.fr' d Λ j.succ with hz
  obtain ⟨y, hy, ey⟩ := MoveChar.exists_family S hl0 (J := j + 1) (by omega)
  have hd := (DualInter.dual_inter L S.Hm S.herm Λ hSD _ y hy).2.1 (algebraMap F E S.th⁻¹ • z)
  rw [ey] at hd
  obtain ⟨a, ha, haY⟩ := hd.1 fun u hu huY => by
    have : -(algebraMap F E S.th⁻¹ * S.h z u) ∈ L.O := by
      refine (L.additive_character_dual_ring _).1 fun c hc => ?_
      have := hcon (L.cj c • u) (Λ.smul_mem ⟨_, GlobalTheory.UnramOrder.cj_mem L hc⟩ hu)
        (Submodule.smul_mem _ _ huY)
      rw [← this, Frames.h, Frames.h, DualInter.smul_r, L.cj_cj]
      congr 1
      ring
    rw [← DualInter.cj_hf S.herm, DualInter.smul_l]
    exact GlobalTheory.UnramOrder.cj_mem L (neg_mem_iff.1 this)
  have hjr : (j : ℕ) + 1 ≤ r + 1 := by omega
  have hzM : z ∈ S.ME :=
    Submodule.add_mem_sup
      (Submodule.smul_mem _ _ ((h1 (r + 1) le_rfl _).2 (Submodule.subset_span ⟨j.succ, j.succ.2, rfl⟩)).2)
      (Submodule.smul_mem _ _ ((h2 (r + 1) le_rfl _).2 (Submodule.subset_span ⟨j.succ, j.succ.2, rfl⟩)).2)
  have haM : a ∈ S.ME := by
    have := S.ME.sub_mem (S.ME.smul_mem (algebraMap F E S.th⁻¹) hzM)
      (sup_le_sup (TermBasic.spanTo_mono S S.f hjr) (TermBasic.spanTo_mono S S.f' hjr) haY)
    rwa [sub_sub_cancel] at this
  have hla : S.levC d Λ a ≤ j + 1 := hFF.2.2.1 a ⟨ha, haM⟩
  obtain ⟨v, hv, v', hv', e0⟩ := Submodule.mem_sup.1 (Submodule.smul_mem _ (algebraMap F E S.th) haY)
  obtain ⟨c, hc, e⟩ := MoveChar.coords S hn j hv
  obtain ⟨c', hc', e'⟩ := MoveChar.coords S hn' j hv'
  have key : algebraMap F E S.th • a =
      ∑ i, (Pi.single j.succ (al j.castSucc) - c : Fin (r + 1) → E) i • S.fr d Λ i +
        ∑ i, (Pi.single j.succ (al' j.castSucc) - c' : Fin (r + 1) → E) i • S.fr' d Λ i := by
    rw [smul_sub, smul_smul, ← map_mul, mul_inv_cancel₀ hth, map_one, one_smul] at e0
    have e1 : v = ∑ i, c i • S.fr d Λ i := e
    have e2 : v' = ∑ i, c' i • S.fr' d Λ i := e'
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, ← e1, ← e2, Pi.single_apply, ite_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [sub_add_sub_comm, e0, ← hz, sub_sub_cancel]
  rw [Frames.levC, key, MoveChar.lev_le_iff S hl] at hla
  have := hla j.succ (by simp)
  rw [Pi.sub_apply, Pi.sub_apply, hc _ (by simp), hc' _ (by simp), Pi.single_eq_same, Pi.single_eq_same,
    sub_zero, sub_zero] at this
  exact hRR this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameMoveCharacterNeOneStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMove_character_ne_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x ∈ S.spanTo S.f (j + 1), ∀ x' ∈ S.spanTo S.f' (j + 1), S.InTh Λ (x + x') → S.lev (S.fr d Λ) (S.fr' d Λ) (x + x') = j + 1 → ∀ al al' : Fin (r + 1) → E, x = ∑ i, al i • S.fr d Λ i → x' = ∑ i, al' i • S.fr' d Λ i → ∃ u ∈ Λ, u ∈ perp L S.Hm (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)) ∧ L.psi0 (-(algebraMap F E S.th⁻¹ * S.h (al j.castSucc • S.fr d Λ j.succ + al' j.castSucc • S.fr' d Λ j.succ) u)) ≠ 1 := by
  first | exact @GlobalTheory.HL.MoveChar.chi_ne_one | exact GlobalTheory.HL.MoveChar.chi_ne_one | (intros; apply GlobalTheory.HL.MoveChar.chi_ne_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalPairingMatrixInvMulSelf
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalPairingMatrixInvMulSelf
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GFrames

theorem lead_last_eq_det {R : Type} [CommRing R] {N : ℕ} (Z : Matrix (Fin N) (Fin N) R) :
    lead Z (Fin.last N) = Z.det := by
  unfold lead
  congr 1

theorem Zh_map_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F)) :
    G.Zh.map (A.loc p).ιE =
      Matrix.diagonal (fun a : Fin (r + 1) =>
          algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (a : ℕ)))) *
        (G.S p).Zh *
      Matrix.diagonal (fun a : Fin (r + 1) =>
          algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (a : ℕ)))) := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
  have h := (GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p).2.2.2.2.1 G.Hm (G.f' b) (G.f a)
  have hZ : G.Zh a b = ∑ i, ∑ j, G.f' b i * G.Hm i j * sig (G.f a j) := rfl
  rw [hZ, ← h, ← G.f_eq p a, ← G.f'_eq p b, ← G.Hm_eq p]
  simp only [Frames.Zh, Frames.h, Matrix.of_apply, hf, Pi.smul_apply, smul_eq_mul, map_mul,
    AlgEquiv.commutes, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem Zh_inv_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) : G.Zh⁻¹ * G.Zh = 1 := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  let p : HeightOneSpectrum (𝓞 F) := ⟨P, hP.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
  haveI := GlobalTheory.HL.PlacesInt.nontrivial_Ep (A.loc p)
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  have hS : IsUnit ((G.S p).Zh.det) := by
    have := (GlobalTheory.FrameBasic.main (A.L p) r k (G.S p)).2.2.2.1
    rwa [Frames.D, lead_last_eq_det] at this
  have hd : IsUnit (Matrix.diagonal (fun a : Fin (r + 1) =>
      algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (a : ℕ))))).det := by
    rw [Matrix.det_diagonal, ← map_prod]
    exact (IsUnit.prod_univ_iff.2 fun a => ((G.c p).isUnit.pow _)).map (algebraMap (A.loc p).Fp (A.loc p).Ep)
  have hι : IsUnit ((A.loc p).ιE G.Zh.det) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Zh_map_eq, Matrix.det_mul, Matrix.det_mul]
    exact (hd.mul hS).mul hd
  have hne : G.Zh.det ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hι
    exact not_isUnit_zero hι
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hne)

end GlobalTheory.HL.GFrames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalPairingMatrixInvMulSelfStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalPairingMatrix_inv_mul_self : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k), G.Zh⁻¹ * G.Zh = 1 := by
  first | exact @GlobalTheory.HL.GFrames.Zh_inv_mul | exact GlobalTheory.HL.GFrames.Zh_inv_mul | (intros; apply GlobalTheory.HL.GFrames.Zh_inv_mul <;> assumption)
end
end
