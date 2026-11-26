module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LiftingObstructionSecondCohomology
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem UpperTheory.V.UnitaryThreeInertia.residue_coordinates_decomposition {O M : Type} [CommRing O] [IsLocalRing O] [AddCommGroup M] [Module O M]
    [Finite M] (hM : ∀ a ∈ maximalIdeal O, ∀ x : M, a • x = 0) :
    ∃ (n : ℕ) (p : Fin n → M →ₗ[O] ResidueField O) (q : Fin n → ResidueField O →ₗ[O] M),
      ∀ x, ∑ i, q i (p i x) = x := by
  have hT : Module.IsTorsionBySet O M (maximalIdeal O) := fun x a => hM a.1 a.2 x
  letI : Module (ResidueField O) M := hT.module
  haveI : IsScalarTower O (ResidueField O) M := hT.isScalarTower
  haveI : Module.Finite (ResidueField O) M := Module.Finite.of_finite
  let B := Module.finBasis (ResidueField O) M
  refine ⟨_, fun i => (B.coord i).restrictScalars O,
    fun i => (LinearMap.toSpanSingleton (ResidueField O) M (B i)).restrictScalars O, fun x => ?_⟩
  simpa using B.sum_repr x

private theorem UpperTheory.V.UnitaryThreeInertia.adjoint_diagonal_rep_apply {O S D : Type} [CommRing O] [CommRing S] [Algebra O S] [Group D]
    (η : D →* ℤˣ) (Ψ : D →* Oˣ) (g : D) (X : Matrix (Fin 3) (Fin 3) S) (a b : Fin 3) :
    adRep (r0 η ((Units.map (algebraMap O S).toMonoidHom).comp Ψ)) g X a b =
      ((Ψ g ^ wt a b : Oˣ) : O) • (if η g = 1 then X a b else -X b.rev a.rev) := by
  rw [adRep_baseLift_apply, Algebra.smul_def, MonoidHom.comp_apply, ← map_zpow]
  rfl

private theorem UpperTheory.V.UnitaryThreeInertia.diagonal_rep_map_algebra {O S D : Type} [CommRing O] [CommRing S] [Algebra O S] [Group D]
    (η : D →* ℤˣ) (Ψ : D →* Oˣ) :
    (GG.map (algebraMap O S)).comp (r0 η Ψ) = r0 η ((Units.map (algebraMap O S).toMonoidHom).comp Ψ) := by
  ext g i j
  · simp [r0, GG.map]
    rw [tor_val, tor_val, Matrix.diagonal_apply, Matrix.diagonal_apply]
    split_ifs
    · rw [← map_zpow, ← map_zpow, Units.coe_map, map_zpow]
      rfl
    · simp
  · simp [r0, GG.map]

private theorem UpperTheory.V.UnitaryThreeInertia.residual_cocycle_is_coboundary {k D : Type} [CommRing k] [Group D] [TopologicalSpace D]
    (η : D →* ℤˣ) (Ψ : D →* kˣ) (j : ℤ) (h : Subsingleton (H2 (gRep η Ψ j)))
    (κ : D × D → Matrix (Fin 3) (Fin 3) k) (hc : IsLocallyConstant κ) (hw : ∀ z, κ z ∈ gw k j)
    (hκ : ∀ g h l, adRep (r0 η Ψ) g (κ (h, l)) - κ (g * h, l) + κ (g, h * l) - κ (g, h) = 0) :
    ∃ b : D → Matrix (Fin 3) (Fin 3) k, IsLocallyConstant b ∧ (∀ g, b g ∈ gw k j) ∧
      ∀ g h, κ (g, h) = adRep (r0 η Ψ) g (b h) - b (g * h) + b g := by
  let f : D × D → Gb (k := k) j := fun z => (⟨κ z, hw z⟩ : ↥(gw k j))
  have hfl : IsLocallyConstant f :=
    IsLocallyConstant.desc f (fun x : Gb (k := k) j => (x.val : Matrix (Fin 3) (Fin 3) k)) hc
      (fun x y hxy => Subtype.ext hxy)
  have hf : f ∈ Z2 (gRep η Ψ j) := by
    refine (mem_cocycles2 _ _).2 ⟨hfl.continuous, fun g h l => ?_⟩
    apply Subtype.ext
    exact hκ g h l
  have h0 : (Submodule.Quotient.mk ⟨f, hf⟩ : H2 (gRep η Ψ j)) = 0 := Subsingleton.elim _ _
  have hB : f ∈ B2 (gRep η Ψ j) := by
    have := (Submodule.Quotient.mk_eq_zero ((B2 (gRep η Ψ j)).comap (Z2 (gRep η Ψ j)).subtype)
      (x := ⟨f, hf⟩)).1 h0
    simpa using this
  obtain ⟨c, hcc, hd⟩ := (separated_dvr_second_cohomology_mem _ _).1 hB
  refine ⟨fun g => (c g).val, ((IsLocallyConstant.iff_continuous c).2 hcc).comp _,
    fun g => (c g).2, fun g h => ?_⟩
  have e := congrArg (fun x : Gb (k := k) j => x.val) (congrFun hd (g, h))
  rw [d1_apply] at e
  exact e.symm

theorem UpperTheory.V.UnitaryThreeInertia.lifting_obstruction_second_cohomology :
    ∀ {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [Finite R] [Group D] [TopologicalSpace D] (η : D →* ℤˣ) (Ψ : D →* Oˣ) (K : Ideal R) (j : ℤ),
      maximalIdeal R * K = ⊥ → Subsingleton (H2 (gRep η ((Units.map (residue O).toMonoidHom).comp Ψ) j)) →
      ∀ κ : D × D → Matrix (Fin 3) (Fin 3) R, IsLocallyConstant κ → (∀ z, κ z ∈ gw R j) → (∀ z, EntIn K (κ z)) →
      (∀ g h k, adRep ((GG.map (algebraMap O R)).comp (r0 η Ψ)) g (κ (h, k)) - κ (g * h, k) + κ (g, h * k) - κ (g, h) = 0) →
      ∃ b : D → Matrix (Fin 3) (Fin 3) R, IsLocallyConstant b ∧ (∀ g, b g ∈ gw R j) ∧ (∀ g, EntIn K (b g)) ∧
        ∀ g h, κ (g, h) = adRep ((GG.map (algebraMap O R)).comp (r0 η Ψ)) g (b h) - b (g * h) + b g := by
  classical
  intro O R D _ _ _ _ _ _ _ _ η Ψ K j hK hH κ hc hw hE hκ
  have memgw : ∀ (S : Type) [CommRing S] (X : Matrix (Fin 3) (Fin 3) S),
      X ∈ gw S j ↔ ∀ a b, ¬ wt a b = j → X a b = 0 := by
    intro S _ X
    unfold gw
    rfl
  have hloc : IsLocalHom (algebraMap O R) := by
    obtain ⟨_, hl, _⟩ := ‹IsCO O R›
    exact hl
  let KO : Submodule O R := K.restrictScalars O
  have hM : ∀ a ∈ maximalIdeal O, ∀ x : KO, a • x = 0 := by
    intro a ha x
    apply Subtype.ext
    have h1 : algebraMap O R a ∈ maximalIdeal R := map_nonunit (algebraMap O R) a ha
    have h2 : algebraMap O R a * (x : R) ∈ maximalIdeal R * K := Ideal.mul_mem_mul h1 x.2
    rw [hK] at h2
    simpa [Algebra.smul_def] using h2
  obtain ⟨n, p, q, hpq⟩ := UpperTheory.V.UnitaryThreeInertia.residue_coordinates_decomposition hM
  rw [UpperTheory.V.UnitaryThreeInertia.diagonal_rep_map_algebra] at hκ ⊢
  have hE' : ∀ z a b, κ z a b ∈ KO := fun z a b => hE z a b
  let κK : D × D → Fin 3 → Fin 3 → KO := fun z a b => ⟨κ z a b, hE' z a b⟩
  have hres : (Units.map (residue O).toMonoidHom).comp Ψ =
      (Units.map (algebraMap O (ResidueField O)).toMonoidHom).comp Ψ := rfl
  have key : ∀ i, ∃ b : D → Matrix (Fin 3) (Fin 3) (ResidueField O), IsLocallyConstant b ∧
      (∀ g, b g ∈ gw (ResidueField O) j) ∧ ∀ g h, Matrix.of (fun a c => p i (κK (g, h) a c)) =
        adRep (r0 η ((Units.map (residue O).toMonoidHom).comp Ψ)) g (b h) - b (g * h) + b g := by
    intro i
    refine UpperTheory.V.UnitaryThreeInertia.residual_cocycle_is_coboundary η ((Units.map (residue O).toMonoidHom).comp Ψ) j hH
      (fun z => Matrix.of (fun a c => p i (κK z a c))) ?_ ?_ ?_
    · let G : Matrix (Fin 3) (Fin 3) R → Matrix (Fin 3) (Fin 3) (ResidueField O) :=
        fun X => Matrix.of fun a c => if h : X a c ∈ KO then p i ⟨X a c, h⟩ else 0
      have hG : (fun z => Matrix.of (fun a c => p i (κK z a c))) = G ∘ κ := by
        funext z
        ext a c
        simp [G, κK, hE' z a c]
      rw [hG]
      exact hc.comp G
    · intro z
      rw [memgw]
      intro a c hac
      have h0 : κK z a c = 0 := Subtype.ext ((memgw R (κ z)).1 (hw z) a c hac)
      simp [h0]
    · intro g h l
      ext a c
      have e := congrFun (congrFun (hκ g h l) a) c
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.zero_apply, Matrix.of_apply] at e ⊢
      rw [UpperTheory.V.UnitaryThreeInertia.adjoint_diagonal_rep_apply] at e
      rw [hres, UpperTheory.V.UnitaryThreeInertia.adjoint_diagonal_rep_apply]
      have eK : ((Ψ g ^ wt a c : Oˣ) : O) • (if η g = 1 then κK (h, l) a c else -κK (h, l) c.rev a.rev) -
          κK (g * h, l) a c + κK (g, h * l) a c - κK (g, h) a c = 0 := by
        apply Subtype.ext
        split_ifs at e ⊢ <;> simpa [κK] using e
      have e2 := congrArg (p i) eK
      split_ifs at e2 ⊢ <;> simpa using e2
  choose bs hbl hbw hbe using key
  refine ⟨fun g => Matrix.of fun a c => ((∑ i, q i (bs i g a c) : KO) : R), ?_, ?_, ?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    filter_upwards [Filter.eventually_all.2 (fun i => (hbl i).eventually_eq x)] with y hy
    simp only [hy]
  · intro g
    rw [memgw]
    intro a c hac
    have h0 : ∀ i, bs i g a c = 0 := fun i => (memgw _ _).1 (hbw i g) a c hac
    simp [h0]
  · intro g
    unfold EntIn
    intro a c
    exact (∑ i, q i (bs i g a c)).2
  · intro g h
    ext a c
    have e : ∀ i, p i (κK (g, h) a c) = ((Ψ g ^ wt a c : Oˣ) : O) •
        (if η g = 1 then bs i h a c else -bs i h c.rev a.rev) - bs i (g * h) a c + bs i g a c := by
      intro i
      have e1 := congrFun (congrFun (hbe i g h) a) c
      rw [hres] at e1
      simpa only [Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, UpperTheory.V.UnitaryThreeInertia.adjoint_diagonal_rep_apply] using e1
    simp only [Matrix.sub_apply, Matrix.add_apply]
    rw [UpperTheory.V.UnitaryThreeInertia.adjoint_diagonal_rep_apply]
    simp only [Matrix.of_apply]
    have hx : κ (g, h) a c = ((κK (g, h) a c : KO) : R) := rfl
    rw [hx, ← hpq (κK (g, h) a c)]
    simp_rw [e]
    split_ifs <;> simp [map_add (f := _), map_sub, map_neg, map_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.smul_sum]
end

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section SlopeTestRemainingChoices

variable {C : Type} [CommRing C] {m : ℕ} {I M : Ideal C}

private theorem entIn_mul_left (A : Matrix (Fin m) (Fin m) C) {X : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) : EntIn I (A * X) := fun a b => by
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem_left _ (hX k b)

private theorem entIn_mul_right (A : Matrix (Fin m) (Fin m) C) {X : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) : EntIn I (X * A) := fun a b => by
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem_right _ (hX a k)

private theorem entIn_thetaLie {X : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) : EntIn I (thetaLie X) := fun a b => by
  have h : EntIn I Xᵀ := fun a b => hX b a
  exact I.neg_mem (entIn_mul_right _ (entIn_mul_left _ h) a b)

private theorem entIn_ite (s : ℤˣ) {X : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) : EntIn I (if s = 1 then X else thetaLie X) := by
  split_ifs
  · exact hX
  · exact entIn_thetaLie hX

private theorem entIn_adFun (x : GG (m := m) (R := C)) {X : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) : EntIn I (x.adFun X) :=
  entIn_mul_right _ (entIn_mul_left _ (entIn_ite _ hX))

private theorem entIn_mul_zero (hI : M * I = ⊥) {X Y : Matrix (Fin m) (Fin m) C}
    (hX : EntIn M X) (hY : EntIn I Y) : X * Y = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  have := Ideal.mul_mem_mul (hX a k) (hY k b)
  rwa [hI, Ideal.mem_bot] at this

private theorem adFun_congr (hI : M * I = ⊥) {x y : GG (m := m) (R := C)} (hr : x.right = y.right)
    (hm : EntIn M (x.mat - y.mat)) {X : Matrix (Fin m) (Fin m) C} (hX : EntIn I X) :
    x.adFun X = y.adFun X := by
  unfold GG.adFun
  rw [hr]
  have hY := entIn_ite y.right hX
  generalize (if y.right = 1 then X else thetaLie X) = Y at hY ⊢
  have h1 : x.mat * Y = y.mat * Y := by
    rw [← sub_eq_zero, ← Matrix.sub_mul]
    exact entIn_mul_zero hI hm hY
  have h2 : ((y.left⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) -
      ((x.left⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) =
      ((x.left⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) * (x.mat - y.mat) *
        ((y.left⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) := by
    simp only [GG.mat, Matrix.mul_sub, Matrix.sub_mul, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      Units.mul_inv, Matrix.mul_one]
  rw [h1, eq_comm, ← sub_eq_zero, ← Matrix.mul_sub, h2]
  exact entIn_mul_zero (by rwa [mul_comm]) (entIn_mul_left _ hY)
    (entIn_mul_right _ (entIn_mul_left _ hm))

private def onePlus (X : Matrix (Fin m) (Fin m) C) (h : X * X = 0) : GL (Fin m) C where
  val := 1 + X
  inv := 1 - X
  val_inv := by simp [Matrix.add_mul, Matrix.mul_sub, h]
  inv_val := by simp [Matrix.mul_add, Matrix.sub_mul, h]

private theorem sgnAct_one_add (hI : I * I = ⊥) (q : GL (Fin m) C)
    (X : Matrix (Fin m) (Fin m) C) (hX : EntIn I X) (hq : (q : Matrix (Fin m) (Fin m) C) = 1 + X)
    (s : ℤˣ) :
    ((sgnAct m C s q : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) =
      1 + (if s = 1 then X else thetaLie X) := by
  have h : ((-1 : ℤˣ) = 1) = False := by decide
  rcases Int.units_eq_one_or s with rfl | rfl
  · simp [hq]
  · have hinv : ((q⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) = 1 - X := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [hq, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, entIn_mul_zero hI hX hX]
      simp
    rw [sgnAct_neg_one, theta_val, hinv]
    simp only [h, if_false, thetaLie, Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, Jmat_mul_Jmat]
    rw [sub_eq_add_neg]

private structure Near (I : Ideal C) (y : GG (m := m) (R := C)) (X : Matrix (Fin m) (Fin m) C) : Prop where
  right : y.right = 1
  mat : y.mat = 1 + X
  ent : EntIn I X

private theorem act_act (s : ℤˣ) (g : GL (Fin m) C) : sgnAct m C s (sgnAct m C s g) = g := by
  rw [← MulAut.mul_apply, ← map_mul, Int.units_mul_self, map_one, MulAut.one_apply]

private theorem Near.mul_mat {y : GG (m := m) (R := C)} {X : Matrix (Fin m) (Fin m) C} (h : Near I y X) (x : GG (m := m) (R := C)) :
    (y * x).mat = (1 + X) * x.mat := by
  rw [← h.mat]
  simp [GG.mat, h.right]

private theorem Near.mul (hI : I * I = ⊥) {y y' : GG (m := m) (R := C)} {X X' : Matrix (Fin m) (Fin m) C}
    (h : Near I y X) (h' : Near I y' X') : Near I (y * y') (X + X') := by
  refine ⟨by simp [h.right, h'.right], ?_, fun a b => I.add_mem (h.ent a b) (h'.ent a b)⟩
  rw [h.mul_mat, h'.mat, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, entIn_mul_zero hI h.ent h'.ent,
    Matrix.mul_one]
  abel

private theorem Near.conj (hI : I * I = ⊥) {y : GG (m := m) (R := C)} {X : Matrix (Fin m) (Fin m) C}
    (h : Near I y X) (x : GG (m := m) (R := C)) : Near I (x * y * x⁻¹) (x.adFun X) := by
  refine ⟨by simp [h.right], ?_, entIn_adFun x h.ent⟩
  have e : (x * y * x⁻¹).left = x.left * sgnAct m C x.right y.left * x.left⁻¹ := by
    simp [h.right, act_act]
  rw [GG.mat, e, Units.val_mul, Units.val_mul, sgnAct_one_add hI _ _ h.ent h.mat, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_one, Units.mul_inv]
  rfl

private theorem Near.uniq {y : GG (m := m) (R := C)} {X X' : Matrix (Fin m) (Fin m) C}
    (h : Near I y X) (h' : Near I y X') : X = X' :=
  add_left_cancel (h.mat.symm.trans h'.mat)

private theorem Near.eq {y y' : GG (m := m) (R := C)} {X : Matrix (Fin m) (Fin m) C}
    (h : Near I y X) (h' : Near I y' X) : y = y' := by
  ext1
  · exact Units.ext (h.mat.trans h'.mat.symm)
  · rw [h.right, h'.right]

private theorem exists_near (hI : I * I = ⊥) {X : Matrix (Fin m) (Fin m) C} (hX : EntIn I X) :
    ∃ y : GG (m := m) (R := C), Near I y X :=
  ⟨⟨onePlus X (entIn_mul_zero hI hX hX), 1⟩, rfl, rfl, hX⟩

private theorem near_of {x y : GG (m := m) (R := C)} {X : Matrix (Fin m) (Fin m) C} (hX : EntIn I X)
    (hr : x.right = y.right) (hm : x.mat = (1 + X) * y.mat) : Near I (x * y⁻¹) X := by
  refine ⟨by simp [hr], ?_, hX⟩
  have e : (x * y⁻¹).left = x.left * y.left⁻¹ := by simp [hr, act_act]
  rw [GG.mat, e, Units.val_mul]
  change x.mat * _ = _
  rw [hm, GG.mat, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

end SlopeTestRemainingChoices

theorem UpperTheory.V.UnitaryThreeInertia.lt_corr :
    ∀ {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [Finite R] [Group D] [TopologicalSpace D] [IsTopologicalGroup D] (η : D →* ℤˣ) (Ψ : D →* Oˣ) (K : Ideal R) (j : ℤ),
      maximalIdeal R * K = ⊥ → K ≤ maximalIdeal R → Subsingleton (H2 (gRep η ((Units.map (residue O).toMonoidHom).comp Ψ) j)) →
      ∀ s : D → GG (m := 3) (R := R), IsLocallyConstant s → (∀ g, (s g).right = η g) →
      (∀ g, EntIn (maximalIdeal R) ((s g).mat - ((r0 η Ψ g).mat).map (algebraMap O R))) →
      (∀ g h, ∃ c ∈ gw R j, EntIn K c ∧ (s g * s h).mat = (1 + c) * (s (g * h)).mat) →
      ∃ r : D →* GG (m := 3) (R := R), IsLocallyConstant (mats r) ∧ ∀ g, (r g).right = η g ∧ ∃ b ∈ gw R j, EntIn K b ∧ (r g).mat = (1 + b) * (s g).mat := by
  intro O R D _ _ _ _ _ _ _ _ _ η Ψ K j hK hle hH s hs hη hred hc
  have hKK : K * K = ⊥ := le_bot_iff.1 (hK ▸ Ideal.mul_mono_left hle)
  choose c hcw hcK hcm using hc
  have hu : ∀ g h, Near K (s g * s h * (s (g * h))⁻¹) (c g h) := fun g h =>
    near_of (hcK g h) (by simp [hη]) (hcm g h)
  have had : ∀ g {X : Matrix (Fin 3) (Fin 3) R}, EntIn K X →
      (s g).adFun X = adRep ((GG.map (algebraMap O R)).comp (r0 η Ψ)) g X := fun g X hX =>
    adFun_congr hK (y := GG.map (algebraMap O R) (r0 η Ψ g)) (hη g) (hred g) hX
  have hlc : IsLocallyConstant fun z : D × D => c z.1 z.2 := by
    have e : (fun z : D × D => c z.1 z.2) =
        (fun w : (GG (m := 3) (R := R) × GG (m := 3) (R := R)) × GG (m := 3) (R := R) => (w.1.1 * w.1.2 * w.2⁻¹).mat - 1) ∘
          fun z : D × D => ((s z.1, s z.2), s (z.1 * z.2)) := by
      funext z
      simp only [Function.comp_apply, (hu z.1 z.2).mat, add_sub_cancel_left]
    rw [e]
    exact (((hs.comp_continuous continuous_fst).prodMk (hs.comp_continuous continuous_snd)).prodMk
      (hs.comp_continuous continuous_mul)).comp _
  obtain ⟨b, hb, hbw, hbK, hbe⟩ := lifting_obstruction_second_cohomology η Ψ K j hK hH (fun z => c z.1 z.2) hlc (fun z => hcw _ _)
    (fun z => hcK _ _) (fun g h k => by
      have h1 := (hu g h).mul hKK (hu (g * h) k)
      have h2 := ((hu h k).conj hKK (s g)).mul hKK (hu g (h * k))
      have e : s g * s h * (s (g * h))⁻¹ * (s (g * h) * s k * (s (g * h * k))⁻¹) =
          s g * (s h * s k * (s (h * k))⁻¹) * (s g)⁻¹ * (s g * s (h * k) * (s (g * (h * k)))⁻¹) := by
        rw [mul_assoc g h k]; group
      rw [e] at h1
      have h3 := h1.uniq h2
      rw [had g (hcK h k)] at h3
      dsimp only
      rw [sub_add_eq_add_sub, ← h3]
      abel)
  have hnb : ∀ g, EntIn K (-b g) := fun g a a' => K.neg_mem (hbK g a a')
  choose e he using fun g => exists_near hKK (hnb g)
  have hmul : ∀ g h, e (g * h) * s (g * h) = e g * s g * (e h * s h) := fun g h => by
    have h1 := ((he g).mul hKK ((he h).conj hKK (s g))).mul hKK (hu g h)
    have h2 : -b g + (s g).adFun (-b h) + c g h = -b (g * h) := by
      have := hbe g h
      dsimp only at this
      rw [had g (hnb h), map_neg, this]
      abel
    rw [h2] at h1
    rw [← h1.eq (he (g * h))]
    group
  refine ⟨MonoidHom.mk' (fun g => e g * s g) hmul, ?_, fun g => ⟨?_, -b g, neg_mem (hbw g), hnb g,
    (he g).mul_mat _⟩⟩
  · have e' : mats (MonoidHom.mk' (fun g => e g * s g) hmul) =
        (fun w : Matrix (Fin 3) (Fin 3) R × GG (m := 3) (R := R) => (1 + -w.1) * w.2.mat) ∘ fun g => (b g, s g) := by
      funext g
      exact (he g).mul_mat _
    rw [e']
    exact (hb.prodMk hs).comp _
  · show (e g * s g).right = η g
    simp [(he g).right, hη]
