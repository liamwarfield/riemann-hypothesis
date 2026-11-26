module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsSetLift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsGradedLiftUnitaryLocalTame
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsLiftD
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsCoordOfNotMatIrr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.NormUniq

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MapTor
noncomputable def UpperTheory.Reformulated.B.H71.wt1 :
    Fin (3 : ℕ) → ℤ :=
    fun (i : Fin (3 : ℕ)) ↦ (1 : ℤ) - (↑(↑i : ℕ) : ℤ)

theorem UpperTheory.Reformulated.B.H71.aux2.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (t : Rˣ),
      ((Matrix.diagonal fun (i : Fin (3 : ℕ)) ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i) : R)) *
          Matrix.diagonal fun (i : Fin (3 : ℕ)) ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i)⁻¹ : R)) =
        (1 : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) R) := by
  intro R _ t
  rw [Matrix.diagonal_mul_diagonal]
  simp only [Units.mul_inv, Matrix.diagonal_one]

theorem UpperTheory.Reformulated.B.H71.aux3.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (t : Rˣ),
      ((Matrix.diagonal fun (i : Fin (3 : ℕ)) ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i)⁻¹ : R)) *
          Matrix.diagonal fun (i : Fin (3 : ℕ)) ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i) : R)) =
        (1 : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) R) := by
  intro R _ t
  rw [Matrix.diagonal_mul_diagonal]
  simp only [Units.inv_mul, Matrix.diagonal_one]

noncomputable def UpperTheory.Reformulated.B.H71.torGL.{u_1} :
    {R : Type u_1} → [inst : CommRing R] → Rˣ → GL (Fin (3 : ℕ)) R :=
    fun {R : Type u_1} [CommRing R] (t : Rˣ) ↦
      { val := Matrix.diagonal fun (i : Fin (3 : ℕ)) ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i) : R),
        inv := Matrix.diagonal fun (i : Fin (3 : ℕ)) ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i)⁻¹ : R),
        val_inv := UpperTheory.Reformulated.B.H71.aux2 t, inv_val := UpperTheory.Reformulated.B.H71.aux3 t : (Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) R)ˣ }

theorem UpperTheory.Reformulated.B.H71.aux5.{u_1} :
    ∀ (R : Type u_1) [inst : CommRing R], UpperTheory.Reformulated.B.H71.torGL (1 : Rˣ) = (1 : GL (Fin (3 : ℕ)) R) := by
  intro R _
  apply Units.ext
  change Matrix.diagonal (fun i : Fin 3 ↦ (↑((1 : Rˣ) ^ UpperTheory.Reformulated.B.H71.wt1 i) : R)) = 1
  simp only [one_zpow, Units.val_one, Matrix.diagonal_one]

theorem UpperTheory.Reformulated.B.H71.aux6.{u_1} :
    ∀ (R : Type u_1) [inst : CommRing R] (s t : Rˣ),
      UpperTheory.Reformulated.B.H71.torGL (s * t) = UpperTheory.Reformulated.B.H71.torGL s * UpperTheory.Reformulated.B.H71.torGL t := by
  intro R _ s t
  apply Units.ext
  change Matrix.diagonal (fun i : Fin 3 ↦ (↑((s * t) ^ UpperTheory.Reformulated.B.H71.wt1 i) : R)) =
    Matrix.diagonal (fun i : Fin 3 ↦ (↑(s ^ UpperTheory.Reformulated.B.H71.wt1 i) : R)) *
      Matrix.diagonal (fun i : Fin 3 ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i) : R))
  rw [Matrix.diagonal_mul_diagonal]
  simp only [mul_zpow, Units.val_mul]

noncomputable def UpperTheory.Reformulated.B.H71.tor.{u_1} :
    (R : Type u_1) → [inst : CommRing R] → Rˣ →* GL (Fin (3 : ℕ)) R :=
    fun (R : Type u_1) [CommRing R] ↦
      { toFun := UpperTheory.Reformulated.B.H71.torGL, map_one' := UpperTheory.Reformulated.B.H71.aux5 R, map_mul' := UpperTheory.Reformulated.B.H71.aux6 R :
        Rˣ →* GL (Fin (3 : ℕ)) R }

theorem UpperTheory.Reformulated.B.H71.map_tor :
    ∀ {A B : Type} [inst : CommRing A] [inst_1 : CommRing B] (f : A →+* B) (t : Aˣ),
      (Matrix.GeneralLinearGroup.map f : GL (Fin (3 : ℕ)) A → GL (Fin (3 : ℕ)) B)
          ((UpperTheory.Reformulated.B.H71.tor A : Aˣ → GL (Fin (3 : ℕ)) A) t) =
        (UpperTheory.Reformulated.B.H71.tor B : Bˣ → GL (Fin (3 : ℕ)) B) ((Units.map (↑f : A →* B) : Aˣ → Bˣ) t) := by
  intro A B _ _ f t
  apply Units.ext
  change (Matrix.diagonal (fun i : Fin 3 ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i) : A))).map f =
    Matrix.diagonal (fun i : Fin 3 ↦ (↑((Units.map (f : A →* B) t) ^ UpperTheory.Reformulated.B.H71.wt1 i) : B))
  rw [Matrix.diagonal_map (map_zero f)]
  congr 1
  funext i
  rw [← map_zpow, Units.coe_map]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LiftAlongSurjectionGraded
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem map_tor {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (t : Aˣ) :
    GeneralLinearGroup.map f (tor A t) = tor B (Units.map f.toMonoidHom t) :=
  _root_.UpperTheory.Reformulated.B.H71.map_tor f t

private theorem map_conjBy {A B D : Type} [CommRing A] [CommRing B] [Group D] (f : A →+* B) (h : GL (Fin 3) A)
    (r : D →* GG (m := 3) (R := A)) :
    (GG.map f).comp (conjBy h r) = conjBy (GeneralLinearGroup.map f h) ((GG.map f).comp r) := by
  have e : GG.map f (GG.ofGL h) = GG.ofGL (GeneralLinearGroup.map f h) := by
    unfold GG.map
    rw [SemidirectProduct.map_inl]
  refine MonoidHom.ext fun g => ?_
  simp only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, e]

private theorem conj_conj {A D : Type} [CommRing A] [Group D] (h h' : GL (Fin 3) A)
    (r : D →* GG (m := 3) (R := A)) :
    conjBy (h * h') r = conjBy h (conjBy h' r) := by
  ext1 g
  simp only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
    _root_.mul_inv_rev, mul_assoc, MulAut.mul_apply]

private theorem conj_one {A D : Type} [CommRing A] [Group D]
    (r : D →* GG (m := 3) (R := A)) : conjBy 1 r = r := by
  ext1 g
  simp [conjBy]

private theorem conj_mat {A D : Type} [CommRing A] [Group D] (h : GL (Fin 3) A)
    (r : D →* GG (m := 3) (R := A)) (g : D) :
    (conjBy h r g).mat = (h : Matrix _ _ A) * (r g).mat *
      ((sgnAct 3 A (r g).right h⁻¹ : GL (Fin 3) A) : Matrix _ _ A) := by
  have : (conjBy h r g).left = h * (r g).left * sgnAct 3 A (r g).right h⁻¹ := by
    simp [conjBy, SemidirectProduct.mul_left, SemidirectProduct.inv_left]
  simp only [GG.mat, this, Units.val_mul]

private theorem setup {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group Γ] [TopologicalSpace Γ] (F : Frame O G Γ ι) (hF : F.Ok) (g₁ : Γ)
    (hg : F.Marked g₁) {R : Type} [CommRing R] [Algebra O R] [IsLocalRing R]
    (r : Γ →* GG (m := 3) (R := R))
    (hr : Red F.η F.Ψ r) :
    ∃ Ψ : Γ →* (ResidueField R)ˣ, IsUnit (2 : R) ∧ Marks F.η Ψ F.c g₁ ∧
      (GG.map (residue R)).comp r = r0 F.η Ψ := by
  refine ⟨(Units.map ((residue R).comp (algebraMap O R)).toMonoidHom).comp F.Ψ, ?_,
    ⟨hF.csq, hF.ηc, by simp [hF.Ψc], hg.1, ?_⟩, ?_⟩
  · simpa [map_ofNat] using hF.two.map (algebraMap O R)
  · simpa using hg.2.map ((residue R).comp (algebraMap O R))
  · refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) (hr.mult g)
    rw [unitaryThreeReflection_left, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_tor]
    ext a b
    exact Ideal.Quotient.eq.2 (hr.red g a b)

theorem UpperTheory.lift_along_surjection_graded :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [TopologicalSpace G]
      [IsTopologicalGroup G] [Group Γ] [TopologicalSpace Γ] (F : Frame O G Γ ι),
      F.Ok → ∀ g₁, F.Marked g₁ → ∀ {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
        [CommRing R'] [Algebra O R'] [IsCO O R'] (q : R →ₐ[O] R'), Function.Surjective q →
      ∀ (r : Γ →* GG (m := 3) (R := R)) (r' : Γ →* GG (m := 3) (R := R')),
        F.Cond r → IsLocallyConstant (mats r) → push q r = r' → F.CondN g₁ r' →
        ∃ r₂ : Γ →* GG (m := 3) (R := R), F.IsPt g₁ r₂ ∧ push q r₂ = r' := by
  intro O _ _ G Γ ι _ _ _ _ _ F hF g₁ hg R R' _ _ _ _ _ _ q hq r r' hr hlc hp hr'
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  have hm : ∀ x : R, q x ∈ maximalIdeal R' ↔ x ∈ maximalIdeal R := fun x => by
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
  have hent : ∀ (h : GL (Fin 3) R), InHat (GeneralLinearGroup.map (q : R →+* R') h) ↔ InHat h := fun h => by
    refine forall_congr' fun a => forall_congr' fun b => ?_
    rw [← hm]
    refine iff_of_eq (congrArg (· ∈ maximalIdeal R') ?_)
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  obtain ⟨Ψ, h2, hM, hred⟩ := setup F hF g₁ hg r hr.toRed
  obtain ⟨Ψ', h2', hM', hred'⟩ := setup F hF g₁ hg r' hr'.toRed
  obtain ⟨h, hh, hN⟩ := exists_normalised F.η Ψ F.c g₁ r h2 hM hred
  have hpush : ∀ H : GL (Fin 3) R, push q (conjBy H r) =
      conjBy (GeneralLinearGroup.map (q : R →+* R') H) r' := fun H => by
    rw [← hp]; exact map_conjBy _ _ _
  have hN' : Normalised F.c g₁ (conjBy (GeneralLinearGroup.map (q : R →+* R') h) r') := by
    rw [← hpush]
    refine ⟨?_, ?_, ?_⟩
    · rw [MonoidHom.comp_apply, GG.map_mat, hN.atc, Matrix.map_one _ (map_zero _) (map_one _)]
    · have := congrArg q hN.z12
      simpa [zmat] using this
    · have := congrArg q hN.z21
      simpa [zmat] using this
  obtain ⟨t', -, ht'⟩ := normalised_unique F.η Ψ' F.c g₁ r' _ h2' hM' hred' ((hent h).2 hh) hr'.norm hN'
  obtain ⟨t₀, ht₀⟩ := hq t'
  obtain ⟨t, rfl⟩ : IsUnit t₀ := by
    by_contra hn
    have := (hm t₀).2 hn
    rw [ht₀] at this
    exact this t'.isUnit
  have ht : Units.map (q : R →+* R').toMonoidHom t = t' := Units.ext ht₀
  have hH : GeneralLinearGroup.map (q : R →+* R') (tor R t⁻¹ * h) = 1 := by
    rw [map_mul, ht', map_tor, map_inv, ht, map_inv, inv_mul_cancel]
  have hHhat : InHat (tor R t⁻¹ * h) := by
    rw [← hent, hH]
    intro a b
    simp
  refine ⟨conjBy (tor R t⁻¹ * h) r, ⟨⟨(cond_conj F _ hHhat).2 r hr, ?_⟩, fun n => ?_⟩, ?_⟩
  · rw [conj_conj]
    exact (conjBy_tor _ _).2.2.1 _ _ hN
  · generalize tor R t⁻¹ * h = H
    have := (hlc.prodMk hF.η_cont).comp fun p : Matrix (Fin 3) (Fin 3) R × ℤˣ =>
      ((H : Matrix _ _ R) * p.1 * ((sgnAct 3 R p.2 H⁻¹ : GL (Fin 3) R) : Matrix _ _ R)).map
        (Ideal.Quotient.mk (maximalIdeal R ^ n))
    convert this using 1
    funext g
    rw [conj_mat, hr.mult g]
    rfl
  · rw [hpush, hH, conj_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CardDualResidueFieldEqCardOfMaximalIdealSmulEqZe
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.card_dual_residueField_eq_card_of_maximalIdeal_smul_eq_zero :
    ∀ {O N : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [AddCommGroup N] [Module O N] [Finite N], (∀ a ∈ maximalIdeal O, ∀ x : N, a • x = 0) → Nat.card (N →ₗ[O] ResidueField O) = Nat.card N := by
  intro O N _ _ _ _ _ _ h
  classical
  have hM : Module.IsTorsionBySet O N (maximalIdeal O) := fun x a => h a a.2 x
  letI : Module (ResidueField O) N := hM.module
  haveI : IsScalarTower O (ResidueField O) N := hM.isScalarTower
  have e := LinearMap.extendScalarsOfSurjectiveEquiv (R := O) (S := ResidueField O) (M := N)
    (N := ResidueField O) IsLocalRing.residue_surjective
  rw [Nat.card_congr e.toEquiv]
  let b := Module.Free.chooseBasis (ResidueField O) N
  exact (Nat.card_congr b.toDualEquiv.toEquiv).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsSmallExtensionFactorizationOfFunctional
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem isCO_of_surj {O : Type} [CommRing O] [IsLocalRing O] {R S : Type} [CommRing R] [Algebra O R]
    [IsCO O R] [Finite R] [CommRing S] [Algebra O S] [Nontrivial S] (f : R →ₐ[O] S)
    (hf : Function.Surjective f) :
    ∃ _ : IsCO O S, ∀ x : R, f x ∈ maximalIdeal S ↔ x ∈ maximalIdeal R := by
  haveI : IsLocalRing S := IsLocalRing.of_surjective' (f : R →+* S) hf
  haveI : Finite S := Finite.of_surjective f hf
  haveI hl : IsLocalHom (f : R →+* S) := IsLocalHom.of_surjective (f : R →+* S) hf
  have hm : ∀ x : R, f x ∈ maximalIdeal S ↔ x ∈ maximalIdeal R := fun x =>
    ⟨fun h hu => h (hu.map f), fun h hu => h (hl.map_nonunit x hu)⟩
  haveI : IsArtinianRing S := inferInstance
  refine ⟨{ complete := inferInstance, isLocalHom := ⟨fun a ha => ?_⟩, res_surj := fun y => ?_ }, hm⟩
  · rw [← f.commutes] at ha
    exact IsLocalHom.map_nonunit (f := algebraMap O R) a (hl.map_nonunit _ ha)
  · obtain ⟨x, rfl⟩ := hf y
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
    refine ⟨a, ?_⟩
    rw [← f.commutes, ← map_sub]
    exact (hm _).2 ha

theorem UpperTheory.exists_small_extension_factorization_of_functional :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [Finite R] [CommRing R'] [Algebra O R'] (p : R →ₐ[O] R'), maximalIdeal R * RingHom.ker p = ⊥ → RingHom.ker p ≤ maximalIdeal R → ∀ φ : RingHom.ker p →ₗ[O] ResidueField O, φ ≠ 0 →
     ∃ (R'' : Type) (_ : CommRing R'') (_ : Algebra O R'') (_ : IsCO O R'') (p₁ : R →ₐ[O] R'') (q : R'' →ₐ[O] R') (ε : ResidueField O →ₗ[O] R''), Function.Surjective p₁ ∧ q.comp p₁ = p ∧ ¬ Function.Injective q ∧ (∀ x : RingHom.ker p, p₁ x = ε (φ x)) ∧ (∀ y, q (ε y) = 0) ∧ (∀ y, ε y ∈ maximalIdeal R'') ∧ ∀ x ∈ maximalIdeal R'', ∀ y, x * ε y = 0 := by
  intro O _ _ R R' _ _ _ _ _ _ p hmul hle φ hφ
  have hz : ∀ m ∈ maximalIdeal R, ∀ x ∈ RingHom.ker p, m * x = 0 := fun m hm x hx => by
    have := Ideal.mul_mem_mul hm hx
    rwa [hmul, Ideal.mem_bot] at this
  let J : Ideal R :=
    { carrier := {x | ∃ h : x ∈ RingHom.ker p, φ ⟨x, h⟩ = 0}
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨add_mem ha hb, ?_⟩
        have : (⟨a + b, add_mem ha hb⟩ : RingHom.ker p) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
        rw [this, map_add (f := _), ha', hb', add_zero]
      zero_mem' := ⟨zero_mem _, map_zero φ⟩
      smul_mem' := by
        rintro r x ⟨hx, hx'⟩
        refine ⟨Ideal.mul_mem_left _ r hx, ?_⟩
        obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) r
        have : (⟨r • x, Ideal.mul_mem_left _ r hx⟩ : RingHom.ker p) = a • ⟨x, hx⟩ := by
          apply Subtype.ext
          have h := hz _ ha x hx
          rw [sub_mul, sub_eq_zero] at h
          show r * x = a • x
          rw [h, Algebra.smul_def]
        rw [this, map_smul, hx', smul_zero] }
  have hJ : ∀ x : RingHom.ker p, (x : R) ∈ J ↔ φ x = 0 := fun x =>
    ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩
  have hJp : ∀ x ∈ J, p x = 0 := fun x ⟨h, _⟩ => h
  obtain ⟨x0, hx0⟩ : ∃ x, φ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (LinearMap.ext h)
  have hsurj : Function.Surjective φ := fun y => by
    obtain ⟨a, ha⟩ := residue_surjective (y * (φ x0)⁻¹)
    refine ⟨a • x0, ?_⟩
    rw [map_smul, Algebra.smul_def, ResidueField.algebraMap_eq, ha, inv_mul_cancel_right₀ hx0]
  have hJtop : J ≠ ⊤ := fun h => hx0 ((hJ x0).1 (h ▸ Submodule.mem_top))
  haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJtop
  have hp1 : Function.Surjective (Ideal.Quotient.mkₐ O J) := Ideal.Quotient.mkₐ_surjective O J
  obtain ⟨inst, hm⟩ := isCO_of_surj (Ideal.Quotient.mkₐ O J) hp1
  let ψ : RingHom.ker p →ₗ[O] R ⧸ J :=
    (Ideal.Quotient.mkₐ O J).toLinearMap ∘ₗ ((RingHom.ker p).subtype.restrictScalars O)
  have hψ : ∀ x : RingHom.ker p, ψ x = Ideal.Quotient.mkₐ O J x := fun _ => rfl
  have hker : LinearMap.ker φ ≤ LinearMap.ker ψ := fun x hx =>
    Ideal.Quotient.eq_zero_iff_mem.2 ((hJ x).2 hx)
  let ε : ResidueField O →ₗ[O] R ⧸ J :=
    (LinearMap.ker φ).liftQ ψ hker ∘ₗ (φ.quotKerEquivOfSurjective hsurj).symm.toLinearMap
  have hε : ∀ x : RingHom.ker p, ε (φ x) = Ideal.Quotient.mkₐ O J x := fun x => by
    have : (φ.quotKerEquivOfSurjective hsurj).symm (φ x) = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    show (LinearMap.ker φ).liftQ ψ hker ((φ.quotKerEquivOfSurjective hsurj).symm (φ x)) = _
    rw [this, Submodule.liftQ_apply, hψ]
  have hq : ∀ x : R, Ideal.Quotient.liftₐ J p hJp (Ideal.Quotient.mkₐ O J x) = p x := fun _ => rfl
  refine ⟨R ⧸ J, inferInstance, inferInstance, inst, Ideal.Quotient.mkₐ O J, Ideal.Quotient.liftₐ J p hJp, ε,
    hp1, AlgHom.ext hq, fun hinj => ?_, fun x => (hε x).symm, fun y => ?_, fun y => ?_, fun x hx y => ?_⟩
  · have h : Ideal.Quotient.mkₐ O J (x0 : R) = 0 := hinj (by rw [hq, map_zero]; exact x0.2)
    exact hx0 ((hJ x0).1 (Ideal.Quotient.eq_zero_iff_mem.1 h))
  · obtain ⟨x, rfl⟩ := hsurj y
    rw [hε, hq]; exact x.2
  · obtain ⟨x, rfl⟩ := hsurj y
    rw [hε]; exact (hm _).2 (hle x.2)
  · obtain ⟨z, rfl⟩ := hsurj y
    obtain ⟨w, rfl⟩ := hp1 x
    rw [hε, ← map_mul, hz w ((hm w).1 hx) _ z.2, map_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsLiftU
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem lu_section {G A : Type} [Group G] [Finite G] [Group A] (g : G →* A) (hg : Function.Surjective g)
    (hc : Nat.Coprime (Nat.card g.ker) (Nat.card A)) : ∃ σ : A →* G, ∀ a, g (σ a) = a := by
  have hi : g.ker.index = Nat.card A := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hg, Subgroup.card_top]
  obtain ⟨C, hC⟩ := Subgroup.exists_right_complement'_of_coprime (N := g.ker) (by rwa [hi])
  have hb : Function.Bijective (g.comp C.subtype) := by
    constructor
    · rw [injective_iff_map_eq_one]
      intro c hc
      have : (c : G) ∈ g.ker ⊓ C := ⟨hc, c.2⟩
      rw [hC.disjoint.eq_bot] at this
      exact Subtype.ext this
    · intro a
      obtain ⟨x, rfl⟩ := hg a
      obtain ⟨⟨k, c⟩, rfl⟩ := hC.2 x
      refine ⟨c, ?_⟩
      have hk : g k = 1 := k.2
      simp [hk]
  exact ⟨C.subtype.comp (MulEquiv.ofBijective _ hb).symm.toMonoidHom,
    fun a => (MulEquiv.ofBijective _ hb).apply_symm_apply a⟩

private theorem lu_conj {H H' A : Type} [Group H] [Finite H] [Group H'] [Group A] [Finite A] (f : H →* H')
    (hK : ∀ a b, f a = 1 → f b = 1 → a * b = b * a) (hc : Nat.Coprime (Nat.card f.ker) (Nat.card A))
    (σ τ : A →* H) (h : ∀ a, f (σ a) = f (τ a)) : ∃ k, f k = 1 ∧ ∀ a, τ a = k * σ a * k⁻¹ := by
  classical
  letI := Fintype.ofFinite A
  letI : CommGroup f.ker := { (inferInstance : Group f.ker) with
    mul_comm := fun a b => Subtype.ext (hK _ _ a.2 b.2) }
  let c : A → f.ker := fun a => ⟨τ a * (σ a)⁻¹, by simp [h a]⟩
  let act : A → f.ker →* f.ker := fun a => (MulAut.conjNormal (σ a) : MulAut f.ker).toMonoidHom
  have hact : ∀ a (k : f.ker), (act a k : H) = σ a * k * (σ a)⁻¹ := fun a k => rfl
  have hcoc : ∀ a b, c (a * b) = c a * act a (c b) := fun a b => by
    apply Subtype.ext
    rw [Subgroup.coe_mul, hact]
    simp [c, mul_assoc]
  have hbij := (powCoprime hc).bijective
  obtain ⟨k, hk⟩ := hbij.2 (∏ b, c b)
  rw [powCoprime_apply] at hk
  refine ⟨k, k.2, fun a => ?_⟩
  have h1 : ∏ b, c b = c a ^ Nat.card A * act a (∏ b, c b) := by
    refine (Equiv.prod_comp (Equiv.mulLeft a) c).symm.trans ?_
    simp only [Equiv.coe_mulLeft, hcoc, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Nat.card_eq_fintype_card, map_prod]
  have h2 : k = c a * act a k := by
    apply hbij.1
    rw [powCoprime_apply, powCoprime_apply, mul_pow, ← map_pow, hk]
    exact h1
  have h3 := congrArg Subtype.val h2
  rw [Subgroup.coe_mul, hact] at h3
  simp only [c] at h3
  calc τ a = (τ a * (σ a)⁻¹ * (σ a * k * (σ a)⁻¹)) * σ a * (k : H)⁻¹ := by group
    _ = _ := by rw [← h3]

private theorem lu_abs {D H H' : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [Group H] [Finite H]
    [Group H'] (f : H →* H') (hK : ∀ a b, f a = 1 → f b = 1 → a * b = b * a) (l e : ℕ) (hl : l.Prime)
    (hle : ¬ l ∣ e) (hKl : ∀ a, f a = 1 → a ^ l = 1) (I : Subgroup D) (hI : I.Normal) (φ : D)
    (hφ : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (hd : ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1)
    (r' : D →* H') (hlc : IsLocallyConstant r') (hs : ∀ g, ∃ h, f h = r' g) (he : ∀ s ∈ I, r' s ^ e = 1) :
    ∃ r : D →* H, (∀ g, f (r g) = r' g) ∧ IsLocallyConstant r ∧ ∀ s ∈ I, r' s = 1 → r s = 1 := by
  haveI := Fact.mk hl
  let A : Subgroup H' := I.map r'
  have hsurj : Function.Surjective (f.subgroupComap A) := by
    rintro ⟨_, s, hsI, rfl⟩
    obtain ⟨h, hh⟩ := hs s
    exact ⟨⟨h, show f h ∈ A from hh ▸ ⟨s, hsI, rfl⟩⟩, Subtype.ext hh⟩
  haveI : Finite A := Finite.of_surjective _ hsurj
  have hA : Nat.Coprime l (Nat.card A) := by
    rw [hl.coprime_iff_not_dvd]
    intro hdv
    obtain ⟨⟨_, s, hsI, rfl⟩, ha⟩ := exists_prime_orderOf_dvd_card' l hdv
    exact hle (ha ▸ orderOf_dvd_of_pow_eq_one (Subtype.ext (he s hsI)))
  have hP : ∀ {G : Type} [Group G] [Finite G], (∀ a : G, a ^ l = 1) → Nat.Coprime (Nat.card G) (Nat.card A) := by
    intro G _ _ hG
    have : IsPGroup l G := fun a => ⟨1, by simpa using hG a⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 this
    rw [hn]
    exact Nat.Coprime.pow_left n hA
  obtain ⟨σ₀, hσ₀⟩ := lu_section (f.subgroupComap A) hsurj (hP fun a =>
    Subtype.ext (Subtype.ext (hKl _ (congrArg Subtype.val a.2))))
  let σ : A →* H := (Subgroup.subtype _).comp σ₀
  have hσ : ∀ a, f (σ a) = a := fun a => congrArg Subtype.val (hσ₀ a)
  have hn : ∀ g : D, ∀ a : A, (r' g)⁻¹ * a * r' g ∈ A := by
    rintro g ⟨_, s, hsI, rfl⟩
    exact ⟨g⁻¹ * s * g, hI.conj_mem' s hsI g, by simp⟩
  let cj : D → A →* A := fun g =>
    { toFun := fun a => ⟨_, hn g a⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hcj : ∀ g a, (cj g a : H') = (r' g)⁻¹ * a * r' g := fun _ _ => rfl
  obtain ⟨x₀, hx₀⟩ := hs φ
  obtain ⟨k, hk, hkc⟩ := lu_conj f hK (hP fun a => Subtype.ext (hKl _ a.2)) σ
    ((MulAut.conj x₀).toMonoidHom.comp (σ.comp (cj φ))) (fun a => by simp [hσ, hcj, hx₀, mul_assoc])
  set x := k⁻¹ * x₀ with hxdef
  have hx : f x = r' φ := by simp [hxdef, hk, hx₀]
  have hxa : ∀ a, x * σ (cj φ a) * x⁻¹ = σ a := fun a => by
    have := hkc a
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    calc x * σ (cj φ a) * x⁻¹ = k⁻¹ * (x₀ * σ (cj φ a) * x₀⁻¹) * k := by rw [hxdef]; group
      _ = σ a := by rw [this]; group
  have hnorm : x ∈ Subgroup.normalizer (σ.range : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨cj φ⁻¹ a, ?_⟩
      rw [← hxa]
      congr 3
      exact Subtype.ext (by simp [hcj, mul_assoc])
    · rintro ⟨a, ha⟩
      refine ⟨cj φ a, ?_⟩
      rw [← hxa] at ha
      simpa using ha
  have hz : ∀ (m : ℤ) (t : H), t ∈ σ.range → x ^ m * t * (x ^ m)⁻¹ ∈ σ.range := fun m t ht =>
    (Subgroup.mem_normalizer_iff.1 (Subgroup.zpow_mem _ hnorm m) t).1 ht
  obtain ⟨d, hdl, hdI, hdφ⟩ := hd (orderOf x) (orderOf_pos x)
  let L : Subgroup (H × Multiplicative (ZMod (orderOf x))) :=
    { carrier := {z | ∃ m : ℤ, z.1 * (x ^ m)⁻¹ ∈ σ.range ∧ z.2 = Multiplicative.ofAdd (m : ZMod (orderOf x))}
      one_mem' := ⟨0, by simp, by simp⟩
      mul_mem' := by
        rintro z w ⟨m, h1, h2⟩ ⟨m', h1', h2'⟩
        refine ⟨m + m', ?_, by simp [h2, h2', ofAdd_add]⟩
        have := mul_mem h1 (hz m _ h1')
        convert this using 1
        simp only [Prod.fst_mul]; group
      inv_mem' := by
        rintro z ⟨m, h1, h2⟩
        refine ⟨-m, ?_, by simp [h2]⟩
        have := hz (-m) _ (inv_mem h1)
        convert this using 1
        simp only [Prod.fst_inv]; group }
  let Φ : L →* H' × Multiplicative (ZMod (orderOf x)) := (f.prodMap (MonoidHom.id _)).comp L.subtype
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨z, u⟩, m, ⟨a, ha⟩, h2⟩ h
    have e1 : f z = 1 := congrArg Prod.fst h
    have e2 : u = 1 := congrArg Prod.snd h
    have e3 : x ^ m = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp only [e2] at h2
      exact (ofAdd_eq_one.1 h2.symm)
    simp only [e3, inv_one, mul_one] at ha
    have e4 : a = 1 := Subtype.ext (by rw [← hσ, ha, e1]; rfl)
    have e5 : z = 1 := by rw [← ha, e4, map_one]
    exact Subtype.ext (Prod.ext e5 e2)
  have hlc2 : IsLocallyConstant (r'.prod d) := hlc.prodMk hdl
  have hr : ∀ g, (r'.prod d) g ∈ Φ.range := by
    have hcl : IsClosed ((Φ.range.comap (r'.prod d) : Subgroup D) : Set D) :=
      ⟨hlc2 ((Φ.range : Set (H' × Multiplicative (ZMod (orderOf x))))ᶜ)⟩
    have hle : I ⊔ Subgroup.zpowers φ ≤ Φ.range.comap (r'.prod d) := by
      refine sup_le (fun s hsI => ?_) ((Subgroup.zpowers_le).2 ?_)
      · exact ⟨⟨(σ ⟨_, s, hsI, rfl⟩, 1), 0, by simp, by simp⟩, Prod.ext (hσ _) (hdI s hsI).symm⟩
      · exact ⟨⟨(x, Multiplicative.ofAdd 1), 1, by simp, by simp⟩, Prod.ext hx hdφ.symm⟩
    intro g
    have := Subgroup.topologicalClosure_minimal _ hle hcl
    rw [hφ] at this
    exact this (Subgroup.mem_top g)
  let ρ : D →* L := (MonoidHom.ofInjective hΦ).symm.toMonoidHom.comp ((r'.prod d).codRestrict _ hr)
  have hρ : ∀ g, Φ (ρ g) = (r'.prod d) g := fun g => MonoidHom.apply_ofInjective_symm hΦ _
  refine ⟨(MonoidHom.fst _ _).comp (L.subtype.comp ρ), fun g => congrArg Prod.fst (hρ g), ?_, fun s hsI h1 => ?_⟩
  · have : IsLocallyConstant ρ := IsLocallyConstant.desc ρ Φ (by
      have : Φ ∘ ρ = r'.prod d := funext hρ
      rw [this]; exact hlc2) hΦ
    exact this.comp fun z : L => z.1.1
  · have : ρ s = 1 := hΦ (by rw [hρ, map_one]; exact Prod.ext h1 (hdI s hsI))
    simp [this]

private theorem lu_inv_mem {M : Type} [Group M] [Finite M] (S : Submonoid M) {x : M} (hx : x ∈ S) : x⁻¹ ∈ S := by
  have : x⁻¹ = x ^ (orderOf x - 1) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
  rw [this]
  exact pow_mem hx _

private theorem lu_sub {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [Finite R]
    (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] : ∃ S : Subgroup (GG (m := 3) (R := R)), ∀ x, x ∈ S ↔ GrMat 𝒜 x.mat := by
  have h1 : GrMat 𝒜 (1 : Matrix (Fin 3) (Fin 3) R) := fun a b => by
    by_cases h : a = b
    · subst h
      simp only [wt, sub_self, Matrix.one_apply_eq]
      exact SetLike.GradedOne.one_mem
    · simp [Matrix.one_apply_ne h]
  have hm : ∀ X Y : Matrix (Fin 3) (Fin 3) R, GrMat 𝒜 X → GrMat 𝒜 Y → GrMat 𝒜 (X * Y) := fun X Y hX hY a b => by
    rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ fun c _ => ?_
    have := SetLike.GradedMul.mul_mem (hX a c) (hY c b)
    rwa [show wt a c + wt c b = wt a b by simp [wt]] at this
  let S₀ : Submonoid (GL (Fin 3) R) :=
    { carrier := {x | GrMat 𝒜 (x : Matrix (Fin 3) (Fin 3) R)}
      one_mem' := h1
      mul_mem' := fun ha hb => hm _ _ ha hb }
  have hθ : ∀ g : GL (Fin 3) R, g ∈ S₀ → theta g ∈ S₀ := fun g hg a b => by
    have hi : GrMat 𝒜 ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := lu_inv_mem S₀ hg
    rw [theta_val]
    generalize ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = X at hi
    have e : (Jmat (R := R) 3 * Xᵀ * Jmat (R := R) 3) a b = X b.rev a.rev := by
      fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]
    have e' : wt b.rev a.rev = wt a b := by fin_cases a <;> fin_cases b <;> rfl
    rw [e, ← e']
    exact hi _ _
  let S₁ : Submonoid (GG (m := 3) (R := R)) :=
    { carrier := {x | x.left ∈ S₀}
      one_mem' := S₀.one_mem
      mul_mem' := fun {x y} hx hy => by
        show x.left * sgnAct (m := 3) (R := R) x.right y.left ∈ S₀
        refine mul_mem hx ?_
        rcases Int.units_eq_one_or x.right with h | h <;> rw [h]
        · rw [sgnAct_one]; exact hy
        · rw [sgnAct_neg_one]; exact hθ _ hy }
  haveI : Finite (GG (m := 3) (R := R)) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  exact ⟨{ S₁ with inv_mem' := fun hx => lu_inv_mem S₁ hx }, fun _ => Iff.rfl⟩

private theorem lu_ker {R R' : Type} [CommRing R] [CommRing R'] (p : R →+* R')
    (hp : ∀ x y, p x = 0 → p y = 0 → x * y = 0) (l : ℕ) (hl : ∀ x, p x = 0 → (l : R) * x = 0) :
    (∀ a b : GG (m := 3) (R := R), GG.map p a = 1 → GG.map p b = 1 → a * b = b * a) ∧
      ∀ a : GG (m := 3) (R := R), GG.map p a = 1 → a ^ l = 1 := by
  have hk : ∀ a : GG (m := 3) (R := R), GG.map p a = 1 → ∃ u : GL (Fin 3) R, a = GG.ofGL u ∧
      ∃ X : Matrix (Fin 3) (Fin 3) R, (u : Matrix (Fin 3) (Fin 3) R) = 1 + X ∧ ∀ i j, p (X i j) = 0 := by
    intro a ha
    have h1 : a.right = 1 := congrArg SemidirectProduct.right ha
    have h2 : a.mat.map p = 1 := congrArg GG.mat ha
    refine ⟨a.left, SemidirectProduct.ext rfl h1, a.mat - 1, by simp [GG.mat], fun i j => ?_⟩
    have := congrFun (congrFun h2 i) j
    rw [Matrix.map_apply] at this
    rw [Matrix.sub_apply, map_sub, this]
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hz : ∀ X Y : Matrix (Fin 3) (Fin 3) R, (∀ i j, p (X i j) = 0) → (∀ i j, p (Y i j) = 0) → X * Y = 0 :=
    fun X Y hX hY => by
      ext i j
      rw [Matrix.mul_apply]
      exact Finset.sum_eq_zero fun c _ => hp _ _ (hX _ _) (hY _ _)
  constructor
  · intro a b ha hb
    obtain ⟨u, rfl, X, hu, hX⟩ := hk a ha
    obtain ⟨w, rfl, Y, hw, hY⟩ := hk b hb
    rw [← map_mul, ← map_mul]
    congr 1
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hu, hw]
    simp only [add_mul, mul_add, hz X Y hX hY, hz Y X hY hX, one_mul, mul_one]
    abel
  · intro a ha
    obtain ⟨u, rfl, X, hu, hX⟩ := hk a ha
    have hn : ∀ n : ℕ, (1 + X) ^ n = 1 + (n : R) • X := fun n => by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, ih]
        simp only [add_mul, mul_add, smul_mul_assoc, hz X X hX hX, one_mul, mul_one, smul_zero, Nat.cast_succ,
          add_smul, one_smul]
        abel
    have : u ^ l = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hu, hn, Units.val_one, add_eq_left]
      ext i j
      exact hl _ (hX i j)
    rw [← map_pow, this, map_one]

theorem UpperTheory.V.UnitaryThreeInertia.exists_lift_u :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.LocVan → ∀ {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (p : R →ₐ[O] R') (j : ℤ), Function.Surjective p → SmallExt O 𝒜 (RingHom.ker p) j →
    ∀ (v : ι), v ∉ F.Tb → ∀ (r' : F.D v →* GG (m := 3) (R := R')), Red (F.ηv v) (F.Ψv v) r' → F.LocAt v r' → IsLocallyConstant (mats r') →
      (∀ g, ∃ X, GrMat 𝒜 X ∧ X.map p = (r' g).mat) →
      ∃ r : F.D v →* GG (m := 3) (R := R), UnitaryThreeInertia.push p r = r' ∧ F.LocAt v r ∧ IsLocallyConstant (mats r) ∧ ∀ g, GrMat 𝒜 (r g).mat := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF _ R R' _ _ _ _ _ _ 𝒜 _ p j hp hS v hv r' hred hloc hlc hgr
  haveI := hS.fin
  haveI : Finite (GG (m := 3) (R := R)) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  obtain ⟨S, hSm⟩ := lu_sub 𝒜
  letI := Fintype.ofFinite (ResidueField O)
  obtain ⟨l, hchar, n, hl, hcard⟩ := FiniteField.card' (ResidueField O)
  have hkill : ∀ x y : R, x ∈ maximalIdeal R → p y = 0 → x * y = 0 := fun x y hx hy => by
    have := Ideal.mul_mem_mul hx (show y ∈ RingHom.ker p from hy)
    rwa [hS.kill] at this
  have hlm : (l : R) ∈ maximalIdeal R := by
    rw [← res_eq_zero_iff O, map_natCast]
    exact CharP.cast_eq_zero _ l
  obtain ⟨hK, hKl⟩ := lu_ker (p : R →+* R') (fun x y hx hy => hkill x y (hS.le hx) hy) l
    (fun x hx => hkill _ x hlm hx)
  have hle : ¬ l ∣ 2 * Nat.card (ResidueField O)ˣ := by
    rw [hl.dvd_mul, Nat.card_units, Nat.card_eq_fintype_card, hcard]
    rintro (h | h)
    · have h2 : ((2 : ℕ) : ResidueField O) = 0 := (CharP.cast_eq_zero_iff _ l 2).2 h
      have h3 := hF.two.map (residue O)
      rw [map_ofNat] at h3
      exact h3.ne_zero (by exact_mod_cast h2)
    · have h1 : l ∣ l ^ (n : ℕ) := dvd_pow_self l n.ne_zero
      have h2 : l ∣ l ^ (n : ℕ) - (l ^ (n : ℕ) - 1) := Nat.dvd_sub h1 h
      rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hl.pos)] at h2
      exact hl.one_lt.ne' (Nat.dvd_one.1 h2)
  obtain ⟨φ, hφ, hd⟩ := hF.frob v
  have hU := hloc.2.2 hv
  have hlc' : IsLocallyConstant r' := by
    have h1 : IsLocallyConstant (F.ηv v) :=
      hF.η_cont.comp_continuous (hF.π_cont.comp continuous_subtype_val)
    refine IsLocallyConstant.desc r' (fun x : GG (m := 3) (R := R') => (x.mat, x.right)) ?_ ?_
    · have := hlc.prodMk h1
      convert this using 1
      funext g
      exact Prod.ext rfl (hred.mult g)
    · intro x y h
      exact SemidirectProduct.ext (Units.ext (congrArg Prod.fst h)) (congrArg Prod.snd h)
  have hs : ∀ g, ∃ h : S, ((GG.map (p : R →+* R')).comp S.subtype) h = r' g := by
    intro g
    obtain ⟨X, hX, hXp⟩ := hgr g
    have hu : IsUnit X := by
      rw [Matrix.isUnit_iff_isUnit_det]
      have h1 : IsUnit (p X.det) := by
        have : p X.det = (r' g).mat.det := by
          rw [← hXp]; exact (p : R →+* R').map_det X
        rw [this, ← Matrix.isUnit_iff_isUnit_det]
        exact (r' g).left.isUnit
      by_contra hn
      have h2 : X.det ∈ maximalIdeal R := hn
      rw [← res_eq_zero_iff O R, ← res_map p X.det, res_eq_zero_iff O R'] at h2
      exact h2 h1
    exact ⟨⟨⟨hu.unit, (r' g).right⟩, (hSm _).2 hX⟩, SemidirectProduct.ext (Units.ext hXp) rfl⟩
  have he : ∀ s ∈ F.Iv v, r' s ^ (2 * Nat.card (ResidueField O)ˣ) = 1 := fun s hs => by
    rw [← map_pow]
    refine hU _ ⟨⟨pow_mem hs _, ?_⟩, ?_⟩
    · show F.ηv v _ = 1
      rw [map_pow, pow_mul, Int.units_sq, one_pow]
    · show ((Units.map (residue O).toMonoidHom).comp (F.Ψv v)) _ = 1
      rw [map_pow, pow_mul', pow_card_eq_one', one_pow]
  obtain ⟨r, hr, hrl, hrI⟩ := lu_abs ((GG.map (p : R →+* R')).comp S.subtype)
    (fun a b ha hb => Subtype.ext (hK _ _ ha hb)) l _ hl hle (fun a ha => Subtype.ext (hKl _ ha))
    (F.Iv v) (hF.I_normal v) φ hφ hd r' hlc' hs he
  refine ⟨S.subtype.comp r, MonoidHom.ext hr, ⟨fun h => ?_, fun h => ?_, fun _ s hs => ?_⟩,
    hrl.comp fun x : S => x.1.mat, fun g => (hSm _).1 (r g).2⟩
  · exact (hv (Or.inl h)).elim
  · exact (hv (Or.inr h)).elim
  · exact congrArg Subtype.val (hrI s hs.1.1 (hU s hs))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.GradedMatrixMulInv
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section
variable {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜]

private theorem gr_mul {X Y : Matrix (Fin 3) (Fin 3) R} (hX : GrMat 𝒜 X) (hY : GrMat 𝒜 Y) :
    GrMat 𝒜 (X * Y) := by
  intro a b
  simp only [Matrix.mul_apply]
  refine Submodule.sum_mem _ fun c _ => ?_
  have h := SetLike.GradedMul.mul_mem (hX a c) (hY c b)
  have e : wt a c + wt c b = wt a b := by simp only [wt]; ring
  rwa [e] at h

private theorem gr_one : GrMat 𝒜 (1 : Matrix (Fin 3) (Fin 3) R) := by
  intro a b
  by_cases h : a = b
  · subst h
    rw [Matrix.one_apply_eq]
    have e : wt a a = 0 := by simp [wt]
    rw [e]
    exact SetLike.GradedOne.one_mem
  · rw [Matrix.one_apply_ne h]
    exact zero_mem _

private theorem gr_pow {g : GL (Fin 3) R} (hg : GrMat 𝒜 (g : Matrix (Fin 3) (Fin 3) R)) (n : ℕ) :
    GrMat 𝒜 ((g ^ n : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  induction n with
  | zero => rw [pow_zero]; exact gr_one 𝒜
  | succ n ih => rw [pow_succ, Units.val_mul]; exact gr_mul 𝒜 ih hg

private theorem gr_inv [Finite R] {g : GL (Fin 3) R} (hg : GrMat 𝒜 (g : Matrix (Fin 3) (Fin 3) R)) :
    GrMat 𝒜 ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  have hn := orderOf_pos g
  have e : g⁻¹ = g ^ (orderOf g - 1) := by
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel hn, pow_orderOf_eq_one]
  rw [e]
  exact gr_pow 𝒜 hg _

private theorem gr_theta [Finite R] {g : GL (Fin 3) R} (hg : GrMat 𝒜 (g : Matrix (Fin 3) (Fin 3) R)) :
    GrMat 𝒜 ((theta g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  rw [theta_val]
  have hi := gr_inv 𝒜 hg
  have key : ∀ (M : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3),
      (Jmat R 3 * Mᵀ * Jmat R 3) a b = M b.rev a.rev := by
    intro M a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Jmat, Fin.sum_univ_three, Fin.rev]
  intro a b
  rw [key]
  have e : wt b.rev a.rev = wt a b := by fin_cases a <;> fin_cases b <;> rfl
  rw [← e]
  exact hi _ _

private theorem gr_act [Finite R] (s : ℤˣ) {g : GL (Fin 3) R} (hg : GrMat 𝒜 (g : Matrix (Fin 3) (Fin 3) R)) :
    GrMat 𝒜 ((sgnAct 3 R s g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · rw [sgnAct_one]; exact hg
  · rw [sgnAct_neg_one]; exact gr_theta 𝒜 hg

end

theorem UpperTheory.graded_matrix_mul_inv :
    ∀ {O R : Type} [CommRing O] [CommRing R] [Algebra O R] [Finite R]
      (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (x y : GG (m := 3) (R := R)),
      GrMat 𝒜 x.mat → GrMat 𝒜 y.mat → GrMat 𝒜 (x * y).mat ∧ GrMat 𝒜 (x⁻¹).mat := by
  intro O R _ _ _ _ 𝒜 _ x y hx hy
  unfold GG.mat at *
  constructor
  · rw [SemidirectProduct.mul_left, Units.val_mul]
    exact gr_mul 𝒜 hx (gr_act 𝒜 _ hy)
  · rw [SemidirectProduct.inv_left]
    exact gr_act 𝒜 _ (gr_inv 𝒜 hx)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LocAtPushOfLocAt
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section SlopeTestRemainingChoices

variable {O R R' D : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R'] [Group D]

private theorem map_ofGL (f : R →+* R') (h : GL (Fin 3) R) :
    GG.map f (GG.ofGL h) = GG.ofGL (GeneralLinearGroup.map f h) := by
  simp only [GG.map, GG.ofGL, SemidirectProduct.map_inl]

private theorem conj_push (φ : R →ₐ[O] R') (h : GL (Fin 3) R) (r : D →* GG (m := 3) (R := R)) (g : D) :
    conjBy (GeneralLinearGroup.map (φ : R →+* R') h)⁻¹ (((GG.map (φ : R →+* R')).comp r)) g =
      GG.map (φ : R →+* R') (conjBy h⁻¹ r g) := by
  simp only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_inv_apply,
    map_mul, map_inv, map_ofGL]

private theorem conj_push_mat (φ : R →ₐ[O] R') (h : GL (Fin 3) R) (r : D →* GG (m := 3) (R := R)) (g : D) (a b : Fin 3) :
    (conjBy (GeneralLinearGroup.map (φ : R →+* R') h)⁻¹ (((GG.map (φ : R →+* R')).comp r)) g).mat a b =
      φ ((conjBy h⁻¹ r g).mat a b) := by
  rw [conj_push]
  simp [GG.mat, GG.map, SemidirectProduct.map_left]

private theorem triIn_push (φ : R →ₐ[O] R') {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D}
    {r : D →* GG (m := 3) (R := R)} {h : GL (Fin 3) R} (H : TriIn η Ψ I r h) :
    TriIn η Ψ I ((GG.map (φ : R →+* R')).comp r) (GeneralLinearGroup.map (φ : R →+* R') h) := by
  refine ⟨?_, ?_⟩
  · intro g hg a b hab
    rw [conj_push_mat, H.tri g hg a b hab, map_zero]
  · intro s hs hη a
    rw [conj_push_mat, H.ine s hs hη a, AlgHom.commutes]

private theorem diagIn_push (φ : R →ₐ[O] R') {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D}
    {r : D →* GG (m := 3) (R := R)} {h : GL (Fin 3) R} (H : DiagIn η Ψ I r h) :
    DiagIn η Ψ I ((GG.map (φ : R →+* R')).comp r) (GeneralLinearGroup.map (φ : R →+* R') h) := by
  refine ⟨triIn_push φ H.toTriIn, ?_⟩
  intro g hg a b hab
  rw [conj_push_mat, H.low g hg a b hab, map_zero]

variable [IsLocalRing O] [IsCO O R] [IsCO O R']

private theorem inHat_push (φ : R →ₐ[O] R') {h : GL (Fin 3) R} (H : InHat h) :
    InHat (GeneralLinearGroup.map (φ : R →+* R') h) := by
  have hm : ∀ x ∈ maximalIdeal R, φ x ∈ maximalIdeal R' := by
    intro x hx
    rw [← res_eq_zero_iff O R', res_map, res_eq_zero_iff O R]
    exact hx
  unfold InHat CongOne EntIn at H ⊢
  intro a b
  have e : ((GeneralLinearGroup.map (φ : R →+* R') h : Matrix (Fin 3) (Fin 3) R') - 1) a b =
      φ (((h : Matrix (Fin 3) (Fin 3) R) - 1) a b) := by
    by_cases hab : a = b <;> simp [Matrix.sub_apply, hab]
  rw [e]
  exact hm _ (H a b)

end SlopeTestRemainingChoices

theorem UpperTheory.locAt_push_of_locAt :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ] (F : Frame O G Γ ι) {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (φ : R →ₐ[O] R') (v : ι) (r : F.D v →* GG (m := 3) (R := R)), F.LocAt v r → F.LocAt v (((GG.map (φ : R →+* R')).comp r)) := by
  intro O _ _ G Γ ι _ _ F R R' _ _ _ _ _ _ φ v r hr
  unfold Frame.LocAt at hr ⊢
  obtain ⟨hT, hD, hU⟩ := hr
  refine ⟨fun hv => ?_, fun hv => ?_, fun hv => ?_⟩
  · obtain ⟨h, hh, ht⟩ := hT hv
    exact ⟨_, inHat_push φ hh, triIn_push φ ht⟩
  · obtain ⟨h, hh, ht⟩ := hD hv
    exact ⟨_, inHat_push φ hh, diagIn_push φ ht⟩
  · intro s hs
    have h1 := hU hv s hs
    simp only [MonoidHom.comp_apply, h1, map_one]
end

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

open UpperTheory.V.UnitaryThreeInertia.Obs in
theorem UpperTheory.V.UnitaryThreeInertia.exists_unobstructed :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.LocVan → ∀ g₁, F.Marked g₁ → ∀ {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (p : R →ₐ[O] R') (j : ℤ), Function.Surjective p → SmallExt O 𝒜 (RingHom.ker p) j →
    Module.Finite (ResidueField O) (F.Ob j) → Nat.card (ResidueField O) ^ Module.finrank (ResidueField O) (F.Ob j) < Nat.card (RingHom.ker p) →
      ∀ (r' : Γ →* GG (m := 3) (R := R')), F.IsPt g₁ r' → (∀ g, ∃ X, GrMat 𝒜 X ∧ X.map p = (r' g).mat) →
      ∃ (R'' : Type) (_ : CommRing R'') (_ : Algebra O R'') (_ : IsCO O R'') (p₁ : R →ₐ[O] R'') (q : R'' →ₐ[O] R') (r : Γ →* GG (m := 3) (R := R'')),
        Function.Surjective p₁ ∧ q.comp p₁ = p ∧ ¬ Function.Injective q ∧ F.IsPt g₁ r ∧ push q r = r' := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF hV g₁ hg₁ R R' _ _ _ _ _ _ 𝒜 _ p j hp hI hfin hlt r' hr' hgr
  have := hI.fin
  have : Finite R' := Finite.of_surjective p hp
  have hS : Sm (incl O (RingHom.ker p)) := ⟨fun y => hI.le y.2, fun x hx y => by
    have := Ideal.mul_mem_mul hx y.2
    rwa [hI.kill, Ideal.mem_bot] at this⟩
  have hinj : Function.Injective (incl O (RingHom.ker p)) := Subtype.val_injective
  have hlc := lc_mats r' hr'.cont
  have hloc : ∀ v, Continuous (F.loc v) := fun v => hF.π_cont.comp continuous_subtype_val
  obtain ⟨s, hs, hsc, hsg⟩ := exists_setLift 𝒜 p hp r' hlc hgr
  have hsr : ∀ g, (s g).right = F.η g := fun g =>
    (congrArg SemidirectProduct.right (hs g)).trans (hr'.mult g)
  have hsm : ∀ g, EntIn (maximalIdeal R) ((s g).mat - ((r0 F.η F.Ψ g).mat).map (algebraMap O R)) := fun g =>
    red_of_map p _ _ g _ (by rw [hs]; exact hr'.red g)
  have hsl : IsLocallyConstant s := lc_of_mat s hsc (by rw [funext hsr]; exact hF.η_cont)
  have hex : ∀ v, ∃ r : F.D v →* GG (m := 3) (R := R), push p r = r'.comp (F.loc v) ∧ F.LocAt v r ∧ IsLocallyConstant (mats r) ∧
      ∀ g, GrMat 𝒜 (r g).mat := fun v => by
    have h0 : Red (F.ηv v) (F.Ψv v) (r'.comp (F.loc v)) := ⟨fun g => hr'.mult _, fun g => hr'.red _⟩
    have hc : IsLocallyConstant (mats (r'.comp (F.loc v))) := hlc.comp_continuous (hloc v)
    by_cases h1 : v = F.vl
    · exact exists_graded_lift_unitary_local_tame F hF hV 𝒜 p j hp hI v h1 _ h0 (hr'.loc v) hc fun g => hgr _
    by_cases h2 : v ∈ F.Sb
    · exact exists_lift_d F hF hV 𝒜 p j hp hI v h2 _ h0 (hr'.loc v) hc fun g => hgr _
    · exact exists_lift_u F hF hV 𝒜 p j hp hI v (fun h3 => h3.elim h1 h2) _ h0 (hr'.loc v) hc fun g => hgr _
  choose ρ hρ hρl hρc hρg using hex
  have hρ' : ∀ v g, GG.map (p : R →+* R') (ρ v g) = r' (F.loc v g) := fun v g => DFunLike.congr_fun (hρ v) g
  have hρr : ∀ v, Red (F.ηv v) (F.Ψv v) (ρ v) := fun v =>
    ⟨fun g => (congrArg SemidirectProduct.right (hρ' v g)).trans (hr'.mult _),
      fun g => red_of_map p _ _ g _ (by rw [hρ']; exact hr'.red _)⟩
  have hρL : ∀ v, IsLocallyConstant (ρ v) := fun v => lc_of_mat _ (hρc v) (by
    rw [funext (hρr v).mult]; exact hF.η_cont.comp_continuous (hloc v))
  have hmul : ∀ x y : GG (m := 3) (R := R), GrMat 𝒜 x.mat → GrMat 𝒜 y.mat → GrMat 𝒜 (x * y⁻¹).mat := fun x y hx hy =>
    (UpperTheory.graded_matrix_mul_inv 𝒜 x y⁻¹ hx (UpperTheory.graded_matrix_mul_inv 𝒜 y y hy hy).2).1
  choose K hK hKw using fun gg : Γ × Γ => exists_ex 𝒜 p j hI.wt hS (s gg.1 * s gg.2) (s (gg.1 * gg.2))
    (by rw [map_mul, hs, hs, hs, map_mul]) (hmul _ _ (UpperTheory.graded_matrix_mul_inv 𝒜 _ _ (hsg _) (hsg _)).1 (hsg _))
  choose A hA hAw using fun (v : ι) (g : F.D v) => exists_ex 𝒜 p j hI.wt hS (s (F.loc v g)) (ρ v g)
    (by rw [hs, hρ']) (hmul _ _ (hsg _) (hρg _ _))
  have hKc : IsLocallyConstant K := by
    refine IsLocallyConstant.desc K hS.ex ?_ fun _ _ => hS.ex_inj hinj
    have e : hS.ex ∘ K = fun gg => s gg.1 * s gg.2 * (s (gg.1 * gg.2))⁻¹ := funext fun gg => by
      rw [hK gg, mul_inv_cancel_right]; rfl
    rw [e]
    exact ((hsl.comp_continuous continuous_fst).mul (hsl.comp_continuous continuous_snd)).mul
      (hsl.comp_continuous continuous_mul).inv
  have hAc : ∀ v, IsLocallyConstant (A v) := fun v => by
    refine IsLocallyConstant.desc (A v) hS.ex ?_ fun _ _ => hS.ex_inj hinj
    have e : hS.ex ∘ A v = fun g => s (F.loc v g) * (ρ v g)⁻¹ := funext fun g => by
      rw [hA v g, mul_inv_cancel_right]; rfl
    rw [e]
    exact (hsl.comp_continuous (hloc v)).mul (hρL v).inv
  let κ : (RingHom.ker p →ₗ[O] ResidueField O) → Γ × Γ → Gb (k := ResidueField O) j := fun φ gg =>
    ⟨(K gg).map φ, fun a b hab => by rw [Matrix.map_apply, hKw gg a b hab, map_zero]⟩
  let α : (RingHom.ker p →ₗ[O] ResidueField O) → ∀ v, F.D v → Gb (k := ResidueField O) j := fun φ v g =>
    ⟨(A v g).map φ, fun a b hab => by rw [Matrix.map_apply, hAw v g a b hab, map_zero]⟩
  have hval : Function.Injective (Gb.val : Gb (k := ResidueField O) j → _) := Subtype.val_injective
  have hZ : ∀ φ, (κ φ, α φ) ∈ F.framedTwoCocycles j := fun φ => by
    refine ⟨⟨?_, fun g g' k => hval ?_⟩, (Submodule.mem_iInf _).2 fun v => ⟨?_, ?_⟩⟩
    · exact (IsLocallyConstant.desc (κ φ) Gb.val (hKc.comp fun Y => Y.map φ) hval).continuous
    · have e := congrArg (fun Y => Y.map φ) (hS.coc F.η F.Ψ hinj s hsr hsm K (fun g g' => hK (g, g')) g g' k)
      simp only [Matrix.map_sub _ (map_sub φ), Matrix.map_add _ (map_add φ), act_map,
        Matrix.map_zero _ (map_zero φ)] at e
      show (F.gbar j g (κ φ (g', k))).val - _ + _ - _ = _
      rw [Frame.gbar, Frame.Ψbar, act_val]
      exact e
    · exact (IsLocallyConstant.desc (α φ v) Gb.val ((hAc v).comp fun Y => Y.map φ) hval).continuous
    · funext ⟨g, g'⟩
      apply hval
      have e := congrArg (fun Y => Y.map φ) (hS.cob (F.ηv v) (F.Ψv v) hinj (fun g => s (F.loc v g)) (ρ v) (hρr v)
        (fun gg => K (F.loc v gg.1, F.loc v gg.2)) (fun g g' => by rw [map_mul]; exact hK (_, _)) (A v) (hA v) g g')
      simp only [Matrix.map_sub _ (map_sub φ), Matrix.map_add _ (map_add φ), act_map] at e
      show (F.gbar j (F.loc v g) (α φ v g')).val - _ + _ = _
      rw [Frame.gbar, Frame.Ψbar, act_val]
      exact e
  obtain ⟨φ, hφ, hB⟩ : ∃ φ, φ ≠ 0 ∧ (κ φ, α φ) ∈ F.framedTwoCoboundaries j := by
    have : Finite (F.Ob j) := Module.finite_of_finite (ResidueField O)
    have hn : ¬ Function.Injective fun φ => (Submodule.Quotient.mk ⟨_, hZ φ⟩ : F.Ob j) := fun hi => by
      have h1 := Nat.card_le_card_of_injective _ hi
      rw [UpperTheory.card_dual_residueField_eq_card_of_maximalIdeal_smul_eq_zero (O := O) (N := RingHom.ker p) (fun a ha x => Subtype.ext (by
        have h2 := hS.kill (algebraMap O R a) (map_nonunit (algebraMap O R) a ha) x
        rw [← Algebra.smul_def] at h2
        exact h2))] at h1
      rw [← Module.natCard_eq_pow_finrank (K := ResidueField O) (V := F.Ob j)] at hlt
      exact absurd hlt (not_lt.2 h1)
    obtain ⟨φ₁, φ₂, e, hne⟩ := Function.not_injective_iff.1 hn
    refine ⟨φ₁ - φ₂, sub_ne_zero.2 hne, ?_⟩
    exact (Submodule.Quotient.eq _).1 e
  obtain ⟨R'', _, _, _, p₁, q, ε, hp₁, hq, hqi, hε, hqε, hm, hk⟩ := UpperTheory.exists_small_extension_factorization_of_functional p hI.kill hI.le φ hφ
  have hS' : Sm ε := ⟨hm, hk⟩
  have hqp : ∀ x : GG (m := 3) (R := R), GG.map (q : R'' →+* R') (GG.map (p₁ : R →+* R'') x) = GG.map (p : R →+* R') x :=
    fun x => by rw [← hq]; rfl
  obtain ⟨r, hr, hrc, hrs⟩ := unobs F hF hV hS' j (fun g => GG.map (p₁ : R →+* R'') (s g)) hsr
    (fun g => red_of_map q _ _ g _ (by rw [hqp, hs]; exact hr'.red g)) (hsc.comp fun X => X.map p₁)
    (fun v => push p₁ (ρ v))
    (fun v => ⟨(hρr v).mult, fun g => red_of_map q _ _ g _ (by
      rw [MonoidHom.comp_apply, hqp, hρ']; exact hr'.red _)⟩)
    (fun v => UpperTheory.locAt_push_of_locAt F p₁ v _ (hρl v)) (κ φ) (α φ)
    (fun g g' => by rw [← map_mul, hK (g, g'), map_mul, map_ex hS hS' p₁ φ hε]; rfl)
    (fun v g => by rw [hA v g, map_mul, map_ex hS hS' p₁ φ hε]; rfl) hB
  have hqs : Function.Surjective q := by
    rw [← hq] at hp
    exact Function.Surjective.of_comp hp
  obtain ⟨r₂, h1, h2⟩ := UpperTheory.lift_along_surjection_graded F hF g₁ hg₁ q hqs r r' hr hrc (MonoidHom.ext fun g => by
    obtain ⟨Y, hY⟩ := hrs g
    rw [MonoidHom.comp_apply, hY, map_mul, map_ex_one hS' q hqε, one_mul, hqp, hs]) hr'.toCondN
  exact ⟨R'', inferInstance, inferInstance, inferInstance, p₁, q, r₂, hp₁, hq, hqi, h1, h2⟩
