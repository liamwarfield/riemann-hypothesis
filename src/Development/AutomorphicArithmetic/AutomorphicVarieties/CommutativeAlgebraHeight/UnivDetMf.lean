module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UnivDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GKillsTr

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UnivDetMf
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem lc_of_ker {G M : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
    (φ : G →* M) (h : IsOpen (φ.ker : Set G)) : IsLocallyConstant φ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker φ h

private theorem chi_ofRep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) =
      ((X : A[X]) • (1 : Matrix (Fin n) (Fin n) A[X]) - (ρ g).map (algebraMap A A[X])).det := by
  change (GDet.repAlg ρ A[X] _).det = _
  congr 1
  rw [map_sub, MonoidAlgebra.mapRingHom_single]
  simp [GDet.repAlg]

private theorem cont_ofChars {n : ℕ} {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (χ : Fin n → G →* Aˣ) (h : ∀ i, IsOpen ((χ i).ker : Set G)) (I : Ideal A) : (GDet.ofChars χ).IsCont I := by
  intro i N
  have h1 : IsLocallyConstant fun g j => χ j g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have := fun j => (lc_of_ker (χ j) (h j)).eventually_eq x
    exact (Filter.eventually_all.2 this).mono fun y hy => funext hy
  have h2 := h1.comp fun v : Fin n → Aˣ => Ideal.Quotient.mk (I ^ N) ((-1) ^ i *
    (((X : A[X]) • (1 : Matrix (Fin n) (Fin n) A[X]) -
      (Matrix.diagonal fun j => (v j : A)).map (algebraMap A A[X])).det).coeff (n - i))
  convert h2 using 1
  funext g
  simp [GDet.lam, GDet.ofChars, chi_ofRep, GDet.diagRep]

private theorem fin_field (l : ℕ) [Fact l.Prime] {n : ℕ} {k G : Type} [Field k] [Finite k] [CharP k l] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (χ : Fin n → G →* kˣ)
    (hP : PhiCond (Γ := G) l) (ho : ∀ i, IsOpen ((χ i).ker : Set G)) (hi : Function.Injective χ) :
    Module.Finite k ((GDet.ofChars χ).CHQuot ∅) := by
  have hinj : Function.Injective (residue k) := (residue k).injective
  haveI : Finite (ResidueField k) := Finite.of_surjective _ residue_surjective
  haveI : CharP (ResidueField k) l := charP_of_injective_ringHom hinj l
  haveI : IsAdicComplete (maximalIdeal k) k := by
    rw [maximalIdeal_eq_bot]
    infer_instance
  let u : kˣ →* (ResidueField k)ˣ := Units.map (residue k).toMonoidHom
  have hu : Function.Injective u := Units.map_injective hinj
  let χ' : Fin n → G →* (ResidueField k)ˣ := fun i => u.comp (χ i)
  have ho' : ∀ i, IsOpen ((χ' i).ker : Set G) := fun i => by
    have : (χ' i).ker = (χ i).ker := MonoidHom.ker_comp_of_injective _ _ hu
    rw [this]
    exact ho i
  have hi' : Function.Injective χ' := fun i j hij =>
    hi (MonoidHom.ext fun g => hu (DFunLike.congr_fun hij g))
  obtain ⟨h, hm⟩ := exists_multFree_of_phiCond_of_injective_chars l χ' hP ho' hi'
  have hmap : (GDet.ofChars χ).map (residue k) = GDet.ofChars χ' := by
    unfold GDet.ofChars
    rw [(d_gmap (GDet.ofRep (GDet.diagRep χ))).2.2.2]
    congr 1
    ext g a b
    by_cases hab : a = b
    · subst hab
      simp [GDet.diagRep, χ', u]
    · simp [GDet.diagRep, hab]
  exact (finE (GDet.ofChars χ) χ' (cont_ofChars χ ho _) hmap hm ∅).2.1

theorem UpperTheory.V.CA.univDet_mf :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] {n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (χ : Fin n → G →* (ResidueField O)ˣ), PhiCond (Γ := G) l → (∀ i, IsOpen ((χ i).ker : Set G)) → Function.Injective χ → ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (D : GDet n R G), IsUnivDet O (GDet.ofChars χ) D := by
  intro l _ O _ _ _ _ _ _ n G _ _ _ _ _ χ hP ho hi
  exact univDet l O (GDet.ofChars χ) hP (cont_ofChars χ ho _) (fin_field l χ hP ho hi)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.PairKills
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section

variable {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]

private theorem pk_starOp_single (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (g : F.G₀) (a : R) :
    F.starOp O R n (MonoidAlgebra.single g a) =
      MulOpposite.op (MonoidAlgebra.single (F.conj g)⁻¹ (a * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R))) := by
  rw [GFrame.starOp, MonoidAlgebra.lift_single]
  show a • MulOpposite.op (MonoidAlgebra.single (F.conj g)⁻¹ ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) = _
  rw [← MulOpposite.op_smul, MonoidAlgebra.smul_single']

private theorem pk_conj_conj (g : F.G₀) : F.conj (F.conj g) = g := by
  apply Subtype.ext
  change F.c * (F.c * g * F.c⁻¹) * F.c⁻¹ = g
  have h : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right F.c_sq
  rw [h, ← mul_assoc, ← mul_assoc, F.c_sq, one_mul, mul_assoc, F.c_sq, mul_one]

private theorem eps_conj_eq_eps' (R : Type) [CommRing R] [Algebra O R] (g : F.G₀) :
    F.eps O R (F.conj g) = F.eps O R g := by
  have h : F.ε ((F.conj g : F.G₀) : F.Γ) = F.ε (g : F.Γ) := by
    show F.ε (F.c * (g : F.Γ) * F.c⁻¹) = F.ε g
    rw [map_mul, map_mul, map_inv, mul_comm (F.ε F.c), mul_assoc, mul_inv_cancel, mul_one]
  simp only [GFrame.eps, pushCh, MonoidHom.comp_apply, Subgroup.coe_subtype, h]

private theorem star_star_monoidAlgebra (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (y : MonoidAlgebra R F.G₀) :
    F.star O R n (F.star O R n y) = y := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp [GFrame.star]
  | add x y hx hy =>
    simp only [GFrame.star, map_add (f := _), MulOpposite.unop_add] at hx hy ⊢
    rw [hx, hy]
  | single g a =>
    show MulOpposite.unop (F.starOp O R n (MulOpposite.unop (F.starOp O R n (MonoidAlgebra.single g a)))) =
      MonoidAlgebra.single g a
    rw [pk_starOp_single, MulOpposite.unop_op, pk_starOp_single, MulOpposite.unop_op]
    congr 1
    · rw [map_inv, inv_inv, pk_conj_conj]
    · rw [map_inv, eps_conj_eq_eps', inv_zpow, mul_assoc, Units.mul_inv, mul_one]

private theorem pk_surj (R : Type) [CommRing R] [Algebra O R] (n : ℕ) : Function.Surjective (F.starOp O R n) := by
  intro x
  refine ⟨F.star O R n (MulOpposite.unop x), ?_⟩
  apply MulOpposite.unop_injective
  exact star_star_monoidAlgebra F O R n (MulOpposite.unop x)

private theorem pk_eps (R B : Type) [CommRing R] [Algebra O R] [CommRing B] [Algebra R B] [Algebra O B]
    [IsScalarTower O R B] (g : F.G₀) (m : ℤ) :
    algebraMap R B ((F.eps O R g ^ m : Rˣ) : R) = ((F.eps O B g ^ m : Bˣ) : B) := by
  simp only [GFrame.eps, pushCh, MonoidHom.comp_apply, ← map_zpow, Units.coe_map, RingHom.coe_comp,
    Function.comp_apply, MonoidHom.coe_coe]
  exact (IsScalarTower.algebraMap_apply O R B _).symm

private theorem pk_bc (R B : Type) [CommRing R] [Algebra O R] [CommRing B] [Algebra R B] [Algebra O B]
    [IsScalarTower O R B] (n : ℕ) (y : MonoidAlgebra B F.G₀) :
    ofT R F.G₀ B (Det.unopS R (MonoidAlgebra R F.G₀) B
      (Algebra.TensorProduct.map (AlgHom.id B B) (F.starOp O R n) (toT R F.G₀ B y))) = F.star O B n y := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp [GFrame.star]
  | add x y hx hy =>
    simp only [map_add (f := _), GFrame.star, MulOpposite.unop_add] at hx hy ⊢
    rw [hx, hy]
  | single g b =>
    show _ = MulOpposite.unop (F.starOp O B n (MonoidAlgebra.single g b))
    rw [pk_starOp_single, MulOpposite.unop_op, toT_single, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      pk_starOp_single, one_mul, Det.unopS, LinearMap.baseChange_tmul]
    show ofT R F.G₀ B (b ⊗ₜ MonoidAlgebra.single (F.conj g)⁻¹ ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) = _
    have hm : MonoidAlgebra.mapRingHom F.G₀ (algebraMap R B)
        (MonoidAlgebra.single (F.conj g)⁻¹ ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) =
        MonoidAlgebra.single (F.conj g)⁻¹ (algebraMap R B ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
      simp [MonoidAlgebra.mapRingHom]
    rw [ofT_tmul, hm, pk_eps, MonoidAlgebra.smul_single']

end

theorem UpperTheory.V.CA.pair_kills :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] [Algebra ℤ_[l] O] {n : ℕ} (r : Resid F O n) {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (p : Pair r R), PhiCond (Γ := F.G₀) l → 1 ≤ n → F.IsPolar O p.D ∧ (∀ y, p.D.Kills y → p.D.Kills (F.star O R n y)) ∧ (∀ z ∈ TwoSidedIdeal.span p.D.CH, F.star O R n z ∈ TwoSidedIdeal.span p.D.CH) ∧ (∀ v g, p.D.Kills (F.oEl v (p.ψ v) g)) ∧ ∀ u, ∀ g ∈ r.Ip u, p.D.Kills (MonoidAlgebra.single g 1 - 1) := by
  intro l _ F O _ _ _ _ _ _ _ n r R _ _ _ p hphi hn
  have hspan : Submodule.span R (↑(MonoidHom.mrange (MonoidAlgebra.of R F.G₀)) : Set (MonoidAlgebra R F.G₀)) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    induction x using MonoidAlgebra.induction_linear with
    | zero => exact Submodule.zero_mem _
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | single g a =>
      have hs : MonoidAlgebra.single g a = a • MonoidAlgebra.of R F.G₀ g := by
        rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
      rw [hs]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨g, rfl⟩)
  have hlam : ∀ x ∈ MonoidHom.mrange (MonoidAlgebra.of R F.G₀), ∀ i : ℕ, 1 ≤ i → i ≤ n →
      p.D.toDet.lam i (MulOpposite.unop (F.starOp O R n x)) = p.D.toDet.lam i x := by
    rintro x ⟨g, rfl⟩ i _ _
    rw [(d_toDet p.D _).2.1, (d_toDet p.D _).2.1, MonoidAlgebra.of_apply]
    exact p.P i g
  obtain ⟨hpull, hCH, hker⟩ := d_star p.D.toDet (F.starOp O R n) _ hspan hlam
  have hpolar : F.IsPolar O p.D := by
    intro B _ _ _ _ y
    have h1 := congrArg (fun X : Det n R (MonoidAlgebra R F.G₀) => X.D B (toT R F.G₀ B y)) hpull
    change p.D.D B (ofT R F.G₀ B (Det.unopS R (MonoidAlgebra R F.G₀) B
      (Algebra.TensorProduct.map (AlgHom.id B B) (F.starOp O R n) (toT R F.G₀ B y)))) =
      p.D.D B (ofT R F.G₀ B (toT R F.G₀ B y)) at h1
    rw [pk_bc, ofT_toT] at h1
    exact h1
  haveI : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  have he : Function.Injective (ResidueField.map (algebraMap O R)) := (resMap_bijective O R).1
  haveI : Finite (ResidueField R) := Finite.of_surjective _ (resMap_bijective O R).2
  haveI : CharP (ResidueField R) l := charP_of_injective_ringHom he l
  let χ : Fin n → F.G₀ →* (ResidueField R)ˣ := fun i =>
    (Units.map (ResidueField.map (algebraMap O R) : ResidueField O →* ResidueField R)).comp (r.chib i)
  have hres : (ResidueField.map (algebraMap O R)).comp (res O R : R →+* ResidueField O) = residue R := by
    ext x
    show ResidueField.map (algebraMap O R) ((RingEquiv.ofBijective _ (resMap_bijective O R)).symm (residue R x)) =
      residue R x
    exact (RingEquiv.ofBijective _ (resMap_bijective O R)).apply_symm_apply _
  have hD : p.D.map (residue R) = GDet.ofChars χ := by
    rw [← hres, ← (d_gmap p.D).2.1, p.red, Resid.Dbar, (d_gmap (GDet.ofRep (diagRep r.chib))).2.2.2, GDet.ofChars]
    congr 1
    ext g i j
    by_cases hij : i = j
    · subst hij
      simp [χ, diagRep, GDet.diagRep]
    · simp [χ, diagRep, GDet.diagRep, Matrix.diagonal_apply_ne _ hij]
  have hopen : ∀ i, IsOpen (↑(χ i).ker : Set F.G₀) := by
    intro i
    have hk : (χ i).ker = (r.chib i).ker := by
      ext g
      simp only [MonoidHom.mem_ker, χ, MonoidHom.comp_apply]
      constructor
      · intro h
        apply Units.ext
        apply he
        have h2 := congrArg Units.val h
        simpa using h2
      · intro h
        rw [h, map_one]
    rw [hk]
    exact r.chib_open i
  have hinj : Function.Injective χ := by
    intro i j hij
    apply r.chib_inj
    ext g
    apply he
    have h2 := congrArg (fun f : F.G₀ →* (ResidueField R)ˣ => ((f g : (ResidueField R)ˣ) : ResidueField R))
      hij
    simpa [χ] using h2
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  obtain ⟨h, hh⟩ := exists_multFree_of_phiCond_of_injective_chars l χ hphi hopen hinj
  have hK : ∀ y, p.D.Kills y ↔ ∀ g : F.G₀, p.D.tr (MonoidAlgebra.single g 1 * y) = 0 :=
    fun y => g_kills_tr p.D χ p.cont hD hh hn y
  refine ⟨hpolar, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have hy' : y ∈ p.D.toDet.ker := (d_ker p.D.toDet y).1.2 ((d_toDet p.D y).2.2.2.2 hy)
    exact (d_toDet p.D _).2.2.2.1 ((d_ker p.D.toDet _).1.1 (hker (pk_surj F O R n) y hy'))
  · intro z hz
    rw [← d_toDet_CH] at hz ⊢
    exact hCH z hz
  · intro v g
    exact (hK _).2 (p.Ord v g)
  · intro u g hg
    exact (hK _).2 (p.I u g hg)
end
