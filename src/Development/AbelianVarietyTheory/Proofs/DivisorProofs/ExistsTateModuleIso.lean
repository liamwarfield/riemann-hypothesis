module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPairingEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMoritaLatticeQuotientTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionBySetPowFreeOfCardPowNumberField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataNsmulRescaleKeepsLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommutatorPairingValueHeckePoints

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericCoordsDescendSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleRootsAndEvaluation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReferenceGeometrySameGeneric
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEvaluationHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFirstFromResolutionAndGaga
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

noncomputable section

namespace GlobalTheory.UPel.HT.PTors

def HasLev {A : Type} [CommRing A] (O : Type) [Ring O] (L M : Type) [AddCommGroup L] [AddCommGroup M]
    [Module O L] [Module O M] [Module A L] [Module A M] (I : Ideal A) : Prop :=
  ∃ l : L →ₗ[O] M, (∀ x, l x = 0 ↔ x ∈ I • (⊤ : Submodule A L)) ∧ ∀ g : M, (∀ c ∈ I, c • g = 0) → ∃ y, l y = g

section Alg

variable {A : Type} [CommRing A] {O : Type} [Ring O] [Algebra A O] {L M : Type} [AddCommGroup L] [AddCommGroup M]
  [Module O L] [Module O M] [Module A L] [Module A M] [IsScalarTower A O L] [IsScalarTower A O M]

omit [Algebra A O] [IsScalarTower A O L] [IsScalarTower A O M] in
theorem hasLev_top : HasLev O L M (⊤ : Ideal A) :=
  ⟨0, fun x => by simp, fun g hg => ⟨0, by simpa using (hg 1 Submodule.mem_top).symm⟩⟩

theorem HasLev.mul {I J : Ideal A} (hIJ : I ⊔ J = ⊤) (hI : HasLev O L M I) (hJ : HasLev O L M J) :
    HasLev O L M (I * J) := by
  obtain ⟨l₁, k₁, s₁⟩ := hI
  obtain ⟨l₂, k₂, s₂⟩ := hJ
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hIJ.symm ▸ Submodule.mem_top : (1 : A) ∈ I ⊔ J)
  have t₁ : ∀ c ∈ I, ∀ x, c • l₁ x = 0 := fun c hc x => by
    rw [← LinearMap.map_smul_of_tower]
    exact (k₁ _).2 (Submodule.smul_mem_smul hc Submodule.mem_top)
  have t₂ : ∀ c ∈ J, ∀ x, c • l₂ x = 0 := fun c hc x => by
    rw [← LinearMap.map_smul_of_tower]
    exact (k₂ _).2 (Submodule.smul_mem_smul hc Submodule.mem_top)
  have u₁ : ∀ x, b • l₁ x = l₁ x := fun x => by
    conv_rhs => rw [← one_smul A (l₁ x), ← hab, add_smul, t₁ a ha, zero_add]
  have u₂ : ∀ x, a • l₂ x = l₂ x := fun x => by
    conv_rhs => rw [← one_smul A (l₂ x), ← hab, add_smul, t₂ b hb, add_zero]
  refine ⟨l₁ + l₂, fun x => ⟨fun h => ?_, fun h => ?_⟩, fun g hg => ?_⟩
  · rw [LinearMap.add_apply] at h
    have h₁ : l₁ x = 0 := by
      have := congrArg (b • ·) h
      simpa only [smul_add, u₁, t₂ b hb, add_zero, smul_zero] using this
    have h₂ : l₂ x = 0 := by rwa [h₁, zero_add] at h
    have e : x = a • x + b • x := by rw [← add_smul, hab, one_smul]
    rw [e]
    refine add_mem ?_ ?_
    · rw [Submodule.mul_smul]
      exact Submodule.smul_mem_smul ha ((k₂ x).1 h₂)
    · rw [mul_comm, Submodule.mul_smul]
      exact Submodule.smul_mem_smul hb ((k₁ x).1 h₁)
  · rw [LinearMap.add_apply, (k₁ x).2 (Submodule.smul_mono_left Ideal.mul_le_left h),
      (k₂ x).2 (Submodule.smul_mono_left Ideal.mul_le_right h), add_zero]
  · obtain ⟨y₁, hy₁⟩ := s₁ (b • g) fun c hc => by
      rw [smul_smul]; exact hg _ (Ideal.mul_mem_mul hc hb)
    obtain ⟨y₂, hy₂⟩ := s₂ (a • g) fun c hc => by
      rw [smul_smul, mul_comm]; exact hg _ (Ideal.mul_mem_mul ha hc)
    refine ⟨b • y₁ + a • y₂, ?_⟩
    simp only [LinearMap.add_apply, map_add (f := _), LinearMap.map_smul_of_tower, smul_add]
    rw [u₁, u₂, t₁ a ha, t₂ b hb, hy₁, hy₂, add_zero, zero_add, ← add_smul, add_comm, hab, one_smul]

theorem hasLev_of_prime_pow [IsDedekindDomain A] (q : A) (hq : q ≠ 0) (e : ℕ)
    (h : ∀ w : Ideal A, w.IsMaximal → q ∈ w → ∀ r, HasLev O L M (w ^ r)) (I : Ideal A) :
    q ^ e ∈ I → HasLev O L M I := by
  induction I using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 => exact fun h0 => absurd (Ideal.mem_bot.1 h0) (pow_ne_zero _ hq)
  | h1 hu => rw [Ideal.isUnit_iff.1 hu]; exact fun _ => hasLev_top
  | @hpr w i hw =>
    intro hm
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [pow_zero, Ideal.one_eq_top]; exact hasLev_top
    · have hwp := Ideal.isPrime_of_prime hw
      exact h w (hwp.isMaximal hw.ne_zero) (hwp.mem_of_pow_mem e (Ideal.pow_le_self hi.ne' hm)) i
  | @hcp I J hIJ hI hJ =>
    intro hm
    refine HasLev.mul ?_ (hI (Ideal.mul_le_left hm)) (hJ (Ideal.mul_le_right hm))
    exact Ideal.isUnit_iff.1 (hIJ (Ideal.dvd_iff_le.2 le_sup_left) (Ideal.dvd_iff_le.2 le_sup_right))

end Alg


open GlobalTheory.AV GlobalTheory.AV.AbVar in
theorem card_ker_eq_det {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (u u' : A ⟶ A) [IsMonHom u] [IsMonHom u']
    (n : ℕ) (hn : n ≠ 0) (hu : u ≫ u' = (𝟙 A) ^ n)
    (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L] (φ : L →ₗ[ℤ] L)
    (hφ : LinearMap.det φ ≠ 0) (l : ℕ) (hl : l.Prime) (ev : ℕ → L → (Over.mk x ⟶ A))
    (h1 : ∀ j y z, ev j (y + z) = ev j y * ev j z) (h2 : ∀ j y, ev j (φ y) = ev j y ≫ u)
    (h3 : ∀ j y, ev j y = 1 ↔ ∃ z, y = l ^ j • z)
    (h4 : ∀ j (q : Over.mk x ⟶ A), q ^ (l ^ j) = 1 ↔ ∃ y, ev j y = q) :
    Nat.card {g : Over.mk x ⟶ A // g ≫ u = 1} = (LinearMap.det φ).natAbs := by
  obtain ⟨x', rfl⟩ : ∃ x', x = 𝟙 _ ≫ x' := ⟨x, (Category.id_comp x).symm⟩
  letI : GrpObj ((Over.pullback x').obj A) := Functor.grpObjObj
  have hA' := GlobalTheory.isAbelianScheme_pullback_obj x' A hA
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim k ((Over.pullback x').obj A) hA'
  let B : AbVar k := { X := (Over.pullback x').obj A, ab := hA', dim := g, smooth := hg }
  have pb : IsGrpPullback B.X A x' (pullback.fst A.hom x') := isGrpPullback_pullback A x'
  have hbij : ∀ T : Over (Sp k), Function.Bijective (pushHom pb T) := fun T => by
    constructor
    · intro y z e
      apply Over.OverMorphism.ext
      apply pb.1.hom_ext
      · exact congrArg (fun z => z.left) e
      · rw [Over.w, Over.w]
    · intro y
      refine ⟨Over.homMk (pb.1.lift y.left T.hom (Over.w y)) (pb.1.lift_snd _ _ _), ?_⟩
      exact Over.OverMorphism.ext (pb.1.lift_fst _ _ _)
  let f : B ⟶ B := Hom.mk (A := B) (B := B) ((Over.pullback x').map u)
    (h := inferInstanceAs (IsMonHom ((Over.pullback x').map u)))
  have hf : ∀ (T : Over (Sp k)) (y : T ⟶ B.X), pushHom pb T (y ≫ f.hom) = pushHom pb T y ≫ u := fun T y => by
    apply Over.OverMorphism.ext
    change (y.left ≫ ((Over.pullback x').map u).left) ≫ pullback.fst A.hom x' =
      (y.left ≫ pullback.fst A.hom x') ≫ u.left
    rw [Category.assoc, Category.assoc]
    congr 1
    exact pullback.lift_fst _ _ _
  let e : (Over.mk (𝟙 (Sp k)) ⟶ B.X) ≃* (Over.mk (𝟙 _ ≫ x') ⟶ A) :=
    MulEquiv.ofBijective (pushHom pb (Over.mk (𝟙 (Sp k)))) (hbij _)
  have ea : ∀ y, e (y ≫ f.hom) = e y ≫ u := fun y => hf _ y
  have hlk : (l : k) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  open GlobalTheory.CharpolyLattice GlobalTheory.HTLat in
  have charpoly_eq_lattice_model : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : GlobalTheory.AV.AbVar k) (f : B ⟶ B)
      (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
      (φ : L →ₗ[ℤ] L) (l : ℕ), l.Prime → (l : k) ≠ 0 →
      ∀ ev : ℕ → L → (Over.mk (𝟙 (Sp k)) ⟶ B.X),
      (∀ j x y, ev j (x + y) = ev j x * ev j y) →
      (∀ j x, ev j (φ x) = ev j x ≫ f.hom) →
      (∀ j x, ev j x = 1 ↔ ∃ y, x = l ^ j • y) →
      (∀ j (q : Over.mk (𝟙 (Sp k)) ⟶ B.X), q ^ (l ^ j) = 1 ↔ ∃ x, ev j x = q) →
      LinearMap.charpoly φ = GlobalTheory.AV.AbVar.charpoly (CategoryTheory.End.of f) := by
    intro k _ _ B f L _ _ _ φ l hl hlk ev hadd hequi hker him
    haveI : Fact l.Prime := ⟨hl⟩
    obtain ⟨e, he⟩ := pts_equiv k B
    obtain ⟨hfree, hfin, -⟩ := tl_free_finrank k l hlk B
    have hc : ∀ n : ℕ, Nat.card {x : B.Pt // x ^ (l ^ n) = 1} = l ^ (2 * B.dim * n) := by
      intro n
      rw [card_torsion_pt k B (l ^ n) (by push_cast; exact pow_ne_zero _ hlk), ← pow_mul, mul_comm n]
    let E : ℕ → L →+ Additive B.Pt := fun j =>
      AddMonoidHom.mk' (fun x => Additive.ofMul (e (ev j x))) fun x y => by
        rw [hadd, map_mul]; rfl
    have hE : ∀ j (n : ℕ) x, e (ev j (n • x)) = e (ev j x) ^ n := fun j n x =>
      congrArg Additive.toMul (map_nsmul (E j) n x)
    have key : ∀ j : ℕ, (LinearMap.charpoly φ).map (Int.castRingHom (ZMod (l ^ j))) =
        (LinearMap.charpoly (tend l B (CategoryTheory.End.of f))).map (PadicInt.toZModPow j) := by
      intro j
      haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ hl.ne_zero⟩
      let K := (powMonoidHom (l ^ j) : B.Pt →* B.Pt).ker
      have hK : ∀ x : B.Pt, x ∈ K ↔ x ^ (l ^ j) = 1 := fun x => MonoidHom.mem_ker
      letI : Module (ZMod (l ^ j)) (Additive K) := AddCommGroup.zmodModule fun x =>
        congrArg Additive.ofMul (Subtype.ext (by
          change ((Additive.toMul x : K) : B.Pt) ^ (l ^ j) = 1
          exact (hK _).1 (Additive.toMul x).2))
      have hsm : ∀ (c : ZMod (l ^ j)) (q : Additive K), c • q = c.val • q := fun c q => by
        conv_lhs => rw [← ZMod.natCast_zmod_val c]
        exact Nat.cast_smul_eq_nsmul _ _ _
      have hπ : ((l : ZMod (l ^ j))) ^ j = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
      let G0 : Additive K →+ Additive K := AddMonoidHom.mk'
        (fun q => Additive.ofMul ⟨((Additive.toMul q : K) : B.Pt) ≫ f.hom, (hK _).2 (by
          rw [← ptMap_apply, ← map_pow, (hK _).1 (Additive.toMul q).2, map_one])⟩)
        fun q q' => congrArg Additive.ofMul (Subtype.ext (MonObj.mul_comp _ _ _))
      let G : Additive K →ₗ[ZMod (l ^ j)] Additive K := G0.toZModLinearMap (l ^ j)
      let eL : L →+ Additive K := AddMonoidHom.mk'
        (fun x => Additive.ofMul ⟨e (ev j x), (hK _).2 (by
          rw [← hE, (hker j _).2 ⟨x, rfl⟩, map_one])⟩)
        fun x y => congrArg Additive.ofMul (Subtype.ext (by
          change e (ev j (x + y)) = e (ev j x) * e (ev j y)
          rw [hadd, map_mul]))
      let eT : Tate l B.Pt →+ Additive K := AddMonoidHom.mk'
        (fun t => Additive.ofMul ⟨t.lev j, (hK _).2 (t.lev_pow j)⟩) fun s t => rfl
      obtain ⟨_, _, h1⟩ := charpoly_reduce (Int.castRingHom (ZMod (l ^ j))) ZMod.intCast_surjective
        ((l : ℤ) ^ j) (by rw [map_pow, map_natCast, hπ]) eL
        (fun q => by
          obtain ⟨x, hx⟩ := (him j (e.symm (Additive.toMul q : K))).1 (by
            rw [← map_pow, (hK _).1 (Additive.toMul q).2, map_one])
          refine ⟨x, congrArg Additive.ofMul (Subtype.ext ?_)⟩
          change e (ev j x) = _
          rw [hx, MulEquiv.apply_symm_apply]
          rfl)
        (fun r x => by rw [map_zsmul, eq_intCast, Int.cast_smul_eq_zsmul])
        (fun x hx => by
          have h0 : e (ev j x) = 1 := congrArg Subtype.val (congrArg Additive.toMul hx)
          obtain ⟨y, hy⟩ := (hker j x).1 ((map_eq_one_iff e e.injective).1 h0)
          exact ⟨y, by rw [hy, ← Nat.cast_pow, natCast_zsmul]⟩)
        φ G (fun x => congrArg Additive.ofMul (Subtype.ext (by
          change e (ev j (φ x)) = e (ev j x) ≫ f.hom
          rw [hequi, he])))
      obtain ⟨_, _, h2⟩ := charpoly_reduce (PadicInt.toZModPow j) (ZMod.ringHom_surjective _)
        ((l : ℤ_[l]) ^ j) (by rw [map_pow, map_natCast, hπ]) eT
        (fun q => by
          obtain ⟨t, ht⟩ := tate_lev_surj B.Pt l (2 * B.dim) hc j _ ((hK _).1 (Additive.toMul q).2)
          exact ⟨t, congrArg Additive.ofMul (Subtype.ext ht)⟩)
        (fun a t => by
          rw [hsm]
          rfl)
        (fun t ht => by
          obtain ⟨s, hs⟩ := (tate_lev_eq_one_iff B.Pt l t j).1
            (congrArg Subtype.val (congrArg Additive.toMul ht))
          exact ⟨s, hs⟩)
        (tend l B (CategoryTheory.End.of f)) G (fun t => rfl)
      exact h1.symm.trans h2
    have hT : (GlobalTheory.AV.AbVar.charpoly (CategoryTheory.End.of f)).map (algebraMap ℤ ℤ_[l]) =
        (tend l B (CategoryTheory.End.of f)).charpoly := by
      apply Polynomial.map_injective (algebraMap ℤ_[l] ℚ_[l]) (IsFractionRing.injective ℤ_[l] ℚ_[l])
      rw [Polynomial.map_map, ← LinearMap.charpoly_baseChange]
      have hc : (algebraMap ℤ_[l] ℚ_[l]).comp (algebraMap ℤ ℤ_[l]) = algebraMap ℤ ℚ_[l] := Subsingleton.elim _ _
      rw [hc]
      haveI : Module.Finite ℚ_[l] (Vl l B) := (tl_free_finrank k l hlk B).2.2.2.1
      obtain ⟨⟨hm, hd, hev⟩, -⟩ := charpoly_spec k B (CategoryTheory.End.of f)
      have key := GlobalTheory.T.abelianVariety_degreePolynomial_map_eq_charpoly_rationalTate k l hlk B (CategoryTheory.End.of f)
        ((GlobalTheory.AV.AbVar.charpoly (CategoryTheory.End.of f)).map (algebraMap ℤ ℚ)) (hm.map _)
        (by rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (algebraMap ℤ ℚ)), hd])
        (fun n => by rw [Polynomial.eval_intCast_map, Int.cast_id, hev n]; simp)
      change (GlobalTheory.AV.AbVar.charpoly (CategoryTheory.End.of f)).map (algebraMap ℤ ℚ_[l]) = (vmap l f).charpoly
      rw [← key, Polynomial.map_map]
      congr 1
    have hinj : Function.Injective (Polynomial.map (Int.castRingHom ℤ_[l])) :=
      Polynomial.map_injective _ Int.cast_injective
    apply hinj
    rw [show Int.castRingHom ℤ_[l] = algebraMap ℤ ℤ_[l] from RingHom.ext_int _ _, hT]
    apply Polynomial.ext
    intro i
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    have h := congrArg (fun P => _root_.AddMonoidAlgebra.coeff (M := ℕ) P i) (key n)
    simp only [Polynomial.coeff_map, eq_intCast] at h ⊢
    rw [map_intCast]
    exact h
  have hch := charpoly_eq_lattice_model k B f L φ l hl hlk (fun j y => e.symm (ev j y))
    (fun j y z => by rw [h1, map_mul])
    (fun j y => e.injective (by rw [ea, e.apply_symm_apply, e.apply_symm_apply, h2]))
    (fun j y => by rw [map_eq_one_iff _ e.symm.injective]; exact h3 j y)
    (fun j q => by
      rw [← map_eq_one_iff e e.injective, map_pow, h4 j (e q)]
      exact exists_congr fun y => e.symm_apply_eq.symm)
  have hev := (charpoly_spec k B (CategoryTheory.End.of f)).1.2.2 0
  rw [← hch, LinearMap.eval_charpoly, map_zero, zero_sub, Int.cast_zero, zero_sub] at hev
  have hdet : (LinearMap.det (-φ)).natAbs = (LinearMap.det φ).natAbs := by
    rw [← neg_one_smul ℤ φ, LinearMap.det_smul, Int.natAbs_mul, Int.natAbs_pow]
    simp
  have hdeg : deg (A := B) (B := B) (-f) = (LinearMap.det φ).natAbs := by
    rw [← hdet, hev, Int.natAbs_natCast]
    rfl
  have hiso : IsIsogeny (A := B) (B := B) (-f) := by
    by_contra h
    rw [deg, if_neg h] at hdeg
    exact hφ (Int.natAbs_eq_zero.1 hdeg.symm)
  have hneg : ∀ (T : Over (Sp k)) (y : T ⟶ B.X), y ≫ Hom.hom (-f) = 1 ↔ y ≫ f.hom = 1 := fun T y => by
    rw [neg_hom, GrpObj.comp_inv, inv_eq_one]
  have hk := GlobalTheory.AV.DegSep.deg_eq_card_ker_of_killed k B B (-f) n (Nat.cast_ne_zero.2 hn) hiso fun T y hy => by
    apply (hbij T).1
    have h := hf T y
    rw [(hneg T y).1 hy, map_one] at h
    rw [map_pow, map_one, ← comp_pow_id_torscard, ← hu, ← Category.assoc, ← h, MonObj.one_comp]
  rw [← hdeg, hk]
  obtain ⟨e', he'⟩ := GlobalTheory.CharpolyLattice.pts_equiv k B
  refine Nat.card_congr (Equiv.subtypeEquiv (e.symm.trans e').toEquiv fun y => ?_)
  obtain ⟨y, rfl⟩ := e.surjective y
  change _ ↔ e' (e.symm (e y)) ≫ Hom.hom (-f) = 1
  rw [e.symm_apply_apply, hneg, ← he', ← ea, map_eq_one_iff e e.injective, map_eq_one_iff e' e'.injective]

section Loc

variable {p : ℕ} [Fact p.Prime] (D : Datum p)

def mulLa (c : 𝓞 D.F) : D.La →ₗ[ℤ] D.La :=
  (DistribSMul.toAddMonoidHom D.La (algebraMap (𝓞 D.F) D.O c)).toIntLinearMap

theorem exists_mul_eq_nat {F : Type} [Field F] [NumberField F] (c : 𝓞 F) (hc : c ≠ 0) :
    ∃ (c' : 𝓞 F) (n : ℕ), n ≠ 0 ∧ c' * c = n := by
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {c}))
  refine ⟨c', _, ?_, hc'⟩
  rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact hc

theorem natAbs_det_mulLa (w : Ideal (𝓞 D.F)) (hw : w.IsMaximal) (H : ℕ) (c : 𝓞 D.F) (hc : c ≠ 0)
    (hH : w ^ H = Ideal.span {c}) :
    letI := D.freeLa
    letI := D.finLa
    (LinearMap.det (mulLa D c)).natAbs = Nat.card (𝓞 D.F ⧸ w) ^ (H * (D.m * D.n)) := by
  letI := D.freeLa
  letI := D.finLa
  letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  have hinj : Function.Injective (mulLa D c) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨c', n, hn, h⟩ := exists_mul_eq_nat c hc
    have h1 : (n : ℤ) • y = 0 := by
      have h2 : (c' * c) • y = 0 := by
        rw [mul_smul]
        exact (congrArg (c' • ·) hy).trans (smul_zero _)
      rwa [h, Nat.cast_smul_eq_nsmul, ← natCast_zsmul] at h2
    exact (smul_eq_zero.1 h1).resolve_left (Int.natCast_ne_zero.2 hn)
  have h := Submodule.natAbs_det_equiv (LinearMap.range (mulLa D c)) (LinearEquiv.ofInjective _ hinj)
  have e : (LinearMap.range (mulLa D c)).subtype ∘ₗ AddMonoidHom.toIntLinearMap
      ((LinearEquiv.ofInjective _ hinj : D.La ≃ₗ[ℤ] LinearMap.range (mulLa D c)) :
        D.La →+ LinearMap.range (mulLa D c)) = mulLa D c := LinearMap.ext fun _ => rfl
  rw [e] at h
  obtain ⟨g, hgs, -, hgk⟩ := GlobalTheory.UPel.HT.EtLev.latQuot_free p D w H hw
  have hker : LinearMap.range (mulLa D c) = LinearMap.ker g.toIntLinearMap := by
    ext y
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    change _ ↔ g y = 0
    rw [hgk, ← GlobalTheory.UPel.HT.EtLev.mem_smul_top_iff_wSub, hH, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨z, hz⟩ => ⟨z, Submodule.mem_top, hz⟩, fun ⟨z, _, hz⟩ => ⟨z, hz⟩⟩
  rw [h, hker, Nat.card_congr (g.toIntLinearMap.quotKerEquivOfSurjective hgs).toEquiv, Nat.card_fun,
    Nat.card_fin, pow_mul _ H, ← Submodule.cardQuot_apply (w ^ H), ← Ideal.absNorm_apply, map_pow,
    Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem card_torsion_place {F : Type} [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M]
    (w : Ideal (𝓞 F)) (hmax : w.IsMaximal) (hne : w ≠ ⊥) (h : ℕ)
    (hdiv : ∀ c : 𝓞 F, c ≠ 0 → Function.Surjective (fun g : M => c • g))
    (hcount : ∀ (H : ℕ) (c : 𝓞 F), c ≠ 0 → w ^ H = Ideal.span {c} →
      Nat.card {g : M // c • g = 0} = Nat.card (𝓞 F ⧸ w) ^ (H * h)) :
    Nat.card (Submodule.torsionBySet (𝓞 F) M (w : Set (𝓞 F))) = Nat.card (𝓞 F ⧸ w) ^ h := by
  have hwnz : w ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero hne
  set H := orderOf (ClassGroup.mk0 ⟨w, hwnz⟩) with hH
  have hH0 : 0 < H := orderOf_pos _
  have hpowz : w ^ H ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hne)
  have hprin : Submodule.IsPrincipal (w ^ H) := by
    rw [← ClassGroup.mk0_eq_one_iff hpowz]
    have : (⟨w ^ H, hpowz⟩ : nonZeroDivisors (Ideal (𝓞 F))) = ⟨w, hwnz⟩ ^ H := rfl
    rw [this, map_pow, hH, pow_orderOf_eq_one]
  obtain ⟨c, hcgen⟩ := hprin.principal
  have hspan : w ^ H = Ideal.span {c} := hcgen
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at hspan
    exact pow_ne_zero _ hne hspan
  have hTH : Nat.card (Submodule.torsionBySet (𝓞 F) M ((w ^ H : Ideal (𝓞 F)) : Set (𝓞 F))) =
      Nat.card (𝓞 F ⧸ w) ^ (H * h) := by
    rw [← hcount H c hc0 hspan, hspan, Submodule.torsionBySet_span_singleton_eq]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g => Submodule.mem_torsionBy_iff c g)
  have hq : 1 < Nat.card (𝓞 F ⧸ w) := by
    have hfin : Finite (𝓞 F ⧸ w) := by
      apply Nat.finite_of_card_ne_zero
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ne, Ideal.absNorm_eq_zero_iff]
      exact hne
    letI := Ideal.Quotient.field w
    exact Finite.one_lt_card
  have hTHfin : Finite (Submodule.torsionBySet (𝓞 F) M ((w ^ H : Ideal (𝓞 F)) : Set (𝓞 F))) := by
    apply Nat.finite_of_card_ne_zero
    rw [hTH]
    exact pow_ne_zero _ (by omega)
  have hsub : Submodule.torsionBySet (𝓞 F) M (w : Set (𝓞 F)) ≤
      Submodule.torsionBySet (𝓞 F) M ((w ^ H : Ideal (𝓞 F)) : Set (𝓞 F)) :=
    Submodule.torsionBySet_le_torsionBySet_of_subset (Ideal.pow_le_self hH0.ne')
  have hT1fin : Finite (Submodule.torsionBySet (𝓞 F) M (w : Set (𝓞 F))) :=
    Finite.of_injective _ (Submodule.inclusion_injective hsub)
  letI := Ideal.Quotient.field w
  haveI : Module.Finite (𝓞 F ⧸ w) (Submodule.torsionBySet (𝓞 F) M (w : Set (𝓞 F))) :=
    Module.Finite.of_finite
  set h' := Module.finrank (𝓞 F ⧸ w) (Submodule.torsionBySet (𝓞 F) M (w : Set (𝓞 F))) with hh'
  have hT1 : Nat.card (Submodule.torsionBySet (𝓞 F) M (w : Set (𝓞 F))) =
      Nat.card (𝓞 F ⧸ w) ^ h' := Module.natCard_eq_pow_finrank
  have hall := GlobalTheory.torsion_pow_card F M w h' hmax hne hdiv hT1 H
  rw [hTH] at hall
  have he : H * h = H * h' := Nat.pow_right_injective hq hall
  rw [hT1, Nat.eq_of_mul_eq_mul_left hH0 he]

theorem exists_lev_of_card (G : Type) [CommGroup G] (act : D.O → G → G)
    (hmul : ∀ b g h, act b (g * h) = act b g * act b h) (hone : ∀ g, act 1 g = g)
    (hcomp : ∀ b c g, act (b * c) g = act b (act c g)) (hadd : ∀ b c g, act (b + c) g = act b g * act c g)
    (hdiv : ∀ n : ℕ, 0 < n → ∀ g : G, ∃ g' : G, g' ^ n = g)
    (hcount : letI := D.freeLa
      letI := D.finLa
      ∀ c : 𝓞 D.F, c ≠ 0 → LinearMap.det (mulLa D c) ≠ 0 →
        Nat.card {g : G // act (algebraMap (𝓞 D.F) D.O c) g = 1} = (LinearMap.det (mulLa D c)).natAbs) (e : ℕ) :
    ∃ ev : D.La → G, (∀ y z, ev (y + z) = ev y * ev z) ∧ (∀ (c : D.O) y, ev (c • y) = act c (ev y)) ∧
      (∀ y, ev y = 1 ↔ ∃ z, y = p ^ e • z) ∧ (∀ q : G, q ^ (p ^ e) = 1 ↔ ∃ y, ev y = q) := by
  letI : Module D.O (Additive G) := GlobalTheory.EtLevMorita.actModule act hmul hone hcomp hadd
  letI : Module (𝓞 D.F) (Additive G) := Module.compHom (Additive G) (algebraMap (𝓞 D.F) D.O)
  haveI : IsScalarTower (𝓞 D.F) D.O (Additive G) := ⟨fun c b x => by
    show (c • b) • x = algebraMap (𝓞 D.F) D.O c • (b • x)
    rw [Algebra.smul_def, mul_smul]⟩
  letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  haveI : IsScalarTower (𝓞 D.F) D.O D.La := ⟨fun c b x => by
    show (c • b) • x = algebraMap (𝓞 D.F) D.O c • (b • x)
    rw [Algebra.smul_def, mul_smul]⟩
  have hp0 : ((p : ℕ) : 𝓞 D.F) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hdiv' : ∀ c : 𝓞 D.F, c ≠ 0 → Function.Surjective (fun g : Additive G => c • g) := by
    intro c hc g
    obtain ⟨c', n, hn, h⟩ := exists_mul_eq_nat c hc
    obtain ⟨g', hg'⟩ := hdiv n (Nat.pos_of_ne_zero hn) g.toMul
    refine ⟨c' • Additive.ofMul g', ?_⟩
    show c • c' • Additive.ofMul g' = g
    rw [smul_smul, mul_comm, h, Nat.cast_smul_eq_nsmul, ← ofMul_pow, hg']
    rfl
  have hloc : ∀ w : Ideal (𝓞 D.F), w.IsMaximal → ((p : ℕ) : 𝓞 D.F) ∈ w → ∀ r,
      HasLev D.O D.La (Additive G) (w ^ r) := by
    intro w hw hpw r
    have hne : w ≠ ⊥ := fun h0 => hp0 (by rwa [h0, Ideal.mem_bot] at hpw)
    have hq : Nat.card (𝓞 D.F ⧸ w) ≠ 0 := by
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ne, Ideal.absNorm_eq_zero_iff]
      exact hne
    have h1 := card_torsion_place (Additive G) w hw hne (D.m * D.n) hdiv' fun H c hc hH => by
      have hd := natAbs_det_mulLa D w hw H c hc hH
      rw [← hd, ← hcount c hc (Int.natAbs_ne_zero.1 (by rw [hd]; exact pow_ne_zero _ hq))]
      rfl
    have hall := GlobalTheory.torsion_pow_card D.F _ w (D.m * D.n) hw hne hdiv' h1
    obtain ⟨f, hf1, hf2, hf3⟩ := GlobalTheory.torsionBySet_pow_free_of_natCard D.F _ w (D.m * D.n) r hw hne hall
    obtain ⟨l, l1, l2, l3, l4⟩ := GlobalTheory.EtLevMorita.exists_lev p D w r hw hpw G act hmul hone hcomp hadd
      (fun a => (f a).toMul) (fun a a' => by rw [map_add (f := _)]; rfl) (fun c a => by rw [hf1]; rfl)
      (fun a a' h => hf2 h) (fun g hg => hf3 (Additive.ofMul g) hg)
    refine ⟨{ toFun := fun y => Additive.ofMul (l y)
              map_add' := fun y z => congrArg Additive.ofMul (l1 y z)
              map_smul' := fun b y => congrArg Additive.ofMul (l2 b y) }, fun y => ?_, fun g hg => l4 g.toMul hg⟩
    rw [GlobalTheory.UPel.HT.EtLev.mem_smul_top_iff_wSub]
    exact l3 y
  obtain ⟨l, l1, l2⟩ := hasLev_of_prime_pow (O := D.O) (L := D.La) (M := Additive G) _ hp0 e hloc
    (Ideal.span {((p : ℕ) : 𝓞 D.F) ^ e}) (Ideal.mem_span_singleton_self _)
  have hk : ∀ y, l y = 0 ↔ ∃ z, y = p ^ e • z := fun y => by
    rw [l1, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    simp only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact ⟨fun ⟨z, _, hz⟩ => ⟨z, hz.symm⟩, fun ⟨z, hz⟩ => ⟨z, Submodule.mem_top, hz.symm⟩⟩
  refine ⟨fun y => (l y).toMul, fun y z => congrArg Additive.toMul (l.map_add y z),
    fun c y => congrArg Additive.toMul (l.map_smul c y), hk,
    fun q => ⟨fun hq => l2 (Additive.ofMul q) fun c hc => ?_, ?_⟩⟩
  · obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hc
    rw [mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, ← ofMul_pow, hq, ofMul_one, smul_zero]
  · rintro ⟨y, rfl⟩
    rw [← toMul_nsmul, ← map_nsmul, (hk _).2 ⟨y, rfl⟩, toMul_zero]

end Loc

theorem act_natCast {O : Type} [Ring O] {S : Scheme.{0}} {G : Over S} [GrpObj G] (act : OActN O G) (n : ℕ) :
    act.act (n : O) = (𝟙 G) ^ n := by
  induction n with
  | zero =>
    have h := act.add 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, pow_zero]
    exact mul_eq_left.mp h.symm
  | succ n ih => rw [Nat.cast_succ, act.add, ih, act.one, pow_succ]

theorem exists_ev_pow : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → ∀ e : ℕ, ∃ ev : D.La → (Over.mk x ⟶ o.A), (∀ y z, ev (y + z) = ev y * ev z) ∧ (∀ (c : D.O) y, ev (c • y) = ev y ≫ o.act.act c) ∧ (∀ y, ev y = 1 ↔ ∃ z, y = p ^ e • z) ∧ (∀ (q : Over.mk x ⟶ o.A), q ^ (p ^ e) = 1 ↔ ∃ y, ev y = q) := by
  intro p _ D R _ b N _ _ S s o k _ _ _ x β hx e
  letI : CommGroup (Over.mk x ⟶ o.A) := Hom.commGroup
  letI := D.freeLa
  letI := D.finLa
  refine exists_lev_of_card D (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun c g h => by haveI := o.act.hom c; exact MonObj.mul_comp _ _ _)
    (fun g => by simp only [o.act.one, Category.comp_id])
    (fun c d g => by simp only [o.act.mul, Category.assoc])
    (fun c d g => by simp only [o.act.add]; exact MonObj.comp_mul _ _ _)
    (fun n hn g => GlobalTheory.AbDivPt.exists_pow_eq_of_isAlgClosed S o.A o.ab k x n hn g) (fun c hc hd => ?_) e
  obtain ⟨I, -⟩ := o.geom k x β hx
  obtain ⟨l, hl1, hl⟩ := Nat.exists_infinite_primes (p + 1)
  have hco : ∀ j, (l ^ j).Coprime p := fun j =>
    Nat.Coprime.pow_left j ((Nat.coprime_primes hl Fact.out).2 (by omega))
  obtain ⟨c', n, hn, h⟩ := exists_mul_eq_nat c hc
  haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
  haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c')
  exact card_ker_eq_det o.A o.ab k x (o.act.act (algebraMap (𝓞 D.F) D.O c))
    (o.act.act (algebraMap (𝓞 D.F) D.O c')) n hn
    (by rw [← o.act.mul, ← map_mul, h, map_natCast, act_natCast]) D.La (mulLa D c) hd l hl
    (fun j => I.ev (l ^ j)) (fun j => I.add _) (fun j y => I.lin _ _ y)
    (fun j => I.ker _ (pow_pos hl.pos j) (hco j)) (fun j => I.onto _ (pow_pos hl.pos j) (hco j))

end GlobalTheory.UPel.HT.PTors
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_evaluation_hom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → ∀ e : ℕ, ∃ ev : D.La → (Over.mk x ⟶ o.A), (∀ y z, ev (y + z) = ev y * ev z) ∧ (∀ (c : D.O) y, ev (c • y) = ev y ≫ o.act.act c) ∧ (∀ y, ev y = 1 ↔ ∃ z, y = p ^ e • z) ∧ (∀ (q : Over.mk x ⟶ o.A), q ^ (p ^ e) = 1 ↔ ∃ y, ev y = q) := by
  first | (exact @GlobalTheory.UPel.HT.PTors.exists_ev_pow) | (exact GlobalTheory.UPel.HT.PTors.exists_ev_pow) | (intros; apply GlobalTheory.UPel.HT.PTors.exists_ev_pow  <;> assumption)
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

noncomputable section

namespace GlobalTheory.UPel.HT.PadicTate

theorem exists_padic_similitude : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → ∃ (ζ : ℕ → kˣ) (ev : ℕ → D.La → (Over.mk x ⟶ o.A)), (∀ e, IsPrimitiveRoot (ζ e) (p ^ e)) ∧ (∀ e, ζ (e + 1) ^ p = ζ e) ∧ (∀ e y z, ev e (y + z) = ev e y * ev e z) ∧ (∀ e (c : D.O) y, ev e (c • y) = ev e y ≫ o.act.act c) ∧ (∀ e y, ev e y = 1 ↔ ∃ z, y = p ^ e • z) ∧ (∀ e (q : Over.mk x ⟶ o.A), q ^ (p ^ e) = 1 ↔ ∃ y, ev e y = q) ∧ (∀ e y, ev (e + 1) y ^ p = ev e y) ∧ (∀ e y z, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (p ^ e) (ev e y) (ev e z) (unitOn (ζ e ^ (2 * D.EF y z)))) := by
  intro p _ D R _ b N hN3 hN S s o k _ _ _ x β hβ
  have hp : p.Prime := Fact.out
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hB : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ o.ab o.ab
  have ub := GlobalTheory.Ex.Specialise.unitOn_bijective (R := k)
  let Q := Over.mk x ⟶ o.A
  let act : D.O → Q → Q := fun c g => g ≫ o.act.act c
  let E : ℕ → Q → Q → kˣ → Prop := fun n g g' z =>
    Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)
  have amul : ∀ c a b, act c (a * b) = act c a * act c b := fun c a b => by
    haveI := o.act.hom c
    exact MonObj.mul_comp _ _ _
  have apow : ∀ c (a : Q) n, a ^ n = 1 → act c a ^ n = 1 := fun c a n h => by
    haveI := o.act.hom c
    show (a ≫ _) ^ n = 1
    rw [← MonObj.pow_comp, h, MonObj.one_comp]
  have powl : ∀ (n : ℕ) (a b : Q), (lift a b) ^ n = lift (a ^ n) (b ^ n) := by
    intro n a b
    ext <;> simp [MonObj.pow_comp]
  have ex : ∀ (n : ℕ) (a b : Q), ∃ c : kˣ, 0 < n → a ^ n = 1 → b ^ n = 1 →
      Out.WeilIs (G2 o.A) o.P n (lift a 1) (lift 1 b) (unitOn c) := fun n a b => by
    by_cases h : 0 < n ∧ a ^ n = 1 ∧ b ^ n = 1
    · obtain ⟨c, -, hc⟩ := GlobalTheory.ProdPairing.exists_weilIs_prod_root S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.ample n h.1 _
        (lift a 1) (lift 1 b) (by rw [powl, h.2.1, one_pow]; ext <;> simp) (by rw [powl, h.2.2, one_pow]; ext <;> simp)
      obtain ⟨c, rfl⟩ := ub.2 c
      exact ⟨c, fun _ _ _ => hc⟩
    · exact ⟨1, fun h₁ h₂ h₃ => absurd ⟨h₁, h₂, h₃⟩ h⟩
  choose W hW using ex
  have uq : ∀ {n : ℤ} {X Y : Over.mk x ⟶ G2 o.A} {c c' : kˣ}, Out.WeilIs (G2 o.A) o.P n X Y (unitOn c) →
      Out.WeilIs (G2 o.A) o.P n X Y (unitOn c') → c = c' := fun h h' =>
    ub.1 (CommutatorPairing.weilIs_unique hG hB o.isLB h h')
  have upow : ∀ (c : kˣ) (m : ℕ), unitOn (c ^ m) = unitOn c ^ m := fun c m => map_pow _ _ _
  have umul : ∀ c c' : kˣ, unitOn (c * c') = unitOn c * unitOn c' := fun c m => map_mul _ _ _
  have uone : unitOn (1 : kˣ) = 1 := map_one _
  have hE : ∀ n, 0 < n → ∀ a b : Q, a ^ n = 1 → b ^ n = 1 → E n a b (W n a b ^ 2) := fun n hn a b ha hb => by
    have h := GlobalTheory.DiagSqAxes.weilIs_diag_sq S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.symm k x n hn
      (Nat.cast_ne_zero.2 hn.ne') a b ha hb _ (hW n a b hn ha hb)
    rw [← upow] at h
    exact h
  have lev : ∀ n m, 0 < n → 0 < m → ∀ a b : Q, a ^ (n * m) = 1 → b ^ (n * m) = 1 →
      W n (a ^ m) (b ^ m) = W (n * m) a b ^ m := fun n m hn hm a b ha hb => by
    have h := GlobalTheory.LevelChangePairing.weilIs_levelChange S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ k x n m hn hm
      (Nat.cast_ne_zero.2 (Nat.mul_pos hn hm).ne') a b ha hb _ (hW (n * m) a b (Nat.mul_pos hn hm) ha hb)
    rw [← upow] at h
    exact uq (hW n _ _ hn (by rw [← pow_mul, mul_comm, ha]) (by rw [← pow_mul, mul_comm, hb])) h
  have wmul : ∀ n, 0 < n → ∀ a a' b : Q, a ^ n = 1 → a' ^ n = 1 → b ^ n = 1 →
      W n (a * a') b = W n a b * W n a' b := fun n hn a a' b ha ha' hb => by
    have h := GlobalTheory.SiegelTypings.weilIs_mul hB o.isLB (hW n a b hn ha hb) (hW n a' b hn ha' hb)
    have e : lift a (1 : Q) * lift a' 1 = lift (a * a') 1 := by ext <;> simp [MonObj.mul_comp]
    rw [← umul, e] at h
    exact uq (hW n _ _ hn (by rw [mul_pow, ha, ha', _root_.mul_one]) hb) h
  have wskew : ∀ n, 0 < n → ∀ a b : Q, a ^ n = 1 → b ^ n = 1 → W n a b * W n b a = 1 := fun n hn a b ha hb => by
    have h := GlobalTheory.SwapPairing.weilIs_swap_eq S o.A o.P o.ab o.isLB o.symm n _ a b _ _
      (CommPairing.weilIs_symm o.isLB (hW n b a hn hb ha)) (hW n a b hn ha hb)
    apply ub.1
    rw [umul, ← h, uone, inv_mul_cancel]
  have wadj : ∀ n, 0 < n → ∀ (c : D.O) (a b : Q), a ^ n = 1 → b ^ n = 1 →
      W n (act c a) b = W n a (act (D.star c).unop b) := fun n hn c a b ha hb =>
    ub.1 (GlobalTheory.AdjPairing.weilIs_adj_eq S o.A o.P o.ab o.isLB _ _ (o.act.hom c) (o.act.hom _) (o.rosati c) n _ a b _ _
      (hW n _ b hn (apow c a n ha) hb) (hW n a _ hn ha (apow _ b n hb)))
  have wnd : ∀ r, ∀ a : Q, a ^ (p ^ r) = 1 → (∀ b : Q, b ^ (p ^ r) = 1 → W (p ^ r) a b = 1) → a = 1 := by
    intro r a ha h
    have hq : 0 < p ^ r := pow_pos hp.pos r
    obtain ⟨e, he, hk⟩ := o.kerP
    have h1 := hk _ a (GlobalTheory.WeilKernel.triv_slice_of_forall_weilIs_one S o.A o.P o.ab o.isLB o.rig₁ o.rig₂ k x (p ^ r) (Nat.cast_ne_zero.2 hq.ne') a ha
      fun b hb => by
        have := hW _ a b hq ha hb
        rwa [h b hb, uone] at this)
    have h2 := pow_gcd_eq_one.2 ⟨h1, ha⟩
    rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right r he), pow_one] at h2
  obtain ⟨ζ, hζ, hζ'⟩ := GlobalTheory.T.exists_compatible_prime_power_roots p k
  obtain ⟨ev, hev, hev'⟩ := GlobalTheory.T.exists_compatible_similitude_level_tower p D k Q act (fun r => W (p ^ r)) ζ amul hζ'
    (fun r a b ha hb => lev (p ^ r) p (pow_pos hp.pos r) hp.pos a b ha hb) fun r => by
      obtain ⟨f, hf⟩ := GlobalTheory.T.exists_level_evaluation_hom p D R b N hN3 hN S s o k x β hβ r
      have hq : 0 < p ^ r := pow_pos hp.pos r
      exact GlobalTheory.T.exists_level_pairing_eq_alt p D k Q act r (W (p ^ r)) (ζ r) (hζ r) (wmul _ hq) (wskew _ hq) (wadj _ hq) (wnd r) f hf
  refine ⟨ζ, ev, hζ, hζ', fun r => (hev r).1.1, fun r => (hev r).1.2.1, fun r => (hev r).1.2.2.1,
    fun r => (hev r).1.2.2.2, hev', fun r y z => ?_⟩
  have hq : 0 < p ^ r := pow_pos hp.pos r
  have h := hE _ hq (ev r y) (ev r z) (((hev r).1.2.2.2 _).2 ⟨y, rfl⟩) (((hev r).1.2.2.2 _).2 ⟨z, rfl⟩)
  have e := (hev r).2 y z
  rw [e, ← zpow_natCast, ← zpow_mul, mul_comm] at h
  simp only [E, Nat.cast_pow] at h
  exact h

end GlobalTheory.UPel.HT.PadicTate
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_roots_and_evaluation : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → ∃ (ζ : ℕ → kˣ) (ev : ℕ → D.La → (Over.mk x ⟶ o.A)), (∀ e, IsPrimitiveRoot (ζ e) (p ^ e)) ∧ (∀ e, ζ (e + 1) ^ p = ζ e) ∧ (∀ e y z, ev e (y + z) = ev e y * ev e z) ∧ (∀ e (c : D.O) y, ev e (c • y) = ev e y ≫ o.act.act c) ∧ (∀ e y, ev e y = 1 ↔ ∃ z, y = p ^ e • z) ∧ (∀ e (q : Over.mk x ⟶ o.A), q ^ (p ^ e) = 1 ↔ ∃ y, ev e y = q) ∧ (∀ e y, ev (e + 1) y ^ p = ev e y) ∧ (∀ e y z, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (p ^ e) (ev e y) (ev e z) (unitOn (ζ e ^ (2 * D.EF y z)))) := by
  first | (exact @GlobalTheory.UPel.HT.PadicTate.exists_padic_similitude) | (exact GlobalTheory.UPel.HT.PadicTate.exists_padic_similitude) | (intros; apply GlobalTheory.UPel.HT.PadicTate.exists_padic_similitude <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleRootsEvaluationInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicSectionOfAnalytic
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace GlobalTheory.UPel.HT.GTateGlue

section Grp

variable {G : Type} [CommGroup G]

theorem bezout {a b : ℕ} (h : a.Coprime b) : (a : ℤ) * Nat.gcdA a b + b * Nat.gcdB a b = 1 := by
  rw [← Nat.gcd_eq_gcd_ab, h.gcd_eq_one, Nat.cast_one]

theorem ext_pow {a b : ℕ} (h : a.Coprime b) {q r : G} (ha : q ^ a = r ^ a) (hb : q ^ b = r ^ b) : q = r := by
  have e : ∀ t : G, t = (t ^ a) ^ Nat.gcdA a b * (t ^ b) ^ Nat.gcdB a b := fun t => by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, bezout h, zpow_one]
  rw [e q, ha, hb, ← e r]

def crt (a b : ℕ) (x y : G) : G := x ^ Nat.gcdB a b * y ^ Nat.gcdA a b

theorem crt_mul (a b : ℕ) (x y x' y' : G) : crt a b (x * x') (y * y') = crt a b x y * crt a b x' y' := by
  simp only [crt, mul_zpow]
  exact mul_mul_mul_comm _ _ _ _

theorem crt_pow_right {a b : ℕ} (h : a.Coprime b) {x y : G} (hx : x ^ a = 1) (hy : y ^ b = 1) :
    crt a b x y ^ b = x := by
  have e : Nat.gcdB a b * (b : ℤ) = 1 + a * (-Nat.gcdA a b) := by linear_combination bezout h
  rw [crt, mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, e, mul_comm (Nat.gcdA a b), zpow_add,
    zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hx, hy, one_zpow, one_zpow, zpow_one, _root_.mul_one,
    _root_.mul_one]

theorem crt_pow_left {a b : ℕ} (h : a.Coprime b) {x y : G} (hx : x ^ a = 1) (hy : y ^ b = 1) :
    crt a b x y ^ a = y := by
  have e : Nat.gcdA a b * (a : ℤ) = 1 + b * (-Nat.gcdB a b) := by linear_combination bezout h
  rw [crt, mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, e, mul_comm (Nat.gcdB a b), zpow_add,
    zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hx, hy, one_zpow, one_zpow, zpow_one, _root_.mul_one,
    _root_.one_mul]

variable (p : ℕ) [hp : Fact p.Prime]

def cp (n : ℕ) : ℕ := n / p ^ n.factorization p

theorem cp_mul_pow (n : ℕ) : cp p n * p ^ n.factorization p = n := by
  rw [mul_comm]; exact Nat.ordProj_mul_ordCompl_eq_self n p

theorem cp_pos {n : ℕ} (hn : 0 < n) : 0 < cp p n := Nat.ordCompl_pos p hn.ne'

theorem cp_coprime {n : ℕ} (hn : 0 < n) : (cp p n).Coprime p := (Nat.coprime_ordCompl hp.out hn.ne').symm

theorem cp_coprime_pow {n : ℕ} (hn : 0 < n) : (cp p n).Coprime (p ^ n.factorization p) :=
  (cp_coprime p hn).pow_right _

theorem cp_mul (n m : ℕ) : cp p (n * m) = cp p n * cp p m := Nat.ordCompl_mul n m p

def sys (f g : ℕ → G) (n : ℕ) : G := crt (cp p n) (p ^ n.factorization p) (f (cp p n)) (g (n.factorization p))

variable {p} {f g : ℕ → G} (hf : ∀ n, 0 < n → n.Coprime p → f n ^ n = 1) (hg : ∀ e, g e ^ p ^ e = 1)

include hf hg in
theorem sys_right {n : ℕ} (hn : 0 < n) : sys p f g n ^ p ^ n.factorization p = f (cp p n) :=
  crt_pow_right (cp_coprime_pow p hn) (hf _ (cp_pos p hn) (cp_coprime p hn)) (hg _)

include hf hg in
theorem sys_left {n : ℕ} (hn : 0 < n) : sys p f g n ^ cp p n = g (n.factorization p) :=
  crt_pow_left (cp_coprime_pow p hn) (hf _ (cp_pos p hn) (cp_coprime p hn)) (hg _)

include hf hg in
theorem sys_tower (hf' : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → f (n * m) ^ m = f n)
    (hg' : ∀ e, g (e + 1) ^ p = g e) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    sys p f g (n * m) ^ m = sys p f g n := by
  have hg'' : ∀ e d, g (e + d) ^ p ^ d = g e := fun e d => by
    induction d with
    | zero => simp
    | succ d ih => rw [pow_succ', pow_mul, ← add_assoc, hg', ih]
  have hnm : 0 < n * m := Nat.mul_pos hn hm
  have ef : (n * m).factorization p = n.factorization p + m.factorization p := by
    rw [Nat.factorization_mul hn.ne' hm.ne']; rfl
  have r := sys_right hf hg hnm
  have l := sys_left hf hg hnm
  refine ext_pow (cp_coprime_pow p hn) ?_ ?_
  · have e : m * cp p n = cp p (n * m) * p ^ m.factorization p := by
      rw [cp_mul, _root_.mul_assoc, cp_mul_pow, mul_comm]
    rw [← pow_mul, e, pow_mul, l, ef, hg'', sys_left hf hg hn]
  · have e : m * p ^ n.factorization p = p ^ (n * m).factorization p * cp p m := by
      rw [ef, pow_add, _root_.mul_assoc, mul_comm _ (cp p m), cp_mul_pow, mul_comm]
    rw [← pow_mul, e, pow_mul, r, cp_mul, hf' _ _ (cp_pos p hn) (cp_pos p hm)
      (Nat.Coprime.mul_left (cp_coprime p hn) (cp_coprime p hm)), sys_right hf hg hn]

include hf hg in
theorem sys_of_coprime {n : ℕ} (hn : 0 < n) (h : n.Coprime p) : sys p f g n = f n := by
  have e : n.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp.out).1 h.symm)
  have r := sys_right hf hg hn
  rwa [cp, e, pow_zero, pow_one, Nat.div_one] at r

end Grp

theorem exists_gTateIso {p : ℕ} [Fact p.Prime] (D : Datum p) {k : Type} [Field k] {Q : Type} [CommGroup Q]
    (act : D.O → Q → Q) (hact : ∀ c q r, act c (q * r) = act c q * act c r) (W : ℕ → Q → Q → kˣ → Prop)
    (hW : ∀ (a b : ℕ) (q r : Q) (c : kˣ), 0 < a → 0 < b → a.Coprime b → q ^ (a * b) = 1 → r ^ (a * b) = 1 →
      W a (q ^ b) (r ^ b) (c ^ b) → W b (q ^ a) (r ^ a) (c ^ a) → W (a * b) q r c)
    (I : TateIsoO D k Q act W) (ζ : ℕ → kˣ) (ev : ℕ → D.La → Q)
    (h₁ : ∀ e, IsPrimitiveRoot (ζ e) (p ^ e)) (h₂ : ∀ e, ζ (e + 1) ^ p = ζ e)
    (h₃ : ∀ e y z, ev e (y + z) = ev e y * ev e z) (h₄ : ∀ e (c : D.O) y, ev e (c • y) = act c (ev e y))
    (h₅ : ∀ e y, ev e y = 1 ↔ ∃ z, y = p ^ e • z) (h₆ : ∀ e (q : Q), q ^ (p ^ e) = 1 ↔ ∃ y, ev e y = q)
    (h₇ : ∀ e y, ev (e + 1) y ^ p = ev e y)
    (h₈ : ∀ e y z, W (p ^ e) (ev e y) (ev e z) (ζ e ^ (2 * D.EF y z))) :
    ∃ J : GTateIso D.toG k Q act W, ∀ n, 0 < n → n.Coprime p → ∀ y, J.ev n y = I.ev n y := by
  have zf : ∀ n, 0 < n → n.Coprime p → I.ζ n ^ n = 1 := fun n a b => (I.ζ_prim n a b).pow_eq_one
  have zg : ∀ e, ζ e ^ p ^ e = 1 := fun e => (h₁ e).pow_eq_one
  have ef : ∀ y n, 0 < n → n.Coprime p → I.ev n y ^ n = 1 := fun y n a b => (I.onto n a b _).2 ⟨y, rfl⟩
  have eg : ∀ y e, ev e y ^ p ^ e = 1 := fun y e => (h₆ e _).2 ⟨y, rfl⟩
  let E : ℕ → D.La → Q := fun n y => sys p (fun m => I.ev m y) (fun e => ev e y) n
  have ER : ∀ n, 0 < n → ∀ y, E n y ^ p ^ n.factorization p = I.ev (cp p n) y := fun n hn y =>
    sys_right (ef y) (eg y) hn
  have EL : ∀ n, 0 < n → ∀ y, E n y ^ cp p n = ev (n.factorization p) y := fun n hn y =>
    sys_left (ef y) (eg y) hn
  have tors : ∀ n, 0 < n → ∀ y, E n y ^ (cp p n * p ^ n.factorization p) = 1 := fun n hn y => by
    rw [pow_mul, EL n hn, eg]
  refine ⟨{ ζ := sys p I.ζ ζ
            ζ_prim := fun n hn => ⟨?_, fun l hl => ?_⟩
            ζ_pow := fun n m hn hm => sys_tower zf zg I.ζ_pow h₂ hn hm
            ev := E
            add := fun n (y z : D.La) => ?_
            lin := fun n (c : D.O) (y : D.La) => ?_
            ker := fun n hn (y : D.La) => ⟨fun h => ?_, ?_⟩
            onto := fun n hn q => ⟨fun h => ?_, ?_⟩
            tower := fun n m hn hm y =>
              sys_tower (ef y) (eg y) (fun a b ha hb hab => I.tower a b ha hb hab y) (fun e => h₇ e y) hn hm
            isom := fun n hn (y z : D.La) => ?_ },
    fun n hn h y => sys_of_coprime (ef y) (eg y) hn h⟩
  · have e : sys p I.ζ ζ n ^ (cp p n * p ^ n.factorization p) = 1 := by rw [pow_mul, sys_left zf zg hn, zg]
    rwa [cp_mul_pow] at e
  · have a := (I.ζ_prim _ (cp_pos p hn) (cp_coprime p hn)).dvd_of_pow_eq_one l (by
      rw [← sys_right zf zg hn, pow_right_comm, hl, one_pow])
    have b := (h₁ (n.factorization p)).dvd_of_pow_eq_one l (by
      rw [← sys_left zf zg hn, pow_right_comm, hl, one_pow])
    have := (cp_coprime_pow p hn).mul_dvd_of_dvd_of_dvd a b
    rwa [cp_mul_pow] at this
  · exact (congrArg₂ (crt _ _) (I.add _ y z) (h₃ _ y z)).trans (crt_mul _ _ _ _ _ _)
  · refine (congrArg₂ (crt _ _) (I.lin _ c y) (h₄ _ c y)).trans ?_
    let φ : Q →* Q := MonoidHom.mk' (act c) (hact c)
    show φ _ ^ _ * φ _ ^ _ = φ (_ ^ _ * _ ^ _)
    rw [map_mul, map_zpow, map_zpow]
  · obtain ⟨z₁, e₁⟩ := (I.ker _ (cp_pos p hn) (cp_coprime p hn) y).1 (by rw [← ER n hn, h, one_pow])
    obtain ⟨z₂, e₂⟩ := (h₅ (n.factorization p) y).1 (by rw [← EL n hn, h, one_pow])
    have bz := bezout (cp_coprime_pow p hn)
    have en := cp_mul_pow p n
    generalize cp p n = a at *
    generalize p ^ n.factorization p = b at *
    refine ⟨(Nat.gcdB a b • z₁ + Nat.gcdA a b • z₂ : D.La), ?_⟩
    show y = n • (Nat.gcdB a b • z₁ + Nat.gcdA a b • z₂ : D.La)
    calc y = ((a : ℤ) * Nat.gcdA a b) • y + ((b : ℤ) * Nat.gcdB a b) • y := by rw [← add_smul, bz, one_smul]
      _ = ((a : ℤ) * Nat.gcdA a b) • (b • z₂) + ((b : ℤ) * Nat.gcdB a b) • (a • z₁) := by rw [← e₁, ← e₂]
      _ = _ := by rw [← en]; module
  · rintro (⟨z, hz⟩ : ∃ z : D.La, y = n • z)
    have hz' : y = (cp p n * p ^ n.factorization p) • z := by rw [cp_mul_pow]; exact hz
    refine ext_pow (cp_coprime_pow p hn) ?_ ?_
    · rw [EL n hn, one_pow]
      exact (h₅ _ _).2 ⟨cp p n • (z : D.La), by rw [hz', mul_comm, mul_smul]⟩
    · rw [ER n hn, one_pow]
      exact (I.ker _ (cp_pos p hn) (cp_coprime p hn) _).2 ⟨p ^ n.factorization p • (z : D.La), by rw [hz', mul_smul]⟩
  · obtain ⟨y₁, e₁⟩ := (I.onto _ (cp_pos p hn) (cp_coprime p hn) (q ^ p ^ n.factorization p)).1 (by
      rw [← pow_mul, mul_comm, cp_mul_pow, h])
    obtain ⟨y₂, e₂⟩ := (h₆ (n.factorization p) (q ^ cp p n)).1 (by rw [← pow_mul, cp_mul_pow, h])
    have bz := bezout (cp_coprime_pow p hn)
    refine ⟨(y₁ + cp p n • Nat.gcdA (cp p n) (p ^ n.factorization p) • (y₂ - y₁) : D.La),
      ext_pow (cp_coprime_pow p hn) ?_ ?_⟩
    · have e : y₁ + cp p n • Nat.gcdA (cp p n) (p ^ n.factorization p) • (y₂ - y₁) =
          y₂ + p ^ n.factorization p • Nat.gcdB (cp p n) (p ^ n.factorization p) • (y₁ - y₂) := by
        generalize cp p n = a at *
        generalize p ^ n.factorization p = b at *
        linear_combination (norm := module) bz • (y₂ - y₁)
      rw [EL n hn, e, h₃, e₂, (h₅ _ _).2 ⟨_, rfl⟩, _root_.mul_one]
    · rw [ER n hn, I.add, e₁, (I.ker _ (cp_pos p hn) (cp_coprime p hn) _).2 ⟨_, rfl⟩, _root_.mul_one]
  · rintro ⟨y, rfl⟩
    have := tors n hn y
    rwa [cp_mul_pow] at this
  · have sw : ∀ (u : kˣ) (t : ℤ) (j : ℕ), (u ^ t) ^ j = (u ^ j) ^ t := fun u t j => by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    have := hW (cp p n) (p ^ n.factorization p) (E n y) (E n z) (sys p I.ζ ζ n ^ (2 * D.EF y z)) (cp_pos p hn)
      (pow_pos (Fact.out : p.Prime).pos _) (cp_coprime_pow p hn) (tors n hn y) (tors n hn z)
      (by rw [ER n hn, ER n hn, sw, sys_right zf zg hn]; exact I.isom _ (cp_pos p hn) (cp_coprime p hn) y z)
      (by rw [EL n hn, EL n hn, sw, sys_left zf zg hn]; exact h₈ _ y z)
    rwa [cp_mul_pow] at this

section Weil

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) {L : LB A.left}
  (hL : L.IsLB) {T : Over S}


include hA hL in
theorem weilIs_pow_eq {a b : ℕ} (hb : 0 < b) {x y : T ⟶ A} {c c' : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs A L ((a * b : ℕ) : ℤ) x y c) (h' : Out.WeilIs A L a (x ^ b) (y ^ b) c') : c ^ b = c' := by
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  obtain ⟨t, ht⟩ := GlobalTheory.HodgeWeil.triv_theta GlobalTheory.CubeTop.cubeTheorem hA hL
  have h₀ := CommPairing.weilIs_symm hL h
  have pw : ∀ j : ℕ, Out.WeilIs A L ((a * b : ℕ) : ℤ) (y ^ (j + 1)) x (c⁻¹ ^ (j + 1)) := fun j => by
    induction j with
    | zero => rwa [zero_add, pow_one, pow_one]
    | succ j ih => rw [pow_succ, pow_succ c⁻¹]; exact GlobalTheory.DiagPairing.weilIs_mul_left hG hA hL ih h₀
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
  have h₂ := CommPairing.weilIs_symm hL (pw j)
  rw [inv_pow, inv_inv, Nat.cast_mul] at h₂
  exact PairingLevels.weilIs_value_eq hG hA hL ht h₂ h'


include hA hL in
theorem weilIs_of_coprime {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) {x y : T ⟶ A}
    {c : Γ(T.left, ⊤)ˣ} (hx : x ^ (a * b) = 1) (hy : y ^ (a * b) = 1)
    (h₁ : Out.WeilIs A L a (x ^ b) (y ^ b) (c ^ b)) (h₂ : Out.WeilIs A L b (x ^ a) (y ^ a) (c ^ a)) :
    Out.WeilIs A L ((a * b : ℕ) : ℤ) x y c := by
  obtain ⟨w, -, hw⟩ := GlobalTheory.HolTorsionAny.exists_weilIs_pow_eq_one hA hL hx hy
  have e₁ := weilIs_pow_eq hA hL hb hw h₁
  have e₂ := weilIs_pow_eq hA hL ha (by rw [mul_comm]; exact hw) h₂
  rwa [ext_pow hab e₂ e₁] at hw

end Weil

theorem glue : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → (∃ (ζ : ℕ → kˣ) (ev : ℕ → D.La → (Over.mk x ⟶ o.A)), (∀ e, IsPrimitiveRoot (ζ e) (p ^ e)) ∧ (∀ e, ζ (e + 1) ^ p = ζ e) ∧ (∀ e y z, ev e (y + z) = ev e y * ev e z) ∧ (∀ e (c : D.O) y, ev e (c • y) = ev e y ≫ o.act.act c) ∧ (∀ e y, ev e y = 1 ↔ ∃ z, y = p ^ e • z) ∧ (∀ e (q : Over.mk x ⟶ o.A), q ^ (p ^ e) = 1 ↔ ∃ y, ev e y = q) ∧ (∀ e y, ev (e + 1) y ^ p = ev e y) ∧ (∀ e y z, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (p ^ e) (ev e y) (ev e z) (unitOn (ζ e ^ (2 * D.EF y z))))) → ∃ I : GTateIso D.toG k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ o.eta y = I.ev N y := by
  intro p _ D R _ b N hN hNp S s o k _ _ _ x β hx ⟨ζ, ev, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩
  obtain ⟨I, hI⟩ := o.geom k x β hx
  have hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := LB.isLB_pull o.isLB _
  have up : ∀ (u : kˣ) (j : ℕ), unitOn (u ^ j) = unitOn u ^ j := fun u j => map_pow _ _ _
  obtain ⟨J, hJ⟩ := exists_gTateIso D (Q := Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun c q r => by have := o.act.hom c; exact MonObj.mul_comp _ _ _)
    (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z))
    (fun a b q r c ha hb hab hq hr w₁ w₂ => weilIs_of_coprime o.ab hL ha hb hab hq hr
      (by rw [up] at w₁; exact w₁) (by rw [up] at w₂; exact w₂))
    I ζ ev h₁ h₂ h₃ h₄ h₅ h₆ h₇ (fun e y z => by rw [Nat.cast_pow]; exact h₈ e y z)
  exact ⟨J, fun y => (hI y).trans (hJ N (by omega) hNp y).symm⟩

end GlobalTheory.UPel.HT.GTateGlue
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatible_roots_evaluation_injective : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → (∃ (ζ : ℕ → kˣ) (ev : ℕ → D.La → (Over.mk x ⟶ o.A)), (∀ e, IsPrimitiveRoot (ζ e) (p ^ e)) ∧ (∀ e, ζ (e + 1) ^ p = ζ e) ∧ (∀ e y z, ev e (y + z) = ev e y * ev e z) ∧ (∀ e (c : D.O) y, ev e (c • y) = ev e y ≫ o.act.act c) ∧ (∀ e y, ev e y = 1 ↔ ∃ z, y = p ^ e • z) ∧ (∀ e (q : Over.mk x ⟶ o.A), q ^ (p ^ e) = 1 ↔ ∃ y, ev e y = q) ∧ (∀ e y, ev (e + 1) y ^ p = ev e y) ∧ (∀ e y z, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (p ^ e) (ev e y) (ev e z) (unitOn (ζ e ^ (2 * D.EF y z))))) → ∃ I : GTateIso D.toG k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ o.eta y = I.ev N y := by
  first | (exact @GlobalTheory.UPel.HT.GTateGlue.glue) | (exact GlobalTheory.UPel.HT.GTateGlue.glue) | (intros; apply GlobalTheory.UPel.HT.GTateGlue.glue  <;> assumption)
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace GlobalTheory

theorem gen_level_extends_tate : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → ∃ I : GTateIso D.toG k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ o.eta y = I.ev N y :=
  fun p _ D R _ b N hN hNp S s o k _ _ _ x β hx =>
    GlobalTheory.T.compatible_roots_evaluation_injective p D R b N hN hNp S s o k x β hx (GlobalTheory.T.exists_compatible_roots_and_evaluation p D R b N hN hNp S s o k x β hx)

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tate_module_iso : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → ∃ I : GTateIso D.toG k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ o.eta y = I.ev N y := by
  first | (exact @GlobalTheory.gen_level_extends_tate) | (exact GlobalTheory.gen_level_extends_tate) | (intros; apply GlobalTheory.gen_level_extends_tate <;> assumption)
