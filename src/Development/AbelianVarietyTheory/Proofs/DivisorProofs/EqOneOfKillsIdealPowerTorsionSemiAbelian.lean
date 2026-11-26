module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosedRingStableSubgroupAbelianNoTorsion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosedStableSubgroupSemiAbelianNoTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosedTorusSubgroupWithoutPiTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosedTorusSubgroupWithoutPiTorsion
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Topology
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory

namespace TorusPiTorsion

open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
attribute [local instance] zuAlgebra

variable {k : Type} [Field k] {X : Type} [AddCommGroup X]

theorem val_splitTorusPoint (t : Multiplicative X →* kˣ) (b : X) :
    SplitTorus.val (splitTorusPoint t) b =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (t (Multiplicative.ofAdd b) : k) := by
  have h : (torusIso k X).hom.appTop.hom (Rosenlicht.chi X b) =
      (Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra k X))).inv.hom (AddMonoidAlgebra.single b 1) := by
    have := torusGamma_chi k X b
    rw [torusGamma, CommRingCat.comp_apply] at this
    rw [← this]
    simp
  rw [SplitTorus.val_eq, splitTorusPoint_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, h,
    SplitTorus.specMap_appTop_apply]
  simp [torusEval_single]

theorem splitTorusPoint_comp_torusMap (t : Multiplicative X →* kˣ) (φ : X →+ X) :
    splitTorusPoint t ≫ SplitTorus.torusMap (Sp k) φ =
      splitTorusPoint (t.comp (AddMonoidHom.toMultiplicative φ)) :=
  SplitTorus.hom_ext fun b => by
    rw [SplitTorus.val_comp_torusMap, val_splitTorusPoint, val_splitTorusPoint]
    rfl

end TorusPiTorsion
end GlobalTheory

namespace GlobalTheory
namespace TorusPiTorsion

theorem finite_of_isClosed_torusZariski_of_smul {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X] [Module.Finite ℤ X]
    (hdiv : ∀ r : O, r ≠ 0 → ∃ m : ℤ, m ≠ 0 ∧ r ∣ (m : O)) {π : O} (hπ0 : π ≠ 0)
    (hπ : ¬ IsUnit π) {H : Subgroup (Multiplicative X →* kˣ)}
    (hH : IsClosed[torusZariski k X] (H : Set (Multiplicative X →* kˣ)))
    (hstab : ∀ (a : O), ∀ s ∈ H,
      s.comp (AddMonoidHom.toMultiplicative (DistribSMul.toAddMonoidHom X a)) ∈ H)
    (htors : ∀ s ∈ H,
      s.comp (AddMonoidHom.toMultiplicative (DistribSMul.toAddMonoidHom X π)) = 1 → s = 1) :
    Finite H := by
  let K : Submodule O X :=
    { carrier := {x | ∀ s ∈ H, s (Multiplicative.ofAdd x) = 1}
      add_mem' := fun {a b} ha hb s hs => by rw [ofAdd_add, map_mul, ha s hs, hb s hs, _root_.mul_one]
      zero_mem' := fun s _ => map_one s
      smul_mem' := fun a x hx s hs => hx _ (hstab a s hs) }
  have hK : ∀ x, x ∈ K ↔ ∀ s ∈ H, s (Multiplicative.ofAdd x) = 1 := fun x => Iff.rfl
  let N : Submodule O X := K ⊔ Ideal.span {π} • ⊤
  have hπN : ∀ x : X, π • x ∈ N := fun x =>
    Submodule.mem_sup_right (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial)
  haveI : Module.Finite O X := Module.Finite.of_restrictScalars_finite ℤ O X
  have hN : (⊤ : Submodule O X) ≤ N := by
    intro x _
    by_contra hx
    obtain ⟨m, hm0, c, hc⟩ := hdiv π hπ0
    have hmQ : ∀ q : X ⧸ N, m • q = 0 := fun q => by
      obtain ⟨y, rfl⟩ := N.mkQ_surjective q
      rw [← Int.cast_smul_eq_zsmul O, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        hc, mul_smul]
      exact hπN _
    have hmQ' : ∀ q : Multiplicative (X ⧸ N), q ^ m.natAbs = 1 := fun q => by
      have h1 : (m.natAbs : ℤ) • q.toAdd = 0 := by
        rcases Int.natAbs_eq m with h | h
        · rw [← h]; exact hmQ _
        · rw [show (m.natAbs : ℤ) = -m by omega, neg_smul, hmQ, neg_zero]
      rw [natCast_zsmul] at h1
      exact congrArg Multiplicative.ofAdd h1
    haveI : Module.Finite ℤ (X ⧸ N) :=
      Module.Finite.of_surjective N.mkQ.toAddMonoidHom.toIntLinearMap N.mkQ_surjective
    haveI : Finite (X ⧸ N) := Module.finite_of_fg_torsion _ fun q =>
      ⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm0⟩, hmQ q⟩
    have hexp : Monoid.exponent (Multiplicative (X ⧸ N)) ≠ 0 := Monoid.exponent_ne_zero_of_finite
    haveI : NeZero ((Monoid.exponent (Multiplicative (X ⧸ N)) : ℕ) : k) := ⟨Nat.cast_ne_zero.2 hexp⟩
    obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
      (Multiplicative (X ⧸ N)) k (a := Multiplicative.ofAdd (N.mkQ x))
      (by simpa using hx)
    let t : Multiplicative X →* kˣ := φ.comp (AddMonoidHom.toMultiplicative N.mkQ.toAddMonoidHom)
    have ht : ∀ y, t y = φ (Multiplicative.ofAdd (N.mkQ y.toAdd)) := fun y => rfl
    have htH : t ∈ H := mem_of_isClosed_torusZariski hH fun y hy => by
      have : N.mkQ y.toAdd = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.mem_sup_left ((hK _).2 hy)
      rw [ht, this, ofAdd_zero, map_one]
    have ht1 : t = 1 := htors t htH (MonoidHom.ext fun y => by
      have : N.mkQ (π • y.toAdd) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hπN _
      change t (Multiplicative.ofAdd (π • y.toAdd)) = 1
      rw [ht, toAdd_ofAdd, this, ofAdd_zero, map_one])
    exact hφ (by simpa [ht] using DFunLike.congr_fun ht1 (Multiplicative.ofAdd x))
  obtain ⟨r, hr, hrK⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (I := Ideal.span {π}) (N := K) (N' := ⊤) (P := ⊤) Module.Finite.fg_top le_rfl hN
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hπ
    rw [zero_sub, Ideal.mem_span_singleton] at hr
    exact isUnit_of_dvd_one ((dvd_neg).1 hr)
  obtain ⟨m, hm0, c, hc⟩ := hdiv r hr0
  have hmK : ∀ x : X, m • x ∈ K := fun x => by
    rw [← Int.cast_smul_eq_zsmul O, hc, mul_smul]
    exact hrK (Submodule.smul_mem_pointwise_smul _ r ⊤ trivial)
  have hmH : ∀ s ∈ H, s ^ m.natAbs = 1 := fun s hs => by
    have h1 : s ^ m = 1 := MonoidHom.ext fun y => by
      have := (hK _).1 (hmK y.toAdd) s hs
      rw [ofAdd_zsmul, map_zpow, ofAdd_toAdd] at this
      rw [MonoidHom.zpow_apply, this, MonoidHom.one_apply]
    exact pow_natAbs_eq_one.2 h1
  exact (finite_setOf_pow_eq_one_torus (R := k) (X := X) (Int.natAbs_ne_zero.2 hm0)).subset
    (t := (H : Set (Multiplicative X →* kˣ))) fun s hs => hmH s hs

end TorusPiTorsion
end GlobalTheory

namespace GlobalTheory
namespace TorusPiTorsion

open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht

theorem exists_int_dvd (E : Type) [Field E] [NumberField E] (r : 𝓞 E) (hr : r ≠ 0) :
    ∃ m : ℤ, m ≠ 0 ∧ r ∣ (m : 𝓞 E) := by
  refine ⟨(Ideal.absNorm (Ideal.span {r}) : ℤ), ?_, ?_⟩
  · rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hr
  · rw [Int.cast_natCast, ← Ideal.mem_span_singleton]
    exact Ideal.absNorm_mem _

theorem finite_of_isClosed_of_no_pi_torsion :
    ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
      (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
      (act : OAct (𝓞 E) (splitTorus (Sp k) X)) (π : 𝓞 E), π ≠ 0 → ¬ IsUnit π →
      ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X))
        (Z : Set (splitTorus (Sp k) X).left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) →
        (∀ (a : 𝓞 E), ∀ x ∈ C, x ≫ act.act a ∈ C) → (∀ x ∈ C, x ≫ act.act π = 1 → x = 1) →
        Finite C := by
  intro E _ _ k _ _ _ X _ _ _ act π hπ0 hπ C Z hZ hC hstab htors
  have hφ : ∀ a, ∃ φ : X →+ X, act.act a = SplitTorus.torusMap (Sp k) φ := fun a => by
    haveI := act.hom a
    exact SplitTorus.exists_eq_torusMap _
  choose φ hφ using hφ
  have hinj : ∀ {ψ ψ' : X →+ X}, SplitTorus.torusMap (Sp k) ψ = SplitTorus.torusMap (Sp k) ψ' →
      ψ = ψ' := fun h => SplitTorus.torusMap_injective h
  have hone : φ 1 = AddMonoidHom.id X := hinj (by rw [← hφ, act.one, SplitTorus.torusMap_id])
  have hmul : ∀ a b, φ (a * b) = (φ a).comp (φ b) := fun a b =>
    hinj (by rw [← hφ, SplitTorus.torusMap_comp, ← hφ, ← hφ, act.mul])
  have hadd : ∀ a b, φ (a + b) = φ a + φ b := fun a b =>
    hinj (by rw [← hφ, SplitTorus.torusMap_add, ← hφ, ← hφ, act.add])
  let ρ : 𝓞 E →+* AddMonoid.End X :=
    { toFun := φ
      map_one' := hone
      map_mul' := hmul
      map_zero' := by
        have h := hadd 0 0
        rw [add_zero] at h
        have h' : φ 0 = 0 := by simpa using h.symm
        exact h'
      map_add' := hadd }
  letI : Module (𝓞 E) X := Module.compHom X ρ
  have hsmul : ∀ (a : 𝓞 E) (x : X), a • x = φ a x := fun a x => rfl
  let e := splitTorusPointEquiv (k := k) (X := X)
  have hpt : ∀ (s : Multiplicative X →* kˣ) (a : 𝓞 E), e s ≫ act.act a =
      e (s.comp (AddMonoidHom.toMultiplicative (DistribSMul.toAddMonoidHom X a))) := by
    intro s a
    rw [hφ a]
    exact splitTorusPoint_comp_torusMap s (φ a)
  let H := C.comap e.toMonoidHom
  have hcl : IsClosed[torusZariski k X] (H : Set (Multiplicative X →* kˣ)) := by
    refine isClosed_induced_iff.2 ⟨(torusIso k X).hom ⁻¹' Z,
      hZ.preimage (torusIso k X).hom.continuous, ?_⟩
    ext t
    change _ ↔ splitTorusPoint t ∈ C
    rw [hC, range_splitTorusPoint_left, Set.singleton_subset_iff]
    rfl
  have h := finite_of_isClosed_torusZariski_of_smul (k := k) (O := 𝓞 E) (X := X)
    (exists_int_dvd E) hπ0 hπ hcl
    (fun a s hs => by
      change e _ ∈ C
      rw [← hpt]
      exact hstab a _ hs)
    (fun s hs h1 => e.injective (by
      rw [map_one]
      refine htors _ hs ?_
      change e s ≫ act.act π = 1
      rw [hpt, h1, map_one]))
  have e' : H ≃ C := e.toEquiv.subtypeEquiv fun _ => Iff.rfl
  exact e'.finite_iff.1 h

end TorusPiTorsion
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosedTorusSubgroupWithoutPiTorsionStatement
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_closed_torus_subgroup_without_pi_torsion : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (act : OAct (𝓞 E) (splitTorus (Sp k) X)) (π : 𝓞 E), π ≠ 0 → ¬ IsUnit π → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X)) (Z : Set (splitTorus (Sp k) X).left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ (a : 𝓞 E), ∀ x ∈ C, x ≫ act.act a ∈ C) → (∀ x ∈ C, x ≫ act.act π = 1 → x = 1) → Finite C := by
  first | exact @GlobalTheory.TorusPiTorsion.finite_of_isClosed_of_no_pi_torsion | exact GlobalTheory.TorusPiTorsion.finite_of_isClosed_of_no_pi_torsion | (intros; apply GlobalTheory.TorusPiTorsion.finite_of_isClosed_of_no_pi_torsion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionTorusAndAbelianQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionTorusAndAbelianQuotient
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.SemiAbAct

theorem exists_torus_quotient_act : ∀ (O : Type) [CommRing O] (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (act : OAct O G), IsSemiAbelian G → ∀ (T : TorusExtension G), letI := T.addCommGroup; letI := T.grpB; ∃ (actB : OAct O T.B) (actT : OAct O (splitTorus (Sp k) T.X)), (∀ a, T.q ≫ actB.act a = act.act a ≫ T.q) ∧ (∀ a, actT.act a ≫ T.i = T.i ≫ act.act a) := by
  intro O _ k _ _ G _ act _ T
  letI := T.addCommGroup
  letI := T.grpB
  have := T.free
  have := T.finite
  have := T.i_hom
  have := T.q_hom
  have := T.q_flat
  have := T.q_surjective
  have := T.q_quasiCompact
  have := T.isAbelian.proper
  have hmono : Mono T.i := T.isKernel.flip.mono_snd_of_mono
  have hepi : Epi T.q := GlobalTheory.SemiRigid.epi_of_fpqc T.q
  have hA : ∀ a, IsMonHom (act.act a) := act.hom

  have hT : ∀ a, T.i ≫ act.act a ≫ T.q = toUnit _ ≫ η := by
    intro a
    rw [GlobalTheory.SemiRigid.torus_const T.X T.B (T.i ≫ act.act a ≫ T.q)]
    simp [IsMonHom.one_hom_assoc, IsMonHom.one_hom]
  let fT : ∀ a, splitTorus (Sp k) T.X ⟶ splitTorus (Sp k) T.X := fun a ↦
    T.isKernel.lift (T.i ≫ act.act a) (toUnit _) (by rw [Category.assoc, hT])
  have hfT : ∀ a, fT a ≫ T.i = T.i ≫ act.act a := fun a ↦ T.isKernel.lift_fst _ _ _

  have hB : ∀ a, ∃ g, T.q ≫ g = act.act a ≫ T.q := fun a ↦
    GlobalTheory.SemiRigid.exists_desc T.q (act.act a ≫ T.q) fun Z x y h ↦ by
      obtain ⟨τ, hτ⟩ := GlobalTheory.SemiRigid.exists_eq_mul T.isKernel h
      rw [hτ, MonObj.mul_comp_assoc, MonObj.mul_comp, Category.assoc, Category.assoc, hT,
        comp_toUnit_assoc, ← Hom.one_def, _root_.one_mul, Category.assoc]
  choose fB hfB using hB
  have hmulT : ∀ a, IsMonHom (fT a) := fun a ↦ by
    refine ⟨?_, ?_⟩
    · rw [← cancel_mono T.i, Category.assoc, hfT, IsMonHom.one_hom_assoc, IsMonHom.one_hom,
        IsMonHom.one_hom]
    · rw [← cancel_mono T.i, Category.assoc, hfT, IsMonHom.mul_hom_assoc, IsMonHom.mul_hom,
        Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc,
        tensorHom_comp_tensorHom_assoc, hfT]
  have hmulB : ∀ a, IsMonHom (fB a) := fun a ↦ by
    refine ⟨?_, ?_⟩
    · have h := IsMonHom.one_hom (f := T.q)
      rw [← h, Category.assoc, hfB, IsMonHom.one_hom_assoc, h]
    · have hqq : Epi (T.q ⊗ₘ T.q) := by
        have : Epi (T.q ▷ G) := GlobalTheory.SemiRigid.epi_of_fpqc _
        have : Epi (T.q ▷ T.B) := GlobalTheory.SemiRigid.epi_of_fpqc _
        have : Epi (lift (snd T.B G) (fst T.B G)) :=
          epi_of_epi_fac (h := 𝟙 _) (f := lift (snd G T.B) (fst G T.B)) (by apply CartesianMonoidalCategory.hom_ext <;> simp)
        have : Epi (lift (snd T.B T.B) (fst T.B T.B)) :=
          epi_of_epi_fac (h := 𝟙 _) (f := lift (snd T.B T.B) (fst T.B T.B)) (by apply CartesianMonoidalCategory.hom_ext <;> simp)
        have hs : T.B ◁ T.q =
            lift (snd T.B G) (fst T.B G) ≫ (T.q ▷ T.B) ≫ lift (snd T.B T.B) (fst T.B T.B) := by
          apply CartesianMonoidalCategory.hom_ext <;> simp
        rw [MonoidalCategory.tensorHom_def, hs]
        infer_instance
      rw [← cancel_epi (T.q ⊗ₘ T.q), ← IsMonHom.mul_hom_assoc, hfB, IsMonHom.mul_hom_assoc,
        IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc, hfB]
  refine ⟨⟨fB, hmulB, ?_, ?_, ?_⟩, ⟨fT, hmulT, ?_, ?_, ?_⟩, hfB, hfT⟩
  · rw [← cancel_epi T.q, hfB, act.one, Category.comp_id, Category.id_comp]
  · intro a b
    rw [← cancel_epi T.q, hfB, act.mul, Category.assoc, ← hfB, reassoc_of% hfB]
  · intro a b
    rw [← cancel_epi T.q, hfB, MonObj.comp_mul, hfB, hfB, act.add, MonObj.mul_comp]
  · rw [← cancel_mono T.i, hfT, act.one, Category.comp_id, Category.id_comp]
  · intro a b
    rw [← cancel_mono T.i, hfT, act.mul, Category.assoc, hfT, reassoc_of% hfT]
  · intro a b
    rw [← cancel_mono T.i, hfT, MonObj.mul_comp, hfT, hfT, act.add, MonObj.comp_mul]

end GlobalTheory.SemiAbAct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionTorusAndAbelianQuotientStatement
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringAction_torus_and_abelian_quotient : ∀ (O : Type) [CommRing O] (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (act : OAct O G), IsSemiAbelian G → ∀ (T : TorusExtension G), letI := T.addCommGroup; letI := T.grpB; ∃ (actB : OAct O T.B) (actT : OAct O (splitTorus (Sp k) T.X)), (∀ a, T.q ≫ actB.act a = act.act a ≫ T.q) ∧ (∀ a, actT.act a ≫ T.i = T.i ≫ act.act a) := by
  first | exact @GlobalTheory.SemiAbAct.exists_torus_quotient_act | exact GlobalTheory.SemiAbAct.exists_torus_quotient_act | (intros; apply GlobalTheory.SemiAbAct.exists_torus_quotient_act <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosedStableSubgroupSemiAbelianNoTorsion
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.OStableClosed
open GlobalTheory.RationalPoint

theorem finite_of_isClosed_of_no_torsion : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G] (act : OAct (𝓞 E) G) (π : 𝓞 E), IsSemiAbelian G → π ≠ 0 → ¬ IsUnit π → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)) (Z : Set G.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ (a : 𝓞 E), ∀ x ∈ C, x ≫ act.act a ∈ C) → (∀ x ∈ C, x ≫ act.act π = 1 → x = 1) → Finite C := by
  intro E _ _ k _ _ _ G _ act π hG hπ hπu C Z hZ hC hstab htor
  have := hG.comm
  have := hG.smooth
  have := hG.quasiCompact
  obtain ⟨T⟩ := GlobalTheory.TorsionDense.nonempty_torusExtension G hG
  letI := T.addCommGroup
  letI := T.free
  letI := T.finite
  letI := T.grpB
  haveI := T.q_hom
  haveI := T.i_hom
  haveI := T.isAbelian.proper
  haveI := T.isAbelian.smooth
  haveI := act.hom π
  obtain ⟨actB, actT, hB, hT⟩ := GlobalTheory.T.exists_ringAction_torus_and_abelian_quotient (𝓞 E) k G act hG T
  let φ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ T.B) :=
    MonoidHom.mk' (fun x => x ≫ T.q) fun x y => MonObj.mul_comp x y T.q
  let j : (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) T.X) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    MonoidHom.mk' (fun x => x ≫ T.i) fun x y => MonObj.mul_comp x y T.i
  let m : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    MonoidHom.mk' (fun x => x ≫ act.act π) fun x y => MonObj.mul_comp x y _
  have hj : Function.Injective j := fun x y hxy =>
    T.isKernel.hom_ext hxy (toUnit_unique _ _)
  have hker : ∀ x, φ x = 1 → ∃ t, j t = x := fun x hx =>
    ⟨T.isKernel.lift x (toUnit _) hx, T.isKernel.lift_fst _ _ _⟩
  have hTf : Finite (C.comap j) := by
    refine GlobalTheory.T.finite_closed_torus_subgroup_without_pi_torsion E k T.X actT π hπ hπu _ (T.i.left ⁻¹' Z)
      (hZ.preimage T.i.left.continuous) (fun x => ?_) (fun a x hx => ?_) (fun x hx h1 => ?_)
    · rw [Subgroup.mem_comap, hC, range_left_subset_iff, range_left_subset_iff]
      rfl
    · rw [Subgroup.mem_comap] at hx ⊢
      change (x ≫ actT.act a) ≫ T.i ∈ C
      rw [Category.assoc, hT a, ← Category.assoc]
      exact hstab a _ hx
    · apply hj
      rw [map_one]
      refine htor _ hx ?_
      change (x ≫ T.i) ≫ act.act π = 1
      rw [Category.assoc, ← hT π, ← Category.assoc, h1, MonObj.one_comp]
  let ψ : C →* (𝟙_ (Over (Sp k)) ⟶ T.B) := φ.comp C.subtype
  have hK : Finite ψ.ker := by
    choose s hs using fun x : ψ.ker => hker x.1.1 x.2
    refine Finite.of_injective
      (fun x : ψ.ker => (⟨s x, by rw [Subgroup.mem_comap, hs]; exact x.1.2⟩ : C.comap j))
      fun x y hxy => ?_
    have := congrArg (fun t : C.comap j => j t.1) hxy
    simp only [hs] at this
    exact Subtype.ext (Subtype.ext this)
  obtain ⟨Z', hZ', h'⟩ := exists_isClosed_image_of_isClosed_subgroup k G T.B T.q inferInstance
    inferInstance inferInstance inferInstance inferInstance C Z hZ hC
  have hR : Finite ψ.range := by
    refine GlobalTheory.T.finite_closed_ringStable_subgroup_abelian_no_torsion E k T.B actB π T.isAbelian hπ hπu _ Z' hZ' (fun y => ?_) (fun a y hy => ?_) ?_
    · rw [← h']
      exact ⟨fun ⟨x, hx⟩ => ⟨x.1, x.2, hx⟩, fun ⟨x, hx, hy⟩ => ⟨⟨x, hx⟩, hy⟩⟩
    · obtain ⟨x, rfl⟩ := hy
      refine ⟨⟨x.1 ≫ act.act a, hstab a _ x.2⟩, ?_⟩
      change (x.1 ≫ act.act a) ≫ T.q = (x.1 ≫ T.q) ≫ actB.act a
      rw [Category.assoc, Category.assoc, hB]
    · rintro _ ⟨y, rfl⟩ hy
      have hmC : ∀ z : C, m z.1 ∈ C := fun z => hstab π _ z.2
      have hmK : ∀ z : ψ.ker, ψ ⟨m z.1.1, hmC z.1⟩ = 1 := fun z => by
        change (z.1.1 ≫ act.act π) ≫ T.q = 1
        rw [Category.assoc, ← hB π, ← Category.assoc]
        change ψ z.1 ≫ actB.act π = 1
        rw [MonoidHom.mem_ker.1 z.2]
        haveI := actB.hom π
        exact MonObj.one_comp _
      let f : ψ.ker → ψ.ker := fun z => ⟨⟨m z.1.1, hmC z.1⟩, hmK z⟩
      have hf : Function.Injective f := fun z₁ z₂ h => by
        have h1 : m z₁.1.1 = m z₂.1.1 := congrArg (fun z : ψ.ker => z.1.1) h
        have h2 : z₁.1.1 / z₂.1.1 = 1 := htor _ (C.div_mem z₁.1.2 z₂.1.2) (by
          change m (z₁.1.1 / z₂.1.1) = 1
          rw [map_div, h1, div_self'])
        exact Subtype.ext (Subtype.ext (div_eq_one.1 h2))
      have hw : ψ ⟨m y.1, hmC y⟩ = 1 := by
        change (y.1 ≫ act.act π) ≫ T.q = 1
        rw [Category.assoc, ← hB π, ← Category.assoc]
        exact hy
      obtain ⟨z, hz⟩ := (Finite.injective_iff_surjective.1 hf) ⟨⟨m y.1, hmC y⟩, hw⟩
      have h1 : m z.1.1 = m y.1 := congrArg (fun z : ψ.ker => z.1.1) hz
      have h2 : y.1 / z.1.1 = 1 := htor _ (C.div_mem y.2 z.1.2) (by
        change m (y.1 / z.1.1) = 1
        rw [map_div, h1, div_self'])
      have h3 : y = z.1 := Subtype.ext (div_eq_one.1 h2)
      rw [h3]
      exact z.2
  exact (MonoidHom.finite_iff_finite_ker_range ψ).2 ⟨hK, hR⟩

end GlobalTheory.OStableClosed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosedStableSubgroupSemiAbelianNoTorsionStatement
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_closed_stable_subgroup_semiAbelian_no_torsion : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G] (act : OAct (𝓞 E) G) (π : 𝓞 E), IsSemiAbelian G → π ≠ 0 → ¬ IsUnit π → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)) (Z : Set G.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ (a : 𝓞 E), ∀ x ∈ C, x ≫ act.act a ∈ C) → (∀ x ∈ C, x ≫ act.act π = 1 → x = 1) → Finite C := by
  first | exact @GlobalTheory.OStableClosed.finite_of_isClosed_of_no_torsion | exact GlobalTheory.OStableClosed.finite_of_isClosed_of_no_torsion | (intros; apply GlobalTheory.OStableClosed.finite_of_isClosed_of_no_torsion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfKillsIdealPowerTorsionSemiAbelian
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Topology TopologicalSpace

attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.IdealTorsion

open RationalPoint GlobalTheory.TorsionDense
open scoped nonZeroDivisors

theorem exists_pow_eq_span (E : Type) [Field E] [NumberField E] (I : Ideal (𝓞 E)) (hI : I ≠ ⊥)
    (hI' : I ≠ ⊤) : ∃ (h : ℕ) (π : 𝓞 E), 0 < h ∧ I ^ h = Ideal.span {π} ∧ π ≠ 0 ∧ ¬ IsUnit π := by
  have hmem : I ∈ (Ideal (𝓞 E))⁰ := mem_nonZeroDivisors_of_ne_zero hI
  let c := ClassGroup.mk0 ⟨I, hmem⟩
  have hc : c ^ Fintype.card (ClassGroup (𝓞 E)) = 1 := pow_card_eq_one
  have hmem' : I ^ Fintype.card (ClassGroup (𝓞 E)) ∈ (Ideal (𝓞 E))⁰ := pow_mem hmem _
  have hp : (I ^ Fintype.card (ClassGroup (𝓞 E))).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff hmem']
    rw [← hc, ← map_pow]
    rfl
  obtain ⟨π, hπ⟩ := hp
  have hpos : 0 < Fintype.card (ClassGroup (𝓞 E)) := Fintype.card_pos
  refine ⟨_, π, hpos, by rw [hπ], ?_, ?_⟩
  · rintro rfl
    have : I ^ Fintype.card (ClassGroup (𝓞 E)) = ⊥ := by rw [hπ]; simp
    exact hI (pow_eq_zero_iff hpos.ne' |>.1 this)
  · intro hu
    have : I ^ Fintype.card (ClassGroup (𝓞 E)) = ⊤ := by
      rw [hπ]; exact Ideal.span_singleton_eq_top.2 hu
    exact hI' (eq_top_iff.2 (this ▸ Ideal.pow_le_self hpos.ne'))

theorem exists_act_pow_stable {k : Type} [Field k] [IsAlgClosed k] {O : Type} [CommRing O]
    (G : Over (Sp k)) [GrpObj G]
    [IsCommMonObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] (act : OAct O G) (π : O)
    (K : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)) (Z : Set G.left) (hZ : IsClosed Z)
    (hK : ∀ x, x ∈ K ↔ Set.range x.left ⊆ Z) (hKs : ∀ x ∈ K, x ≫ act.act π ∈ K) :
    ∃ a : ℕ, ∀ x ∈ K, ∃ y ∈ K, y ≫ act.act (π ^ (a + 1)) = x ≫ act.act (π ^ a) := by
  letI := zariski G
  haveI := noetherianSpace_zariski G
  have hcl : ∀ n : ℕ, IsClosed {z : 𝟙_ (Over (Sp k)) ⟶ G | ∃ y ∈ K, y ≫ act.act (π ^ n) = z} :=
    fun n => by
    obtain ⟨Z', hZ', h⟩ := exists_isClosed_image_of_isClosed_subgroup k G G (act.act (π ^ n))
      (act.hom _) inferInstance inferInstance inferInstance inferInstance K Z hZ hK
    refine isClosed_induced_iff.2 ⟨Z', hZ', ?_⟩
    ext z
    rw [Set.mem_preimage, ← range_left_subset_iff, ← h]
    rfl
  let F : ℕ → Closeds (𝟙_ (Over (Sp k)) ⟶ G) := fun a => ⟨_, hcl a⟩
  obtain ⟨_, ⟨a, rfl⟩, hmin⟩ := (wellFounded_lt (α := Closeds (𝟙_ (Over (Sp k)) ⟶ G))).has_min
    (Set.range F) ⟨_, 0, rfl⟩
  have hle : F (a + 1) ≤ F a := by
    rintro _ ⟨y, hy, rfl⟩
    haveI := act.hom π
    refine ⟨y ≫ act.act π, ?_, by rw [Category.assoc, ← act.mul, ← pow_succ']⟩
    exact hKs y hy
  have heq : F (a + 1) = F a := hle.eq_of_not_lt (hmin _ ⟨_, rfl⟩)
  refine ⟨a, fun x hx => ?_⟩
  have : x ≫ act.act (π ^ a) ∈ F (a + 1) := by
    rw [heq]
    exact ⟨x, hx, rfl⟩
  exact this

end GlobalTheory.IdealTorsion

namespace GlobalTheory.IdealTorsion

open RationalPoint GlobalTheory.TorsionDense

theorem eq_one_of_idealTorsion_comp_eq_one : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G] (act : OAct (𝓞 E) G) (u : G ⟶ G) (I : Ideal (𝓞 E)), IsSemiAbelian G → IsMonHom u → (∀ a, act.act a ≫ u = u ≫ act.act a) → I ≠ ⊤ → (∀ (j : ℕ) (x : 𝟙_ (Over (Sp k)) ⟶ G), (∀ a ∈ I ^ j, x ≫ act.act a = 1) → x ≫ u = 1) → u = 1 := by
  intro E _ _ k _ _ _ G _ act u I hG hu hcomm hI hkill
  have := hG.comm
  have := hG.smooth
  have := hG.quasiCompact
  have := isIntegral_left_of_isSemiAbelian G
  haveI := hu
  have hact : ∀ a, IsMonHom (act.act a) := act.hom
  have h0 : act.act 0 = 1 := by
    have h := act.add 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  let φ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    MonoidHom.mk' (fun x => x ≫ u) fun x y => MonObj.mul_comp x y u
  by_cases hbot : I = ⊥
  · subst hbot
    refine eq_one_of_finite_range u ?_
    have : (Set.range fun x : 𝟙_ (Over (Sp k)) ⟶ G => x ≫ u) ⊆ {1} := by
      rintro _ ⟨x, rfl⟩
      refine hkill 1 x fun a ha => ?_
      rw [pow_one, Ideal.mem_bot] at ha
      rw [ha, h0, MonObj.comp_one]
    exact (Set.finite_singleton _).subset this
  obtain ⟨h, π, hh, hπ, hπ0, hπu⟩ := exists_pow_eq_span E I hbot hI
  have htors : ∀ (n : ℕ) (x : 𝟙_ (Over (Sp k)) ⟶ G), x ≫ act.act (π ^ n) = 1 → x ≫ u = 1 := by
    intro n x hx
    refine hkill (h * n) x fun a ha => ?_
    rw [pow_mul, hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [mul_comm, act.mul, ← Category.assoc, hx, MonObj.one_comp]
  obtain ⟨a, ha⟩ := exists_act_pow_stable G act π φ.ker (u.left ⁻¹' {pt (1 : 𝟙_ (Over (Sp k)) ⟶ G)})
    ((isClosed_pt _).preimage u.left.continuous) (fun x => by
      rw [range_left_subset_iff, Set.mem_preimage, ← pt_comp, Set.mem_singleton_iff,
        pt_injective.eq_iff]
      rfl) (fun x hx => by
      rw [MonoidHom.mem_ker] at hx ⊢
      change x ≫ act.act π ≫ u = 1
      rw [hcomm, ← Category.assoc]
      change (x ≫ u) ≫ act.act π = 1
      rw [show x ≫ u = 1 from hx, MonObj.one_comp])
  obtain ⟨Z', hZ', h'⟩ := exists_isClosed_image_of_isClosed_subgroup k G G u hu inferInstance
    inferInstance inferInstance inferInstance ⊤ Set.univ isClosed_univ (by simp)
  have hfin : Finite φ.range := by
    refine GlobalTheory.T.finite_closed_stable_subgroup_semiAbelian_no_torsion E k G act π hG hπ0 hπu _ Z' hZ' (fun y => ?_) ?_ ?_
    · rw [← h']
      exact ⟨fun ⟨x, hx⟩ => ⟨x, trivial, hx⟩, fun ⟨x, _, hx⟩ => ⟨x, hx⟩⟩
    · rintro b _ ⟨g, rfl⟩
      refine ⟨g ≫ act.act b, ?_⟩
      change (g ≫ act.act b) ≫ u = (g ≫ u) ≫ act.act b
      rw [Category.assoc, hcomm, Category.assoc]
    · rintro _ ⟨g, rfl⟩ hg
      have hgk : g ≫ act.act π ∈ φ.ker := by
        rw [MonoidHom.mem_ker]
        change (g ≫ act.act π) ≫ u = 1
        rw [Category.assoc, hcomm, ← Category.assoc]
        exact hg
      obtain ⟨y, hy, hyg⟩ := ha _ hgk
      let ψ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
        MonoidHom.mk' (fun x => x ≫ act.act (π ^ (a + 1))) fun x y => MonObj.mul_comp x y _
      have h1 : φ (g / y) = 1 := htors (a + 1) (g / y) (by
        change ψ (g / y) = 1
        rw [map_div, div_eq_one]
        change g ≫ act.act (π ^ (a + 1)) = y ≫ act.act (π ^ (a + 1))
        rw [hyg, pow_succ', act.mul, Category.assoc])
      rwa [map_div, MonoidHom.mem_ker.1 hy, div_one] at h1
  exact eq_one_of_finite_range u hfin

end GlobalTheory.IdealTorsion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfKillsIdealPowerTorsionSemiAbelianStatement
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_one_of_kills_idealPowerTorsion_semiAbelian : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G] (act : OAct (𝓞 E) G) (u : G ⟶ G) (I : Ideal (𝓞 E)), IsSemiAbelian G → IsMonHom u → (∀ a, act.act a ≫ u = u ≫ act.act a) → I ≠ ⊤ → (∀ (j : ℕ) (x : 𝟙_ (Over (Sp k)) ⟶ G), (∀ a ∈ I ^ j, x ≫ act.act a = 1) → x ≫ u = 1) → u = 1 := by
  first | exact @GlobalTheory.IdealTorsion.eq_one_of_idealTorsion_comp_eq_one | exact GlobalTheory.IdealTorsion.eq_one_of_idealTorsion_comp_eq_one | (intros; apply GlobalTheory.IdealTorsion.eq_one_of_idealTorsion_comp_eq_one <;> assumption)
end
