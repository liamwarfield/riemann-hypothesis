module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.GroupHomologyLongExact

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Shapiro
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.IndPerm
open CategoryTheory UpperTheory.V.KH

open Representation in
private theorem indV_mk_mul {k G : Type} [CommRing k] [Group G] (S : Subgroup G) (s : S) (h : G)
    (a : k) :
    IndV.mk S.subtype (Representation.trivial k S k) (s.1 * h) a =
      IndV.mk S.subtype (Representation.trivial k S k) h a := by
  have := Coinvariants.mk_self_apply
    (Representation.tprod ((leftRegular k G).comp S.subtype) (Representation.trivial k S k)) s
    (MonoidAlgebra.single h (1 : k) ⊗ₜ[k] a)
  simpa [ofMulAction_single] using this

open Representation in
private noncomputable def fwd (k G X : Type) [CommRing k] [Group G] [MulAction G X] (x : X) :
    IndV (MulAction.stabilizer G x).subtype
      (Representation.trivial k (MulAction.stabilizer G x) k) →ₗ[k] (X →₀ k) :=
  Representation.Coinvariants.lift _
    (TensorProduct.lift <| (Finsupp.lift _ _ _ fun h : G => Finsupp.lsingle (h⁻¹ • x)) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)
    fun g ↦ by
      ext h : 4
      have hg : (g : G)⁻¹ • x = x := (g⁻¹).2
      simp [mul_smul, hg]

open Representation in
private theorem fwd_mk (k G X : Type) [CommRing k] [Group G] [MulAction G X] (x : X) (h : G)
    (a : k) :
    fwd k G X x (IndV.mk _ _ h a) = Finsupp.single (h⁻¹ • x) a := by
  simp [fwd]

private theorem induced_trivial_iso_permutation (k G X : Type) [CommRing k] [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X] (x : X) (σ : Representation k G (X →₀ k))
    (hσ : ∀ g y c, σ g (Finsupp.single y c) = Finsupp.single (g • y) c) :
    Nonempty (Rep.ind (MulAction.stabilizer G x).subtype
      (Rep.trivial k (MulAction.stabilizer G x) k) ≅ Rep.of σ) := by
  choose c hc using fun y : X => MulAction.exists_smul_eq G x y
  let bwd : (X →₀ k) →ₗ[k] Representation.IndV (MulAction.stabilizer G x).subtype
      (Representation.trivial k (MulAction.stabilizer G x) k) :=
    Finsupp.lsum k fun y => Representation.IndV.mk _ _ (c y)⁻¹
  have hb : ∀ y a, bwd (Finsupp.single y a) = Representation.IndV.mk _ _ (c y)⁻¹ a := by
    intro y a
    simp [bwd]
  have h1 : fwd k G X x ∘ₗ bwd = LinearMap.id := by
    refine Finsupp.lhom_ext fun y a => ?_
    rw [LinearMap.comp_apply, hb, fwd_mk, inv_inv, hc]
    rfl
  have h2 : bwd ∘ₗ fwd k G X x = LinearMap.id := by
    refine Representation.IndV.hom_ext _ _ fun h => LinearMap.ext fun a => ?_
    show bwd (fwd k G X x (Representation.IndV.mk _ _ h a)) = Representation.IndV.mk _ _ h a
    rw [fwd_mk, hb]
    have hs : h * c (h⁻¹ • x) ∈ MulAction.stabilizer G x := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, hc, smul_inv_smul]
    have := indV_mk_mul (MulAction.stabilizer G x) ⟨_, hs⟩ (c (h⁻¹ • x))⁻¹ a
    simp only [mul_inv_cancel_right] at this
    exact this.symm
  let e : Representation.IndV (MulAction.stabilizer G x).subtype
      (Representation.trivial k (MulAction.stabilizer G x) k) ≃ₗ[k] (X →₀ k) :=
    LinearEquiv.ofLinear (fwd k G X x) bwd h1 h2
  refine ⟨Rep.mkIso (Representation.Equiv.mk e fun g => ?_)⟩
  refine Representation.IndV.hom_ext _ _ fun h => LinearMap.ext fun a => ?_
  show fwd k G X x (Representation.ind _ _ g (Representation.IndV.mk _ _ h a)) =
    σ g (fwd k G X x (Representation.IndV.mk _ _ h a))
  rw [Representation.ind_mk, fwd_mk, fwd_mk, hσ, mul_inv_rev, inv_inv, mul_smul]

theorem UpperTheory.V.KH.indPerm :
    ∀ (G X : Type) [Group G] [MulAction G X] [MulAction.IsPretransitive G X] (x : X),
      Nonempty (Rep.ind (MulAction.stabilizer G x).subtype
        (Rep.trivial ℤ (MulAction.stabilizer G x) ℤ) ≅ permRep G X) := by
  intro G X _ _ _ x
  exact induced_trivial_iso_permutation ℤ G X x (perm G X) perm_single
end

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.shapiro :
    ∀ (G X : Type) [Group G] [MulAction G X] [MulAction.IsPretransitive G X] (x : X) (n : ℕ),
      Nonempty (groupHomology (permRep G X) n ≃+ HZ (MulAction.stabilizer G x) n) := by
  intro G X _ _ _ x n
  classical
  obtain ⟨e⟩ := indPerm G X x
  let i1 := (groupHomology.functor ℤ G n).mapIso e.symm
  let i2 := groupHomology.indIso (MulAction.stabilizer G x) (Rep.trivial ℤ (MulAction.stabilizer G x) ℤ) n
  exact ⟨(i1 ≪≫ i2).toLinearEquiv.toAddEquiv⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.PermTrans
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FinGroup
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.ImportsAlt
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.MapNsmul
open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.mapNsmul :
    ∀ (G : Type) [Group G] (A B : Rep ℤ G) (f : A ⟶ B) (g : B ⟶ A) (n j : ℕ),
      (∀ a, g.hom (f.hom a) = n • a) → Subsingleton (groupHomology B j) →
      ∀ z : groupHomology A j, n • z = 0 := by
  intro G _ A B f g n j h hB z
  have hc : groupHomology.chainsMap (MonoidHom.id G) (f ≫ g) =
      n • 𝟙 (groupHomology.inhomogeneousChains A) := by
    ext i : 1
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun c => ?_
    refine Finsupp.ext fun y => ?_
    simp [h]
  have hm : groupHomology.map (MonoidHom.id G) (f ≫ g) j = n • 𝟙 (groupHomology A j) := by
    simp only [groupHomology.map, hc]
    change (HomologicalComplex.homologyFunctor _ _ j).map _ = _
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
    rfl
  have e1 : (groupHomology.map (MonoidHom.id G) (f ≫ g) j).hom z = n • z := by
    rw [hm]
    rfl
  rw [← e1, groupHomology.map_id_comp]
  have e2 : (groupHomology.map (MonoidHom.id G) f j).hom z = 0 :=
    Subsingleton.elim (α := groupHomology B j) _ _
  simp [e2]
end

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.kill :
    ∀ (S : Type) [Group S] [Finite S] (j : ℕ) (z : HZ S (j + 1)), Nat.card S • z = 0 := by
  intro S _ _ j z
  classical
  haveI : Fintype S := Fintype.ofFinite S
  let v : S →₀ ℤ := ∑ s : S, Finsupp.single s 1
  have hv : ∀ g : S, perm S S g v = v := by
    intro g
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [v, map_sum, perm_single]
    exact Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun _ => rfl)
  let fi : (Rep.trivial ℤ S ℤ).ρ.IntertwiningMap (permRep S S).ρ :=
    ⟨LinearMap.toSpanSingleton ℤ _ v, fun g => by
      apply LinearMap.ext_ring
      simp [Rep.trivial_ρ, permRep, hv]⟩
  let gi : (permRep S S).ρ.IntertwiningMap (Rep.trivial ℤ S ℤ).ρ :=
    ⟨aug S, fun g => by
      apply Finsupp.lhom_ext
      intro x c
      simp [Rep.trivial_ρ, permRep, perm_single, aug_single]⟩
  have hcomp : ∀ a : Rep.trivial ℤ S ℤ,
      (Rep.Hom.hom (Rep.ofHom gi)) ((Rep.Hom.hom (Rep.ofHom fi)) a) = Nat.card S • a := by
    intro a
    change aug S (a • v) = Nat.card S • a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [v, map_smul, map_sum, aug_single, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      nsmul_eq_mul, Nat.card_eq_fintype_card, mul_one]
    ring
  have hsub : Subsingleton (groupHomology (permRep S S) (j + 1)) := by
    obtain ⟨e⟩ := shapiro S S (1 : S) (j + 1)
    haveI : Subsingleton (MulAction.stabilizer S (1 : S)) := by
      constructor
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      have ha' : a * 1 = 1 := ha
      have hb' : b * 1 = 1 := hb
      simp only [mul_one] at ha' hb'
      subst ha' hb'
      rfl
    have hz := ModuleCat.isZero_iff_subsingleton.mp
      (isZero_groupHomology_succ_of_subsingleton
        (Rep.trivial ℤ (MulAction.stabilizer S (1 : S)) ℤ) j)
    exact e.injective.subsingleton
  exact mapNsmul S (Rep.trivial ℤ S ℤ) (permRep S S) (Rep.ofHom fi) (Rep.ofHom gi) (Nat.card S) (j + 1) hcomp hsub z
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Subquot
open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.subquot :
    ∀ (ι Z H : Type) [Finite ι] [AddCommGroup Z] [AddCommGroup H] (i : Z →+ (ι →₀ ℤ)) (q : Z →+ H)
      (n : ℕ), 1 ≤ n → Function.Injective i → Function.Surjective q → (∀ h : H, n • h = 0) →
      CardLe H (n ^ Nat.card ι) := by
  intro ι Z H _ _ _ i q n hn hi hq hk
  classical
  have := Fintype.ofFinite ι
  let i' : Z →ₗ[ℤ] (ι →₀ ℤ) := i.toIntLinearMap
  have hi' : Function.Injective i' := hi
  have : Module.Finite ℤ Z := Module.Finite.of_injective i' hi'
  have : Module.Free ℤ Z :=
    Module.Free.of_equiv (LinearEquiv.ofInjective i' hi').symm
  have hr : Module.finrank ℤ Z ≤ Nat.card ι := by
    have h := LinearMap.finrank_le_finrank_of_injective hi'
    rwa [Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card] at h
  let b := Module.finBasis ℤ Z
  let f : (Fin (Module.finrank ℤ Z) → Fin n) → H := fun c => ∑ k, (((c k : ℕ) : ℤ)) • q (b k)
  have hn0 : (0 : ℤ) < n := by exact_mod_cast hn
  have hf : Function.Surjective f := by
    intro h
    obtain ⟨z, rfl⟩ := hq h
    refine ⟨fun k => ⟨(b.repr z k % n).toNat, ?_⟩, ?_⟩
    · have h1 := Int.emod_nonneg (b.repr z k) hn0.ne'
      have h2 := Int.emod_lt_of_pos (b.repr z k) hn0
      omega
    · set_option synthInstance.maxHeartbeats 100000 in
        conv_rhs => rw [← b.sum_repr z, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h1 := Int.emod_nonneg (b.repr z k) hn0.ne'
      rw [map_zsmul]
      simp only [Int.toNat_of_nonneg h1]
      have h3 : (n : ℤ) • q (b k) = 0 := by rw [natCast_zsmul]; exact hk _
      conv_rhs => rw [← Int.emod_add_ediv_mul (b.repr z k) n, add_smul, mul_smul, h3, smul_zero,
        add_zero]
  refine ⟨Finite.of_surjective f hf, (Nat.card_le_card_of_surjective f hf).trans ?_⟩
  rw [Nat.card_fun, Nat.card_fin, Nat.card_fin]
  exact Nat.pow_le_pow_right hn hr
end

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.finGroup :
    ∀ (S : Type) [Group S] [Finite S] (j : ℕ),
      CardLe (HZ S (j + 1)) (Nat.card S ^ (Nat.card S ^ (j + 1))) := by
  intro S _ _ j
  have hi : Function.Injective (groupHomology.iCycles (Rep.trivial ℤ S ℤ) (j + 1)).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hq : Function.Surjective (groupHomology.π (Rep.trivial ℤ S ℤ) (j + 1)).hom :=
    fun x => groupHomology_induction_on x fun y => ⟨y, rfl⟩
  have h := subquot (Fin (j + 1) → S) (groupHomology.cycles (Rep.trivial ℤ S ℤ) (j + 1))
    (HZ S (j + 1)) (groupHomology.iCycles (Rep.trivial ℤ S ℤ) (j + 1)).hom.toAddMonoidHom
    (groupHomology.π (Rep.trivial ℤ S ℤ) (j + 1)).hom.toAddMonoidHom (Nat.card S)
    Nat.card_pos hi hq (kill S j)
  rwa [Nat.card_fun, Nat.card_fin] at h
end

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.permTrans :
    ∀ (G X : Type) [Group G] [MulAction G X] [MulAction.IsPretransitive G X] [Nonempty X] (s j : ℕ),
      StabLe G X s → CardLe (groupHomology (permRep G X) (j + 1)) (s ^ (s ^ (j + 1))) := by
  intro G X _ _ _ _ s j hs
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨hfin, hcard⟩ := hs x
  haveI := hfin
  obtain ⟨e⟩ := shapiro G X x (j + 1)
  have h1 := finGroup (MulAction.stabilizer G x) j
  have hpos : 0 < Nat.card (MulAction.stabilizer G x) := Nat.card_pos
  have hle : Nat.card (MulAction.stabilizer G x) ^ Nat.card (MulAction.stabilizer G x) ^ (j + 1)
      ≤ s ^ s ^ (j + 1) := by
    have hs1 : 0 < s := lt_of_lt_of_le hpos hcard
    calc Nat.card (MulAction.stabilizer G x) ^ Nat.card (MulAction.stabilizer G x) ^ (j + 1)
        ≤ s ^ Nat.card (MulAction.stabilizer G x) ^ (j + 1) := Nat.pow_le_pow_left hcard _
      _ ≤ s ^ s ^ (j + 1) := Nat.pow_le_pow_right hs1 (Nat.pow_le_pow_left hcard _)
  exact transport.2.1 _ _ e.symm.toEquiv _ (transport.2.2.2 _ _ _ hle h1)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.PermEmpty
open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.permEmpty :
    ∀ (G X : Type) [Group G] [MulAction G X] [IsEmpty X] (j : ℕ),
      CardLe (groupHomology (permRep G X) j) 1 := by
  intro G X _ _ _ j
  have hC : Subsingleton ((groupHomology.inhomogeneousChains (permRep G X)).X j) := by
    change Subsingleton ((Fin j → G) →₀ (X →₀ ℤ))
    infer_instance
  have hZ : Subsingleton (groupHomology.cycles (permRep G X) j) := by
    refine ⟨fun a b => ?_⟩
    exact (ModuleCat.mono_iff_injective (groupHomology.iCycles (permRep G X) j)).1
      inferInstance (Subsingleton.elim _ _)
  have hH : Subsingleton (groupHomology (permRep G X) j) := by
    refine ⟨fun a b => ?_⟩
    induction a using groupHomology_induction_on with
    | h a =>
      induction b using groupHomology_induction_on with
      | h b => rw [Subsingleton.elim a b]
  haveI := hH
  exact ⟨Finite.of_subsingleton, (Finite.card_le_one_iff_subsingleton).2 hH⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.PermSplit
open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.permSplit :
    ∀ (G X : Type) [Group G] [MulAction G X] (U V : SubMulAction G X), (∀ y, y ∈ V ↔ y ∉ U) →
      ∃ (f : permRep G U ⟶ permRep G X) (g : permRep G X ⟶ permRep G V),
        Function.Injective f.hom ∧ Function.Exact f.hom g.hom ∧ Function.Surjective g.hom := by
  intro G X _ _ U V hUV
  let F : (perm G U).IntertwiningMap (perm G X) :=
    { toLinearMap := Finsupp.lmapDomain ℤ ℤ (Subtype.val : U → X)
      isIntertwining' := by
        intro g
        refine LinearMap.ext fun f => ?_
        simp only [LinearMap.comp_apply, perm_apply, Finsupp.lmapDomain_apply]
        rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
        congr 1 }
  let Gm : (perm G X).IntertwiningMap (perm G V) :=
    { toLinearMap := Finsupp.lsubtypeDomain (V : Set X)
      isIntertwining' := by
        intro g
        refine LinearMap.ext fun f => ?_
        ext ⟨y, hy⟩
        change (Finsupp.mapDomain (fun x => g • x) f) y =
          (Finsupp.mapDomain (fun v : V => g • v) (Finsupp.subtypeDomain (· ∈ V) f)) ⟨y, hy⟩
        have hy' : g⁻¹ • y ∈ V := V.smul_mem _ hy
        have e2 : (⟨y, hy⟩ : V) = g • (⟨g⁻¹ • y, hy'⟩ : V) := Subtype.ext (by simp)
        rw [e2, Finsupp.mapDomain_apply_of_injective (MulAction.injective g), Finsupp.subtypeDomain_apply]
        have e1 : y = g • (g⁻¹ • y) := (smul_inv_smul g y).symm
        conv_lhs => rw [e1]
        rw [Finsupp.mapDomain_apply_of_injective (MulAction.injective g)] }
  refine ⟨Rep.ofHom F, Rep.ofHom Gm, ?_, ?_, ?_⟩
  · rw [Rep.hom_ofHom]
    change Function.Injective (Finsupp.mapDomain (Subtype.val : U → X) : (U →₀ ℤ) → (X →₀ ℤ))
    exact Finsupp.mapDomain_injective Subtype.val_injective
  · rw [Rep.hom_ofHom, Rep.hom_ofHom]
    intro y
    change Finsupp.subtypeDomain (· ∈ V) y = 0 ↔
      y ∈ Set.range (Finsupp.mapDomain (Subtype.val : U → X) : (U →₀ ℤ) → (X →₀ ℤ))
    constructor
    · intro hy0
      refine ⟨Finsupp.subtypeDomain (· ∈ U) y, ?_⟩
      ext x
      by_cases hx : x ∈ U
      · rw [show x = ((⟨x, hx⟩ : U) : X) from rfl, Finsupp.mapDomain_apply_of_injective Subtype.val_injective,
          Finsupp.subtypeDomain_apply]
      · rw [Finsupp.mapDomain_notin_range _ _ (by rintro ⟨u, rfl⟩; exact hx u.2)]
        have hxV : x ∈ V := (hUV x).2 hx
        have h1 := DFunLike.congr_fun hy0 ⟨x, hxV⟩
        simp only [Finsupp.subtypeDomain_apply, Finsupp.coe_zero, Pi.zero_apply] at h1
        exact h1.symm
    · rintro ⟨u, rfl⟩
      ext ⟨x, hx⟩
      rw [Finsupp.subtypeDomain_apply, Finsupp.mapDomain_notin_range _ _ ?_]
      · simp
      · rintro ⟨w, rfl⟩
        exact ((hUV _).1 hx) w.2
  · rw [Rep.hom_ofHom]
    intro h
    refine ⟨Finsupp.mapDomain (Subtype.val : V → X) h, ?_⟩
    ext ⟨y, hy⟩
    change Finsupp.mapDomain (Subtype.val : V → X) h ((⟨y, hy⟩ : V) : X) = h ⟨y, hy⟩
    exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.OrbStep
open CategoryTheory UpperTheory.V.KH

private theorem UpperTheory.V.KH.stabLe_sub {G X : Type} [Group G] [MulAction G X] {s : ℕ}
    (h : StabLe G X s) (U : SubMulAction G X) : StabLe G U s := by
  intro u
  rw [SubMulAction.stabilizer_of_subMul]
  exact h u

theorem UpperTheory.V.KH.orbStep :
    ∀ (G X : Type) [Group G] [MulAction G X] (A s : ℕ) (x : X), OrbLe G X (A + 1) → StabLe G X s →
      ∃ U V : SubMulAction G X, (∀ y, y ∈ V ↔ y ∉ U) ∧ Nonempty U ∧ MulAction.IsPretransitive G U ∧
        StabLe G U s ∧ StabLe G V s ∧ OrbLe G V A := by
  intro G X _ _ A s x hO hS
  let U : SubMulAction G X :=
    { carrier := MulAction.orbit G x
      smul_mem' := by
        rintro g y ⟨h, rfl⟩
        exact ⟨g * h, mul_smul _ _ _⟩ }
  have hxU : x ∈ U := MulAction.mem_orbit_self x
  refine ⟨U, Uᶜ, fun y => Iff.rfl, ⟨⟨x, hxU⟩⟩, ?_, stabLe_sub hS U, stabLe_sub hS Uᶜ, ?_⟩
  · refine ⟨fun a b => ?_⟩
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    obtain ⟨g, rfl⟩ := ha
    obtain ⟨h, rfl⟩ := hb
    refine ⟨h * g⁻¹, Subtype.ext ?_⟩
    change (h * g⁻¹) • g • x = h • x
    rw [smul_smul, inv_mul_cancel_right]
  · have hrel : ∀ a b : (Uᶜ : SubMulAction G X),
        (MulAction.orbitRel G (Uᶜ : SubMulAction G X)) a b ↔ (MulAction.orbitRel G X) a b := by
      intro a b
      rw [SubMulAction.orbitRel_of_subMul]
      rfl
    let f : MulAction.orbitRel.Quotient G (Uᶜ : SubMulAction G X) → MulAction.orbitRel.Quotient G X :=
      Quotient.map (fun a => (a : X)) (fun a b hab => (hrel a b).1 hab)
    let F : Option (MulAction.orbitRel.Quotient G (Uᶜ : SubMulAction G X)) →
        MulAction.orbitRel.Quotient G X := fun o => o.elim (Quotient.mk _ x) f
    have hF : Function.Injective F := by
      have hne : ∀ a : (Uᶜ : SubMulAction G X),
          (Quotient.mk _ (a : X) : MulAction.orbitRel.Quotient G X) ≠ Quotient.mk _ x := by
        intro a hax
        have h1 : (MulAction.orbitRel G X) (a : X) x := Quotient.exact hax
        exact a.2 h1
      rintro (_ | p) (_ | q) hpq
      · rfl
      · induction q using Quotient.inductionOn with
        | h b => exact absurd hpq.symm (hne b)
      · induction p using Quotient.inductionOn with
        | h a => exact absurd hpq (hne a)
      · induction p using Quotient.inductionOn with
        | h a =>
          induction q using Quotient.inductionOn with
          | h b =>
            congr 1
            exact Quotient.sound ((hrel a b).2 (Quotient.exact hpq))
    haveI : Finite (MulAction.orbitRel.Quotient G X) := hO.1
    haveI : Finite (Option (MulAction.orbitRel.Quotient G (Uᶜ : SubMulAction G X))) :=
      Finite.of_injective F hF
    haveI : Finite (MulAction.orbitRel.Quotient G (Uᶜ : SubMulAction G X)) :=
      Finite.of_injective some (Option.some_injective _)
    refine ⟨inferInstance, ?_⟩
    have h2 := Nat.card_le_card_of_injective F hF
    rw [Finite.card_option] at h2
    have h3 := hO.2
    omega
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.CardStep
open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.cardStep :
    ∀ (A B C : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (f : A →+ B) (g : B →+ C)
      (a c : ℕ), Function.Exact f g → CardLe A a → CardLe C c → CardLe B (a * c) := by
  intro A B C _ _ _ f g a c hex hA hC
  obtain ⟨hAf, ha⟩ := hA
  obtain ⟨hCf, hc⟩ := hC
  have hker : g.ker = f.range := AddMonoidHom.exact_iff.mp hex
  have h1 : Nat.card g.ker ≤ Nat.card A := by
    rw [hker]
    exact Nat.card_le_card_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have h2 : g.ker.index ≤ Nat.card C := by
    rw [AddSubgroup.index_ker]
    exact Finite.card_subtype_le _
  haveI hfin1 : Finite g.ker := by
    rw [hker]
    exact Finite.of_surjective _ f.rangeRestrict_surjective
  have hpos1 : 0 < Nat.card g.ker := Nat.card_pos
  have hpos2 : 0 < g.ker.index := by
    rw [AddSubgroup.index_ker]
    exact Nat.card_pos
  have hcard := AddSubgroup.card_mul_index g.ker
  refine ⟨Nat.finite_of_card_ne_zero (by rw [← hcard]; positivity), ?_⟩
  rw [← hcard]
  exact Nat.mul_le_mul (h1.trans ha) (h2.trans hc)
end

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.permCard :
    ∀ (G : Type) [Group G] (s j A : ℕ) (X : Type) [MulAction G X], OrbLe G X A → StabLe G X s →
      1 ≤ s → CardLe (groupHomology (permRep G X) (j + 1)) (s ^ (A * s ^ (j + 1))) := by
  intro G _ s j A
  have hempty : ∀ (A : ℕ) (X : Type) [MulAction G X] [IsEmpty X], 1 ≤ s →
      CardLe (groupHomology (permRep G X) (j + 1)) (s ^ (A * s ^ (j + 1))) := by
    intro A X _ _ hs
    obtain ⟨h1, h2⟩ := permEmpty G X (j + 1)
    exact ⟨h1, h2.trans (Nat.one_le_pow _ _ hs)⟩
  induction A with
  | zero =>
    intro X _ hO _ hs
    haveI : IsEmpty X := ⟨fun x => by
      obtain ⟨hf, hc⟩ := hO
      haveI : Nonempty (MulAction.orbitRel.Quotient G X) := ⟨Quotient.mk'' x⟩
      have := Nat.card_pos (α := MulAction.orbitRel.Quotient G X)
      omega⟩
    exact hempty 0 X hs
  | succ A ih =>
    intro X _ hO hS hs
    rcases isEmpty_or_nonempty X with hX | ⟨⟨x⟩⟩
    · exact hempty _ X hs
    · obtain ⟨U, V, hUV, hne, htr, hSU, hSV, hOV⟩ := orbStep G X A s x hO hS
      obtain ⟨f, g, hf, hfg, hg⟩ := permSplit G X U V hUV
      obtain ⟨⟨u, v, huv⟩, -⟩ := les G _ _ _ f g hf hfg hg (j + 1)
      have h1 := permTrans G U s j hSU
      have h2 := ih V hOV hSV hs
      have h3 := cardStep _ _ _ u v _ _ huv h1 h2
      have e : s ^ (s ^ (j + 1)) * s ^ (A * s ^ (j + 1)) = s ^ ((A + 1) * s ^ (j + 1)) := by
        rw [← pow_add]; congr 1; ring
      rwa [e] at h3
