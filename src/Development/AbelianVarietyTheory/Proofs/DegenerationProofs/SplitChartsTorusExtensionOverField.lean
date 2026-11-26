module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemRangeAppLEChartIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorusQuotientSchemeOverNilpotentThickening
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyTrivialTorusQuotientFlatSurjectiveCosets

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeightZeroSumOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.LocalWeightUnits

theorem exists_weight_zero_sum_one {A X J : Type} [CommRing A] [AddCommGroup X] [Fintype J] (P : X → AddSubgroup A)
    (one : 1 ∈ P 0) (mul : ∀ u v χ χ', u ∈ P χ → v ∈ P χ' → u * v ∈ P (χ + χ'))
    (ex : ∀ u : A, ∃ a : X →₀ A, (∀ χ, a χ ∈ P χ) ∧ u = a.sum fun _ x => x)
    (un : ∀ a : X →₀ A, (∀ χ, a χ ∈ P χ) → (a.sum fun _ x => x) = 0 → a = 0)
    (g : J → A) (δ : X) (hg : ∀ f, g f ∈ P δ) (hs : Ideal.span (Set.range g) = ⊤) :
    ∃ b : J → A, (∀ f, b f ∈ P 0) ∧ (∀ f, g f ∣ b f) ∧ ∑ f, b f = 1 := by
  classical
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hs.ge (Submodule.mem_top (x := (1 : A))))
  choose a ha hsum using fun f => ex (c f)
  let T : (X →₀ A) →ₗ[A] A := Finsupp.lsum A fun _ => LinearMap.id
  have hT : ∀ a : X →₀ A, T a = a.sum fun _ x => x := fun a => rfl
  let B : X →₀ A := ∑ f, g f • Finsupp.equivMapDomain (Equiv.addLeft δ) (a f) - Finsupp.single 0 1
  have hB : ∀ χ, B χ = ∑ f, g f * a f (-δ + χ) - Finsupp.single (0 : X) (1 : A) χ := fun χ => by
    simp [B]
  have hm : ∀ f χ, g f * a f (-δ + χ) ∈ P χ := fun f χ => by
    simpa using mul _ _ _ _ (hg f) (ha f (-δ + χ))
  have h0 : B = 0 := by
    refine un B (fun χ => ?_) ?_
    · rw [hB]
      refine sub_mem (sum_mem fun f _ => hm f χ) ?_
      rw [Finsupp.single_apply]
      split_ifs with h
      · exact h ▸ one
      · exact zero_mem _
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [← hT, map_sub, map_sum]
        simp only [map_smul]
        simp only [hT, Finsupp.sum_equivMapDomain, ← hsum, smul_eq_mul]
        rw [Finsupp.sum_single_index rfl, sub_eq_zero, ← hc]
        exact Finset.sum_congr rfl fun f _ => mul_comm _ _
  refine ⟨fun f => g f * a f (-δ + 0), fun f => hm f 0, fun f => Dvd.intro _ rfl, ?_⟩
  have := hB 0
  rw [h0, Finsupp.single_eq_same] at this
  exact (sub_eq_zero.1 this.symm)

variable {S : Scheme.{0}} {H : Over S} [GrpObj H] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ H}

theorem hasWt_iff {V : H.left.Opens} {u : Γ(H.left, V)} {χ : X} : HasWt i V u χ ↔ GlobalTheory.UU.IsWt i V u χ :=
  ⟨fun h Z t g h₁ h₂ => h Z t g h₂ h₁, fun h Z t g h₁ h₂ => h Z t g h₂ h₁⟩

def wtSpace (i : splitTorus S X ⟶ H) (V : H.left.Opens) (χ : X) : AddSubgroup Γ(H.left, V) where
  carrier := {u | GlobalTheory.UU.IsWt i V u χ}
  zero_mem' := GlobalTheory.UU.isWt_zero χ
  add_mem' := GlobalTheory.UU.IsWt.add
  neg_mem' := fun {u} hu Z t g h₁ h₂ => by rw [map_neg, map_neg, hu Z t g h₁ h₂, mul_neg]

theorem stable_basicOpen {V : H.left.Opens} (hV : Stable i V) {b : Γ(H.left, V)} (hb : HasWt i V b 0) :
    Stable i (H.left.basicOpen b) := by
  intro Y t g h
  have h₁ : ⊤ ≤ g.left ⁻¹ᵁ V := h.trans (g.left.preimage_mono (H.left.basicOpen_le b))
  have e := congrArg Y.left.basicOpen (hb Y t g h₁ (hV Y t g h₁))
  rw [charUnit_zero_val, map_one, _root_.one_mul, Scheme.basicOpen_appLE, Scheme.basicOpen_appLE] at e
  exact ((le_inf le_rfl h).trans e.ge).trans inf_le_right

theorem preimage_le_of_stable {V : H.left.Opens} (hV : Stable i V) :
    (snd (splitTorus S X) H).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) H ≫ i) * snd (splitTorus S X) H).left ⁻¹ᵁ V := by
  let U := (snd (splitTorus S X) H).left ⁻¹ᵁ V
  let Y : Over S := Over.mk (U.ι ≫ (splitTorus S X ⊗ H).hom)
  let j : Y ⟶ splitTorus S X ⊗ H := Over.homMk U.ι rfl
  have h := hV Y (j ≫ fst _ _) (j ≫ snd _ _) (fun y _ => y.2)
  rw [Category.assoc, ← MonObj.comp_mul] at h
  exact fun y hy => h (x := ⟨y, hy⟩) trivial

theorem exists_units {d : ℕ} {i : splitTorus S (Fin d → ℤ) ⟶ H} {V : H.left.Opens} (w : Fin d → Γ(H.left, V)ˣ)
    (hw : ∀ k, GlobalTheory.UU.IsWt i V (w k).val (Pi.single k 1)) :
    ∃ u : Multiplicative (Fin d → ℤ) →* Γ(H.left, V)ˣ, ∀ χ, HasWt i _ (u (Multiplicative.ofAdd χ)).val χ := by
  let e := Pi.basisFun ℤ (Fin d)
  let l : (Fin d → ℤ) →ₗ[ℤ] Additive Γ(H.left, V)ˣ := e.constr ℤ fun k => Additive.ofMul (w k)
  let M : AddSubgroup (Fin d → ℤ) :=
    { carrier := {χ | GlobalTheory.UU.IsWt i _ (Additive.toMul (l χ)).val χ}
      zero_mem' := by
        show GlobalTheory.UU.IsWt i _ (Additive.toMul (l 0)).val 0
        rw [map_zero]; exact GlobalTheory.UU.isWt_one
      add_mem' := fun {a c} ha hc => by
        show GlobalTheory.UU.IsWt i _ (Additive.toMul (l (a + c))).val (a + c)
        rw [map_add (f := _)]; exact GlobalTheory.UU.IsWt.mul ha hc
      neg_mem' := fun {a} ha => by
        show GlobalTheory.UU.IsWt i _ (Additive.toMul (l (-a))).val (-a)
        rw [map_neg]; exact GlobalTheory.UU.IsWt.inv ha }
  have hM : Submodule.span ℤ (Set.range e) ≤ M.toIntSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    show GlobalTheory.UU.IsWt i _ (Additive.toMul (l (e k))).val (e k)
    rw [Module.Basis.constr_basis, Pi.basisFun_apply]
    exact hw k
  exact ⟨AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom, fun χ => hasWt_iff.2 (hM (e.mem_span χ))⟩

theorem mem_basicOpen_of_mem {Z : Scheme.{0}} (C : Charts Z) {a a'} {j : C.I} {y : Z} (hy : y ∈ C.W a)
    (h : y ∈ Z.basicOpen (C.r a' j)) : y ∈ Z.basicOpen (C.r a j) := by
  have e := congrArg Z.basicOpen (C.trans a' a j)
  rw [Scheme.basicOpen_mul] at e
  erw [Z.basicOpen_res (C.r a' j) (homOfLE _).op, Z.basicOpen_res (C.r a j) (homOfLE _).op] at e
  exact (e.le ⟨⟨Z.basicOpen_le _ h, hy⟩, h⟩).2.2

theorem main : ∀ (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom] [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (i : splitTorus (Sp K) (Fin d → ℤ) ⟶ H), C.Torus c i → ∀ (a) (x : H.left), x ∈ C.W a → ∃ b : Γ(H.left, C.W a), HasWt i (C.W a) b 0 ∧ x ∈ H.left.basicOpen b ∧ Stable i (H.left.basicOpen b) ∧ ∃ u : Multiplicative (Fin d → ℤ) →* Γ(H.left, H.left.basicOpen b)ˣ, ∀ χ, HasWt i _ (u (Multiplicative.ofAdd χ)).val χ := by
  intro K _ H _ _ _ _ _ C d c i hT a x hx
  classical
  obtain ⟨ex, un⟩ := GlobalTheory.functions_graded_by_weights _ H _ i hT.hom (C.W a) (C.aff a) (preimage_le_of_stable (hT.stable a))
  let J := ∀ k : Fin d, {j : C.I // C.wt j = c k}
  let _ : Fintype J := Fintype.ofFinite J
  let g : J → Γ(H.left, C.W a) := fun f => ∏ k, C.r a (f k).1
  have hg : ∀ f, g f ∈ wtSpace i (C.W a) (∑ k : Fin d, Pi.single k 1) := fun f => by
    change GlobalTheory.UU.IsWt i _ (∏ k ∈ Finset.univ, C.r a (f k).1) (∑ k ∈ Finset.univ, Pi.single k 1)
    induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
    | empty => exact GlobalTheory.UU.isWt_one
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact (hasWt_iff.1 (hT.wt a _ k (f k).2)).mul ih
  have hs : Ideal.span (Set.range g) = ⊤ := by
    rw [← (C.aff a).self_le_iSup_basicOpen_iff]
    intro y hy
    choose a' j hj hyj using fun k => hT.bpf k y
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨g fun k => ⟨j k, hj k⟩, _, rfl⟩, ?_⟩
    rw [H.left.mem_basicOpen _ y hy, map_prod]
    exact IsUnit.prod_univ_iff.2 fun k => (H.left.mem_basicOpen _ y hy).1 (mem_basicOpen_of_mem C hy (hyj k))
  obtain ⟨b, hb, hd, h1⟩ := exists_weight_zero_sum_one (wtSpace i (C.W a)) GlobalTheory.UU.isWt_one
    (fun _ _ _ _ => GlobalTheory.UU.IsWt.mul) ex un g _ hg hs
  have hu : IsUnit (∑ f, (H.left.presheaf.germ (C.W a) x hx).hom (b f)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, h1, map_one]; exact isUnit_one
  obtain ⟨f, -, hf⟩ := IsLocalRing.exists_of_isUnit_sum hu
  refine ⟨b f, hasWt_iff.2 (hb f), (H.left.mem_basicOpen _ x hx).2 hf,
    stable_basicOpen (hT.stable a) (hasWt_iff.2 (hb f)), ?_⟩
  have hw : ∀ k, IsUnit (resG H.left (H.left.basicOpen_le (b f)) (C.r a (f k).1)) := fun k =>
    isUnit_of_dvd_unit (map_dvd _ ((Finset.dvd_prod_of_mem _ (Finset.mem_univ k)).trans (hd f)))
      (H.left.toRingedSpace.isUnit_res_basicOpen (b f))
  exact exists_units (fun k => (hw k).unit) fun k => (hasWt_iff.1 (hT.wt a _ k (f k).2)).res _

end GlobalTheory.LocalWeightUnits
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitChartsTorusExtensionOverField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.SplitChartsField

open GlobalTheory.UU GlobalTheory.AffineThickening GlobalTheory.TorusQuotientLift GlobalTheory.LocalWeightUnits

theorem geometricallyConnected_of_surjective {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z)
    [Surjective p] [GeometricallyConnected (p ≫ f)] : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have : ConnectedSpace ↥(pullback (p ≫ f) x) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  let q := (pullbackRightPullbackFstIso f x p).inv ≫ pullback.snd p (pullback.fst f x)
  have : Surjective q := inferInstance
  exact q.surjective.connectedSpace q.continuous

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] {B : Scheme.{0}}
  {i : splitTorus S X ⟶ G} {q : G.left ⟶ B} [IsAffineHom q] {V : B.Opens} (hi : IsMonHom i) (hV : IsAffineOpen V)
  (h₀ : ∀ a : Γ(G.left, q ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (q.app V).hom c = a)
  (hinj : Function.Injective (q.app V).hom) (hS : Stable i (q ⁻¹ᵁ V))
include hi hV h₀ hS


include hinj in
theorem exists_mem_basicOpen (P : Γ(G.left, q ⁻¹ᵁ V) → Prop)
    (hP : ∀ x ∈ q ⁻¹ᵁ V, ∃ b, IsWt i _ b 0 ∧ x ∈ G.left.basicOpen b ∧ P b) {y : B} (hy : y ∈ V) :
    ∃ c : Γ(B, V), y ∈ B.basicOpen c ∧ P ((q.app V).hom c) := by
  have hG : Graded i (q ⁻¹ᵁ V) :=
    GlobalTheory.functions_graded_by_weights _ G _ i hi _ (hV.preimage q) (preimage_le_of_stable hS)
  let s : Set Γ(B, V) := {c | P ((q.app V).hom c)}
  let α : Γ(B, V) →+* wtZero i (q ⁻¹ᵁ V) := (q.app V).hom.codRestrict _ fun c => (h₀ _).2 ⟨c, rfl⟩
  have hα : Function.Bijective α := ⟨fun a b h => hinj (congrArg Subtype.val h), fun a => by
    obtain ⟨c, hc⟩ := (h₀ a.1).1 a.2
    exact ⟨c, Subtype.ext hc⟩⟩
  have h1 : Ideal.span ((q.app V).hom '' s) = ⊤ := by
    rw [← (hV.preimage q).self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨b, hb, hxb, hPb⟩ := hP x hx
    obtain ⟨c, rfl⟩ := (h₀ b).1 hb
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨_, c, hPb, rfl⟩, hxb⟩
  have h2 : (1 : wtZero i (q ⁻¹ᵁ V)) ∈ (Ideal.span s).map α := hG.mem_map _ α 1 (by
    rw [Ideal.map_span]
    exact h1.ge trivial)
  have h3 : Ideal.span s = ⊤ := by
    obtain ⟨c, hc, e⟩ := (Ideal.mem_map_iff_of_surjective α hα.2).1 h2
    rw [Ideal.eq_top_iff_one, ← hα.1 (e.trans (map_one α).symm)]
    exact hc
  obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1 (hV.self_le_iSup_basicOpen_iff.2 h3 hy)
  exact ⟨c.1, hc, c.2⟩

theorem isWt_basicOpen_iff (c : Γ(B, V)) (a : Γ(G.left, q ⁻¹ᵁ B.basicOpen c)) :
    IsWt i _ a 0 ↔ ∃ c', (q.app (B.basicOpen c)).hom c' = a := by
  have e : q ⁻¹ᵁ B.basicOpen c = G.left.basicOpen ((q.app V).hom c) := Scheme.preimage_basicOpen _ _
  have hle := B.basicOpen_le c
  have hG : Graded i (q ⁻¹ᵁ V) :=
    GlobalTheory.functions_graded_by_weights _ G _ i hi _ (hV.preimage q) (preimage_le_of_stable hS)
  have hS' : Stable i (q ⁻¹ᵁ B.basicOpen c) := e ▸ stable_basicOpen hS (hasWt_iff.2 ((h₀ _).2 ⟨c, rfl⟩))
  have hG' : Graded i (q ⁻¹ᵁ B.basicOpen c) :=
    GlobalTheory.functions_graded_by_weights _ G _ i hi _ ((hV.basicOpen c).preimage q) (preimage_le_of_stable hS')
  have hw : ∀ x, IsWt i _ ((q.app (B.basicOpen c)).hom (rs hle x)) 0 := fun x => by
    rw [app_rs]
    exact ((h₀ _).2 ⟨x, rfl⟩).res _
  obtain ⟨v, hv⟩ : IsUnit (rs hle c) := B.toRingedSpace.isUnit_res_basicOpen c
  constructor
  · intro ha
    obtain ⟨n, y, hy⟩ := exists_eq_pow_mul (hV.preimage q) (q.preimage_mono hle) _ a e
    rw [← app_rs q hle] at hy
    obtain ⟨x, hx, hx'⟩ := hG.exists_lift hG' (rs (q.preimage_mono hle)) (fun _ _ hx => hx.res _) y (χ := 0)
      (hy ▸ mul_mem (pow_mem (S := wtZero i _) (hw c) n) ha)
    obtain ⟨x, rfl⟩ := (h₀ x).1 hx
    refine ⟨(v⁻¹).val ^ n * rs hle x, ?_⟩
    rw [map_mul, app_rs, hx', hy, ← hv, ← map_pow _ v.val, ← _root_.mul_assoc, ← map_mul, ← mul_pow,
      Units.inv_mul, one_pow, map_one, _root_.one_mul]
  · rintro ⟨c', rfl⟩
    obtain ⟨n, y, hy⟩ := exists_eq_pow_mul hV hle c c' rfl
    have e' : c' = (v⁻¹).val ^ n * rs hle y := by
      rw [hy, ← hv, ← _root_.mul_assoc, ← mul_pow, Units.inv_mul, one_pow, _root_.one_mul]
    have h1 : IsWt i _ (Units.map (q.app (B.basicOpen c)).hom.toMonoidHom v).val 0 := by
      have := hw c
      rwa [← hv] at this
    have h2 := h1.inv
    rw [neg_zero] at h2
    rw [e', map_mul, map_pow]
    exact mul_mem (pow_mem (S := wtZero i _) h2 n) (hw y)


omit hi h₀ hS in
include hinj in
theorem injective_basicOpen (c : Γ(B, V)) : Function.Injective (q.app (B.basicOpen c)).hom := by
  have hle := B.basicOpen_le c
  obtain ⟨v, hv⟩ : IsUnit (rs hle c) := B.toRingedSpace.isUnit_res_basicOpen c
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨n, y, hy⟩ := exists_eq_pow_mul hV hle c a rfl
  obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero (hV.preimage q) (q.preimage_mono hle) ((q.app V).hom c)
    ((q.app V).hom y) (Scheme.preimage_basicOpen _ _) (by rw [← app_rs q hle, hy, map_mul, ha, mul_zero])
  rw [← map_pow, ← map_mul, map_eq_zero_iff _ hinj] at hm
  have := congrArg (rs hle) hm
  rwa [map_mul, map_pow, map_zero, hy, ← hv, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
    Units.mul_right_eq_zero, Units.mul_right_eq_zero] at this


omit hi hV h₀ hS in
theorem main : ∀ (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom] [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (i : splitTorus (Sp K) (Fin d → ℤ) ⟶ H), GeometricallyConnected H.hom → C.Torus c i → ∃ (B : Over (Sp K)) (_ : GrpObj B) (q : H ⟶ B), IsAbelianScheme B ∧ IsMonHom q ∧ Flat q.left ∧ Surjective q.left ∧ IsAffineHom q.left ∧ IsPullback i (toUnit _) q (η[B]) ∧ ∀ a, ∃ (V : B.left.Opens) (h : C.W a = q.left ⁻¹ᵁ V), IsAffineOpen V ∧ ∀ u, HasWt i (C.W a) u 0 ↔ u ∈ Set.range (q.left.appLE V (C.W a) h.le).hom := by
  intro K _ H _ _ _ _ _ C d c i hc hT
  obtain ⟨B, q, hp, ha, V, hcov, hV⟩ := Charts.Torus.exists_proper_quotient K H C d c i hT
  obtain ⟨hm, hf, hs, hsm, hfib⟩ := GlobalTheory.LocTriv.main (Sp K) (Fin d → ℤ) H B i q hT.hom ha fun y => by
    obtain ⟨a, hy⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge (Set.mem_univ y))
    obtain ⟨haff, h, hinj, h₀⟩ := hV a
    have hS := hT.stable a
    have hl := GlobalTheory.LocalWeightUnits.main K H C d c i hT a
    generalize C.W a = W at h hinj h₀ hS hl
    subst h
    rw [Scheme.Hom.appLE_eq_app] at hinj h₀
    have h₀' := fun u => hasWt_iff.symm.trans (h₀ u)
    obtain ⟨b, hb, hb₁, u, hu⟩ := exists_mem_basicOpen hT.hom haff h₀' hinj hS
      (fun b => Stable i (H.left.basicOpen b) ∧ ∃ u : Multiplicative (Fin d → ℤ) →* Γ(H.left, H.left.basicOpen b)ˣ,
        ∀ χ, HasWt i _ (u (Multiplicative.ofAdd χ)).val χ)
      (fun x hx => (hl x hx).imp fun b hb => ⟨hasWt_iff.1 hb.1, hb.2⟩) hy
    refine ⟨B.left.basicOpen b, hb, haff.basicOpen b, isWt_basicOpen_iff hT.hom haff h₀' hS b,
      injective_basicOpen haff hinj b, ?_⟩
    rw [Scheme.preimage_basicOpen]
    exact ⟨preimage_le_of_stable hb₁, u, fun χ => hasWt_iff.1 (hu χ)⟩
  obtain ⟨g, hcomm, hq, hker⟩ :=
    GlobalTheory.grpObj_of_flat_coset_quotient (Sp K) H _ B i q hT.hom hm hf hs inferInstance hfib
  have : GeometricallyConnected (q.left ≫ B.hom) := by rwa [Over.w]
  refine ⟨B, g, q, ⟨hcomm, hsm inferInstance, hp, geometricallyConnected_of_surjective q.left B.hom⟩, hq, hf, hs, ha,
    hker, fun a => ?_⟩
  obtain ⟨haff, h, -, h₀⟩ := hV a
  exact ⟨V a, h, haff, h₀⟩

end GlobalTheory.SplitChartsField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitChartsTorusExtensionOverFieldStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitCharts_torus_extension_over_field : ∀ (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom] [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (i : splitTorus (Sp K) (Fin d → ℤ) ⟶ H), GeometricallyConnected H.hom → C.Torus c i → ∃ (B : Over (Sp K)) (_ : GrpObj B) (q : H ⟶ B), IsAbelianScheme B ∧ IsMonHom q ∧ Flat q.left ∧ Surjective q.left ∧ IsAffineHom q.left ∧ IsPullback i (toUnit _) q (η[B]) ∧ ∀ a, ∃ (V : B.left.Opens) (h : C.W a = q.left ⁻¹ᵁ V), IsAffineOpen V ∧ ∀ u, HasWt i (C.W a) u 0 ↔ u ∈ Set.range (q.left.appLE V (C.W a) h.le).hom :=
  GlobalTheory.SplitChartsField.main
end
