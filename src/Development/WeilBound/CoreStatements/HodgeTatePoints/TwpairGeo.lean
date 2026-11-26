module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeFiniteProjectiveBaseChange
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenHopfOrder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.TwpairAlg
open GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT

noncomputable section

namespace PositivityTheory.HtPt.Twpair

section Ind

variable {R : Type} [CommRing R] {T : Type} [CommGroup T]

theorem translate_mem {A : Subalgebra R (T → R)} (hA : IsHopfOrder A) {f : T → R} (hf : f ∈ A) (t : T) :
    (fun h => f (t * h)) ∈ A := by
  have key : ∀ g ∈ prodSpan A, (fun h => g (t, h)) ∈ A := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, -, b, hb, rfl⟩ := h
      exact A.smul_mem hb (a t)
    | zero => exact A.zero_mem
    | add x y _ _ hx hy => exact A.add_mem hx hy
    | smul r x _ hx => exact A.smul_mem hx r
  exact key _ (hA.comul f hf)


omit [CommGroup T] in
theorem mul_mem_prodSpan {A : Subalgebra R (T → R)} {a b : T → R} (ha : a ∈ A) (hb : b ∈ A)
    {g : T × T → R} (hg : g ∈ prodSpan A) : (fun z => a z.1 * b z.2 * g z) ∈ prodSpan A := by
  induction hg using Submodule.span_induction with
  | mem x h =>
    obtain ⟨a', ha', b', hb', rfl⟩ := h
    refine Submodule.subset_span ⟨a * a', A.mul_mem ha ha', b * b', A.mul_mem hb hb', ?_⟩
    funext z
    simp only [Pi.mul_apply]
    ring
  | zero =>
    have := (prodSpan A).zero_mem
    convert this using 1
    funext z
    simp
  | add x y _ _ hx hy =>
    have := (prodSpan A).add_mem hx hy
    convert this using 1
    funext z
    simp [mul_add]
  | smul r x _ hx =>
    have := (prodSpan A).smul_mem r hx
    convert this using 1
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    ring


open Classical in
def extZero (H : Subgroup T) (t : T) (a : H → R) : T → R :=
  fun x => if h : t⁻¹ * x ∈ H then a ⟨_, h⟩ else 0


open Classical in
def extZero₂ (H : Subgroup T) (t s : T) (g : H × H → R) : T × T → R :=
  fun z => if h : t⁻¹ * z.1 ∈ H ∧ s⁻¹ * z.2 ∈ H then g (⟨_, h.1⟩, ⟨_, h.2⟩) else 0

theorem extZero_mem {H : Subgroup T} {A : Subalgebra R (H → R)} (hA : IsHopfOrder A) (t : T) {a : H → R}
    (ha : a ∈ A) : extZero H t a ∈ indOrder H.subtype A := by
  intro u
  by_cases hu : t⁻¹ * u ∈ H
  · have := translate_mem hA ha ⟨_, hu⟩
    convert this using 1
    funext h
    have h1 : t⁻¹ * (u * H.subtype h) ∈ H := by
      rw [← mul_assoc]; exact H.mul_mem hu h.2
    simp only [extZero]
    rw [dite_eq_left h1]
    congr 1
    exact Subtype.ext (mul_assoc _ _ _).symm
  · have : (fun h : H => extZero H t a (u * H.subtype h)) = 0 := by
      funext h
      have h1 : ¬ t⁻¹ * (u * H.subtype h) ∈ H := by
        rw [← mul_assoc]
        exact fun h1 => hu ((H.mul_mem_cancel_right h.2).1 h1)
      simp only [extZero]
      rw [dite_eq_right h1]
      rfl
    rw [this]
    exact A.zero_mem

theorem extZero₂_mem {H : Subgroup T} {A : Subalgebra R (H → R)} (hA : IsHopfOrder A) (t s : T)
    {g : H × H → R} (hg : g ∈ prodSpan A) : extZero₂ H t s g ∈ prodSpan (indOrder H.subtype A) := by
  induction hg using Submodule.span_induction with
  | mem x h =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    refine Submodule.subset_span ⟨_, extZero_mem hA t ha, _, extZero_mem hA s hb, ?_⟩
    funext z
    by_cases h1 : t⁻¹ * z.1 ∈ H <;> by_cases h2 : s⁻¹ * z.2 ∈ H <;> simp [extZero, extZero₂, h1, h2]
  | zero =>
    have : extZero₂ H t s (0 : H × H → R) = 0 := by
      funext z
      simp [extZero₂]
    rw [this]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have := Submodule.add_mem _ hx hy
    convert this using 1
    funext z
    simp only [extZero₂, Pi.add_apply]
    split_ifs <;> simp
  | smul r x _ hx =>
    have := Submodule.smul_mem _ r hx
    convert this using 1
    funext z
    simp [extZero₂] 

theorem pair_ind : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (H : Subgroup T) (A : Subalgebra R (H → R)) (β : T →* T →* Rˣ), IsHopfOrder A → (fun z : H × H => ((β z.1 z.2 : Rˣ) : R)) ∈ prodSpan A → (fun z : T × T => ((β z.1 z.2 : Rˣ) : R)) ∈ prodSpan (indOrder H.subtype A) := by
  intro R _ _ _ T _ _ H A β hA hβ
  classical
  have := Fintype.ofFinite (T ⧸ H)
  have h1 : ∀ t s : T, (fun w : H × H => ((β (t * w.1) (s * w.2) : Rˣ) : R)) ∈ prodSpan A := by
    intro t s
    have ha := char_mem_hopfOrder R H A hA ((β.flip s).comp H.subtype)
    have hb := char_mem_hopfOrder R H A hA ((β t).comp H.subtype)
    have := Submodule.smul_mem _ ((β t s : Rˣ) : R) (mul_mem_prodSpan ha hb hβ)
    convert this using 1
    funext w
    simp only [Pi.smul_apply, smul_eq_mul, MonoidHom.map_mul, MonoidHom.mul_apply,
      MonoidHom.flip_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, Units.val_mul]
    ring
  have key : ∀ (c : T ⧸ H) (x : T), c.out⁻¹ * x ∈ H ↔ c = (x : T ⧸ H) := by
    intro c x
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  have e : (fun z : T × T => ((β z.1 z.2 : Rˣ) : R)) = ∑ c : (T ⧸ H) × (T ⧸ H),
      extZero₂ H c.1.out c.2.out (fun w : H × H => ((β (c.1.out * w.1) (c.2.out * w.2) : Rˣ) : R)) := by
    funext z
    rw [Finset.sum_apply, Finset.sum_eq_single ((z.1 : T ⧸ H), (z.2 : T ⧸ H))]
    · simp only [extZero₂]
      rw [dite_eq_left ⟨(key _ _).2 rfl, (key _ _).2 rfl⟩]
      simp only [mul_inv_cancel_left]
    · intro c _ hc
      simp only [extZero₂]
      rw [dite_eq_right]
      rintro ⟨a, b⟩
      exact hc (Prod.ext ((key _ _).1 a) ((key _ _).1 b))
    · simp
  rw [e]
  exact Submodule.sum_mem _ fun c _ => extZero₂_mem hA _ _ (h1 _ _)

end Ind

section Val

variable {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]

theorem mem_maximalIdeal_iff [IsLocalRing O] (hv : v.Integers O) (x : O) :
    x ∈ IsLocalRing.maximalIdeal O ↔ v (algebraMap O C x) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne (hv.map_le_one x) h, fun h => h.ne⟩

theorem prime_eq_bot_or_maximal [IsLocalRing O] (hv : v.Integers O) (P : Ideal O) [hP : P.IsPrime] :
    P = ⊥ ∨ P = IsLocalRing.maximalIdeal O := by
  by_cases h : P = ⊥
  · exact Or.inl h
  right
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine le_antisymm (IsLocalRing.le_maximalIdeal hP.ne_top) fun y hy => ?_
  rw [mem_maximalIdeal_iff hv] at hy
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (hv.valuation_pos_iff_ne_zero.2 hx0) hy
  have : x ∣ y ^ n := hv.dvd_of_le (by rw [map_pow, map_pow]; exact hn.le)
  exact hP.mem_of_pow_mem n (Ideal.mem_of_dvd P this hx)

theorem henselian [IsAlgClosed C] [IsLocalRing O] (hv : v.Integers O) : HenselianLocalRing O where
  is_henselian f hf a₀ h₀ _ := by
    rw [mem_maximalIdeal_iff hv] at h₀
    have hm : (f.map (algebraMap O C)).Monic := hf.map _
    have e := (IsAlgClosed.splits (f.map (algebraMap O C))).eval_eq_prod_roots_of_monic hm (algebraMap O C a₀)
    rw [Polynomial.eval_map_algebraMap, Polynomial.aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval] at e
    have : ∃ r ∈ (f.map (algebraMap O C)).roots, v (algebraMap O C a₀ - r) < 1 := by
      by_contra hne
      push Not at hne
      rw [e, map_multiset_prod] at h₀
      refine absurd h₀ (not_lt.2 (Multiset.one_le_prod_of_one_le fun x hx => ?_))
      simp only [Multiset.map_map, Multiset.mem_map] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      exact hne r hr
    obtain ⟨r, hr, hlt⟩ := this
    have hr1 : v r ≤ 1 := by
      have : r = algebraMap O C a₀ - (algebraMap O C a₀ - r) := by ring
      rw [this]
      exact v.map_sub_le (hv.map_le_one _) hlt.le
    obtain ⟨a, rfl⟩ := hv.exists_of_le_one hr1
    refine ⟨a, ?_, ?_⟩
    · have := (Polynomial.mem_roots hm.ne_zero).1 hr
      exact (Polynomial.isRoot_map_iff hv.hom_inj).1 this
    · rw [mem_maximalIdeal_iff hv, map_sub, Valuation.map_sub_swap]
      exact hlt

end Val

section Lev

variable {La : Type} [AddCommGroup La]

theorem lev_surjective (p n : ℕ) : Function.Surjective (lev p n : La → LevGrp La p n) := fun t => by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ t.toAdd
  exact ⟨a, congrArg Multiplicative.ofAdd ha⟩

theorem finite_levGrp [Module.Finite ℤ La] {p : ℕ} (hp : p ≠ 0) (n : ℕ) : Finite (LevGrp La p n) := by
  have : Finite (La ⧸ LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))) := by
    refine Module.finite_of_fg_torsion _ fun x => ?_
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine ⟨⟨((p ^ n : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by positivity)⟩, ?_⟩
    change Submodule.Quotient.mk (((p ^ n : ℕ) : ℤ) • a) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨a, by simp only [LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul]⟩
  infer_instance

theorem exists_bichar {O : Type} [CommRing O] (p n : ℕ) (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : Oˣ) (hζ : ζ ^ p ^ n = 1) :
    ∃ β : LevGrp La p n →* LevGrp La p n →* Oˣ, ∀ a b, β (lev p n a) (lev p n b) = ζ ^ B a b := by
  let N := LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))
  let z : ℤ →ₗ[ℤ] Additive Oˣ := LinearMap.toSpanSingleton ℤ _ (Additive.ofMul ζ)
  have hz : ∀ k : ℤ, z ((p ^ n) • k) = 0 := by
    intro k
    rw [map_nsmul, LinearMap.toSpanSingleton_apply, smul_comm, ← ofMul_pow, hζ]
    simp
  let B' : La →ₗ[ℤ] La →ₗ[ℤ] Additive Oˣ := B.compr₂ z
  let B'' : (La ⧸ N) →ₗ[ℤ] (La ⧸ N) →ₗ[ℤ] Additive Oˣ := B'.liftQ₂ N N
    (by
      rintro _ ⟨a, rfl⟩
      rw [LinearMap.mem_ker]
      ext b
      simp only [B', LinearMap.smul_apply, LinearMap.id_apply, LinearMap.compr₂_apply, map_nsmul,
        LinearMap.zero_apply]
      rw [← map_nsmul, hz])
    (by
      rintro _ ⟨a, rfl⟩
      rw [LinearMap.mem_ker]
      ext b
      simp only [B', LinearMap.smul_apply, LinearMap.id_apply, LinearMap.compr₂_apply, map_nsmul,
        LinearMap.zero_apply, LinearMap.flip_apply]
      rw [← map_nsmul, hz])
  refine ⟨{ toFun := fun x => { toFun := fun y => (B'' x.toAdd y.toAdd).toMul
                                map_one' := by simp
                                map_mul' := by simp }
            map_one' := by ext; simp
            map_mul' := by intros; ext; simp }, fun a b => ?_⟩
  change (z (B a b)).toMul = _
  rw [LinearMap.toSpanSingleton_apply, ← ofMul_zpow]
  rfl

end Lev

end PositivityTheory.HtPt.Twpair
end
end

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.SubOrder

noncomputable section

namespace PositivityTheory.HtPt.Twpair

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

omit [IsDomain R] in
theorem mem_of_finite [IsLocalRing R] {X : Over (Spec (CommRingCat.of R))} (W : X.left.Opens)
    (hW : ∀ x : X.left, X.hom x = IsLocalRing.closedPoint R → x ∈ W)
    (Y : Over (Spec (CommRingCat.of R))) (hY : IsFinite Y.hom) (h : Y ⟶ X) (z : Y.left) :
    h.left z ∈ W := by
  have : IsFinite (h.left ≫ X.hom) := by rw [Over.w h]; exact hY
  exact (GlobalTheory.preimage_eq_top_of_closedFibre_subset (R := CommRingCat.of R) X.hom W hW h.left).ge (Set.mem_univ z)

theorem isFinOpenSub [IsLocalRing R] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (hfin : IsFinite (U.ι ≫ Γ.G.hom))
    (hU : ∀ x : Γ.G.left, Γ.G.hom x = IsLocalRing.closedPoint R → x ∈ U) : Γ.IsFinOpenSub U := by
  have hV : IsFinite (openOver Γ.G U).hom := hfin
  refine ⟨hfin, ?_, ?_, ?_⟩
  · intro x
    refine mem_of_finite U hU (𝟙_ _) ?_ η[Γ.G] x
    show IsFinite (𝟙 _)
    infer_instance
  · intro S x y hx hy z
    obtain ⟨x', rfl⟩ := exists_factor_openIncl U x hx
    obtain ⟨y', rfl⟩ := exists_factor_openIncl U y hy
    have hP : IsFinite (openOver Γ.G U ⊗ openOver Γ.G U).hom := by
      rw [Over.tensorObj_hom]
      infer_instance
    have key := mem_of_finite U hU _ hP
      ((fst _ _ ≫ openIncl Γ.G U) * (snd _ _ ≫ openIncl Γ.G U))
    have heq : x' ≫ openIncl Γ.G U * y' ≫ openIncl Γ.G U =
        lift x' y' ≫ ((fst _ _ ≫ openIncl Γ.G U) * (snd _ _ ≫ openIncl Γ.G U)) := by
      rw [comp_mul]
      simp
    rw [heq]
    simpa using key ((lift x' y').left z)
  · intro S x hx z
    obtain ⟨x', rfl⟩ := exists_factor_openIncl U x hx
    have key := mem_of_finite U hU _ hV (openIncl Γ.G U)⁻¹
    have heq : (x' ≫ openIncl Γ.G U)⁻¹ = x' ≫ (openIncl Γ.G U)⁻¹ := by
      simp [Hom.inv_def]
    rw [heq]
    simpa using key (x'.left z)

theorem regularAt_generic [Finite T] (Γ : QFGroup R T) (f : T → FractionRing R) (g : Γ.G.left)
    (hg : (Γ.G.hom g).asIdeal = ⊥) : Γ.RegularAt f g := by
  obtain ⟨d, hd, V, hgV, s, hs⟩ := RegDenom.exists_denom_regularAt R T Γ f g
  let σ : Γ(Γ.G.left, V) := RegDenom.structHom Γ.G.hom V d
  let W := Γ.G.left.basicOpen σ
  have hW : W ≤ V := Γ.G.left.basicOpen_le σ
  have hgW : g ∈ W := by
    have e : W = V ⊓ Γ.G.hom ⁻¹ᵁ (Spec (CommRingCat.of R)).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv d) :=
      Scheme.basicOpen_appLE _ _ _ _ _
    rw [e, basicOpen_eq_of_affine]
    refine ⟨hgV, ?_⟩
    change d ∉ (Γ.G.hom g).asIdeal
    rw [hg]
    exact hd
  let ρ : Γ(Γ.G.left, V) →+* Γ(Γ.G.left, W) := (Γ.G.left.presheaf.map (homOfLE hW).op).hom
  have hu : IsUnit (ρ σ) := Γ.G.left.toRingedSpace.isUnit_res_basicOpen σ
  obtain ⟨u, hu⟩ := hu.exists_left_inv
  refine ⟨W, hgW, u * ρ s, fun t ht => ?_⟩
  have htV : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ V := fun z hz => hW (ht hz)
  have hρ : ∀ a, RegDenom.valHom (Γ.pt t).left W ht (ρ a) = RegDenom.valHom (Γ.pt t).left V htV a := by
    intro a
    have := Scheme.Hom.map_appLE (Γ.pt t).left ht (homOfLE hW).op
    simp only [RegDenom.valHom, RingHom.comp_apply]
    rw [← this]
    rfl
  have h1 := congrArg (RegDenom.valHom (Γ.pt t).left W ht) hu
  rw [map_mul, map_one, hρ, RegDenom.valHom_structHom Γ.G.hom _ _ (Over.w (Γ.pt t)) V htV d] at h1
  rw [← RegDenom.valHom_apply, map_mul, hρ, RegDenom.valHom_apply _ _ _ s, hs t htV]
  change _ * (_ * f t) = f t
  rw [← _root_.mul_assoc, h1, _root_.one_mul]

theorem valHom_top_comp {B C : Type} [CommRing B] [CommRing C] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X)
    (φ : B →+* C) (s : Γ(X, ⊤)) :
    valAt (Spec.map (CommRingCat.ofHom φ) ≫ x) ⊤ le_top s = φ (valAt x ⊤ le_top s) := by
  have e : (x.appLE ⊤ ⊤ le_top).hom s =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (valAt x ⊤ le_top s) := by
    simp [valAt]
  have e1 := valHom_appLE (Spec.map (CommRingCat.ofHom φ)) x (V := ⊤) (W := ⊤) le_top le_top le_top s
  have e2 := valHom_spec_top φ le_top (valAt x ⊤ le_top s)
  exact e1.symm.trans ((congrArg _ e).trans e2)

section sec

variable {Γ : QFGroup R T} {U : Γ.G.left.Opens} {hU : IsAffineOpen U}
variable [Algebra R Γ(Γ.G.left, U)]
  (hρ : hU.fromSpec ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R Γ(Γ.G.left, U))))

include hρ

theorem exists_tensor_of_prod (s : Γ((Γ.G ⊗ Γ.G).left, ⊤)) :
    ∃ c : Γ(Γ.G.left, U) ⊗[R] Γ(Γ.G.left, U), ∀ (a b : T) (ha : ⊤ ≤ (Γ.pt a).left ⁻¹ᵁ U)
      (hb : ⊤ ≤ (Γ.pt b).left ⁻¹ᵁ U),
      valAt (lift (Γ.pt a) (Γ.pt b)).left ⊤ le_top s =
        Algebra.TensorProduct.productMap (valAlg hρ a ha) (valAlg hρ b hb) c := by
  let B := Γ(Γ.G.left, U)
  let Q : Over (Spec (CommRingCat.of R)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (B ⊗[R] B))))
  let iL : B →+* B ⊗[R] B := (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toRingHom
  let iR : B →+* B ⊗[R] B := (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B).toRingHom
  let x : Q ⟶ Γ.G := Over.homMk (Spec.map (CommRingCat.ofHom iL) ≫ hU.fromSpec) (by
    simp only [Category.assoc, Q, Over.mk_hom]
    rw [hρ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2)
  let y : Q ⟶ Γ.G := Over.homMk (Spec.map (CommRingCat.ofHom iR) ≫ hU.fromSpec) (by
    simp only [Category.assoc, Q, Over.mk_hom]
    rw [hρ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp [iR, Algebra.TensorProduct.algebraMap_apply'])
  refine ⟨valAt (lift x y).left ⊤ le_top s, ?_⟩
  intro a b ha hb
  let φ : B ⊗[R] B →+* FractionRing R :=
    (Algebra.TensorProduct.productMap (valAlg hρ a ha) (valAlg hρ b hb)).toRingHom
  let w : genPt R ⟶ Q := Over.homMk (Spec.map (CommRingCat.ofHom φ)) (by
    simp only [Q, Over.mk_hom, genPt]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp [φ])
  have hwx : w ≫ x = Γ.pt a := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, w, x, Over.homMk_left]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : φ.comp iL = valHom (Γ.pt a).left U ha := by
      ext r
      simp [φ, iL]
      try rfl
    rw [this]
    exact spec_valHom_fromSpec _ hU ha
  have hwy : w ≫ y = Γ.pt b := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, w, y, Over.homMk_left]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : φ.comp iR = valHom (Γ.pt b).left U hb := by
      ext r
      simp [φ, iR]
      try rfl
    rw [this]
    exact spec_valHom_fromSpec _ hU hb
  have hw : w ≫ lift x y = lift (Γ.pt a) (Γ.pt b) := by
    rw [comp_lift, hwx, hwy]
  have e : (lift (Γ.pt a) (Γ.pt b)).left = Spec.map (CommRingCat.ofHom φ) ≫ (lift x y).left := by
    rw [← hw]; rfl
  have e2 := valHom_congr e ⊤ le_top le_top
  exact (DFunLike.congr_fun e2 s).trans (valHom_top_comp (lift x y).left φ s)

end sec

theorem exists_order [ValuationRing R] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (hF : Γ.IsFinOpenSub U) :
    ∃ A : Subalgebra R (subH Γ hF → R), IsHopfOrder A ∧
      (∀ f ∈ A, ∃ s : Γ(Γ.G.left, U), ∀ (t : subH Γ hF) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U),
        valAt (Γ.pt t).left U h s = algebraMap R _ (f t)) ∧
      ∀ (s : Γ((Γ.G ⊗ Γ.G).left, ⊤)) (g : subH Γ hF × subH Γ hF → R),
        (∀ z : subH Γ hF × subH Γ hF, valAt (lift (Γ.pt z.1) (Γ.pt z.2)).left ⊤ le_top s = algebraMap R _ (g z)) →
        g ∈ prodSpan A := by
  have hU := isAffineOpen_of_fin Γ hF
  letI : Algebra R Γ(Γ.G.left, U) := (secRho Γ hU).toAlgebra
  have hρ : hU.fromSpec ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R Γ(Γ.G.left, U))) :=
    fromSpec_hom Γ hU
  have hfin := sec_finite hρ hF
  have inj : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  have hval : ∀ (t : subH Γ hF) (s : Γ(Γ.G.left, U)),
      ∃ r : R, algebraMap R (FractionRing R) r = valAlg hρ t t.2 s := by
    intro t s
    have h1 : IsIntegral R s := Algebra.IsIntegral.isIntegral s
    exact IsIntegrallyClosed.isIntegral_iff.1 (h1.map (valAlg hρ t t.2))
  choose Φf hΦf using hval
  let Φ : Γ(Γ.G.left, U) →ₐ[R] (subH Γ hF → R) :=
    { toFun := fun s t => Φf t s
      map_one' := funext fun t => inj (by simp [hΦf])
      map_mul' := fun a b => funext fun t => inj (by simp [hΦf])
      map_zero' := funext fun t => inj (by simp [hΦf])
      map_add' := fun a b => funext fun t => inj (by simp [hΦf])
      commutes' := fun r => funext fun t => inj (by
        rw [hΦf, AlgHom.commutes]; rfl) }
  have hΦ : ∀ (s : Γ(Γ.G.left, U)) (t : subH Γ hF) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U),
      valAt (Γ.pt t).left U h s = algebraMap R _ (Φ s t) := fun s t h => (hΦf t s).symm
  have key : ∀ c' : Γ(Γ.G.left, U) ⊗[R] Γ(Γ.G.left, U), ∃ g ∈ prodSpan Φ.range, ∀ z : subH Γ hF × subH Γ hF,
      algebraMap R (FractionRing R) (g z) =
        Algebra.TensorProduct.productMap (valAlg hρ z.1 z.1.2) (valAlg hρ z.2 z.2.2) c' := by
    intro c'
    induction c' with
    | tmul a b =>
      refine ⟨fun z => Φ a z.1 * Φ b z.2, Submodule.subset_span ⟨Φ a, ⟨a, rfl⟩, Φ b, ⟨b, rfl⟩, rfl⟩, fun z => ?_⟩
      simp only [map_mul, Algebra.TensorProduct.productMap_apply_tmul]
      exact congrArg₂ (· * ·) (hΦ a z.1 z.1.2).symm (hΦ b z.2 z.2.2).symm
    | add a b ha hb =>
      obtain ⟨g, hg, hg'⟩ := ha
      obtain ⟨g₂, hg₂, hg₂'⟩ := hb
      exact ⟨g + g₂, Submodule.add_mem _ hg hg₂, fun z => by simp [hg', hg₂']⟩
  have hfinA : Module.Finite R Φ.range :=
    Module.Finite.of_surjective Φ.rangeRestrict.toLinearMap Φ.rangeRestrict_surjective
  refine ⟨Φ.range, ⟨hfinA, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · have htf : Module.IsTorsionFree R Φ.range :=
      Function.Injective.moduleIsTorsionFree Φ.range.val.toLinearMap Subtype.val_injective (fun _ _ => rfl)
    have : Module.Flat R Φ.range := by
      rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
      exact htf
    have : Module.Free R Φ.range := Module.free_of_flat_of_isLocalRing
    infer_instance
  · classical
    have := Fintype.ofFinite (subH Γ hF)
    let v : subH Γ hF → Γ(Γ.G.left, U) →+* FractionRing R := fun t => RegDenom.valHom (Γ.pt t.1).left U t.2
    have hv : Function.Injective v := by
      intro s t e
      have hst := RegDenom.eq_of_valHom_eq hU s.2 t.2 e
      obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := inferInstance
      exact Subtype.ext (Γ.pt_inj s.1 t.1 x x (by rw [hst]))
    have h1 : ∀ h : subH Γ hF, ∃ d : R, d ≠ 0 ∧ d • (Pi.single h 1 : subH Γ hF → R) ∈ Φ.range := by
      intro h
      obtain ⟨d, hd, b, hb⟩ := RegDenom.exists_denom_of_injective (algebraMap R Γ(Γ.G.left, U)) v hv
        (fun t r => val_algebraMap hρ t.1 t.2 r) (fun t => algebraMap R _ ((Pi.single h 1 : subH Γ hF → R) t))
      refine ⟨d, hd, b, funext fun t => inj ?_⟩
      refine (hΦ b t t.2).symm.trans ((hb t).trans ?_)
      rw [← map_mul]
      rfl
    choose d hd hdA using h1
    refine ⟨∏ h, d h, Finset.prod_ne_zero_iff.2 fun h _ => hd h, fun f => ?_⟩
    have e : (∏ h, d h) • f =
        ∑ h, (f h * ∏ h' ∈ Finset.univ.erase h, d h') • (d h • (Pi.single h 1 : subH Γ hF → R)) := by
      funext t
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      rw [Finset.sum_eq_single t]
      · rw [Pi.single_eq_same, ← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ t)]
        ring
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb.symm]
      · simp
    rw [e]
    exact Subalgebra.sum_mem _ fun h _ => Subalgebra.smul_mem _ (hdA h) _
  · rintro _ ⟨s, rfl⟩
    obtain ⟨c, hc⟩ := exists_tensor hρ hF s
    obtain ⟨g, hg, hg'⟩ := key c
    have : (fun z : subH Γ hF × subH Γ hF => (Φ s) (z.1 * z.2)) = g := by
      funext z
      apply inj
      rw [hg' z, ← hc z.1 z.2 z.1.2 z.2.2 (z.1 * z.2).2]
      exact (hΦ s (z.1 * z.2) (z.1 * z.2).2).symm
    change (fun z : subH Γ hF × subH Γ hF => (Φ s) (z.1 * z.2)) ∈ prodSpan Φ.range
    rw [this]
    exact hg
  · rintro _ ⟨s, rfl⟩
    obtain ⟨c, hc⟩ := exists_inv hρ hF s
    refine ⟨c, funext fun x => inj ?_⟩
    have e1 := hc x x.2 (x⁻¹).2
    have e2 := hΦ s x⁻¹ (x⁻¹).2
    have e3 := hΦ c x x.2
    exact e3.symm.trans (Eq.trans (valAlg_apply hρ _ _ _).symm (e1.symm.trans e2))
  · rintro _ ⟨s, rfl⟩
    exact ⟨s, fun t h => hΦ s t h⟩
  · intro s g hg
    obtain ⟨c, hc⟩ := exists_tensor_of_prod hρ s
    obtain ⟨g', hg1, hg2⟩ := key c
    have : g = g' := funext fun z => inj (by rw [hg2 z, ← hc z.1 z.2 z.1.2 z.2.2, hg z])
    rw [this]
    exact hg1

theorem bichar_mem_prodSpan [ValuationRing R] (hH : HenselianLocalRing R)
    (hdim : ∀ P : PrimeSpectrum R, P.asIdeal = ⊥ ∨ P = IsLocalRing.closedPoint R) [Finite T] (Γ : QFGroup R T)
    (β : T →* T →* Rˣ) (s : Γ((Γ.G ⊗ Γ.G).left, ⊤))
    (hs : ∀ a b, valAt (lift (Γ.pt a) (Γ.pt b)).left ⊤ le_top s = algebraMap R _ ((β a b : Rˣ) : R)) :
    (fun z : T × T => ((β z.1 z.2 : Rˣ) : R)) ∈ prodSpan (Γ.btOrder ⊤) := by
  have := Γ.quasiFinite
  have := Γ.separated
  have := Γ.quasiCompact
  have := Γ.finPres
  let U := GlobalTheory.finitePart Γ.G.hom
  have hU : ∀ x : Γ.G.left, Γ.G.hom x = IsLocalRing.closedPoint R → x ∈ U :=
    GlobalTheory.mem_finitePart_of_eq_closedPoint (R := CommRingCat.of R) Γ.G.hom
  have hF := isFinOpenSub Γ U (GlobalTheory.isFinite_finitePart (R := CommRingCat.of R) Γ.G.hom) hU
  obtain ⟨A, hA, hsec, hprod⟩ := exists_order Γ U hF
  have h1 := pair_ind R T (subH Γ hF) A β hA (hprod s _ fun z => hs z.1 z.2)
  have hle : indOrder (subH Γ hF).subtype A ≤ Γ.btOrder ⊤ := by
    intro f hf
    refine Algebra.subset_adjoin fun t g _ => ?_
    rcases hdim (Γ.G.hom g) with hg | hg
    · exact regularAt_generic Γ _ g hg
    · obtain ⟨σ, hσ⟩ := hsec _ (hf t)
      exact ⟨U, hU g hg, σ, fun h hh => hσ ⟨h, hh⟩ hh⟩
  refine Submodule.span_mono ?_ h1
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact ⟨a, hle ha, b, hle hb, rfl⟩

end PositivityTheory.HtPt.Twpair
