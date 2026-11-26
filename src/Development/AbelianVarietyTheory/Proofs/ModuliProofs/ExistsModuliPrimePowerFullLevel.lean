module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TangentLeDim
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyThetaFamilyOverOpenClosure
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueMapToThetaFamilyOpenPart
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGoodThetaComplexClassUnitaryFullLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGrpPullbackOfIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.ThetaToObj

section Comb
variable {Q L : Type} [AddCommGroup L] {n : ℕ}

theorem add_zero' [Group Q] {f : L → Q} (hf : ∀ x y, f (x + y) = f x * f y) : f 0 = 1 := by
  have := hf 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem add_nsmul' [Group Q] {f : L → Q} (hf : ∀ x y, f (x + y) = f x * f y) (m : ℕ) (x : L) :
    f (m • x) = f x ^ m := by
  induction m with
  | zero => rw [zero_smul, pow_zero, add_zero' hf]
  | succ m ih => rw [succ_nsmul, hf, ih, pow_succ]

theorem ext_basis [CommGroup Q] (bas : (Fin n → ℤ) ≃ₗ[ℤ] L) {f f' : L → Q} (hf : ∀ x y, f (x + y) = f x * f y)
    (hf' : ∀ x y, f' (x + y) = f' x * f' y) (h : ∀ i, f (bas (Pi.single i 1)) = f' (bas (Pi.single i 1))) (x : L) :
    f x = f' x := by
  let F : L →+ Additive Q := AddMonoidHom.mk' (fun x => Additive.ofMul (f x)) fun x y => by rw [hf]; rfl
  let F' : L →+ Additive Q := AddMonoidHom.mk' (fun x => Additive.ofMul (f' x)) fun x y => by rw [hf']; rfl
  have : F.toIntLinearMap ∘ₗ bas.toLinearMap = F'.toIntLinearMap ∘ₗ bas.toLinearMap := by
    refine (Pi.basisFun ℤ (Fin n)).ext fun i => ?_
    rw [Pi.basisFun_apply]
    exact congrArg Additive.ofMul (h i)
  have e := LinearMap.congr_fun this (bas.symm x)
  simpa [F, F'] using e

theorem exists_comb [CommGroup Q] (bas : (Fin n → ℤ) ≃ₗ[ℤ] L) (p : Fin n → Q) (k : ℕ) (hp : ∀ i, p i ^ k = 1) :
    ∃ f : L → Q, (∀ x y, f (x + y) = f x * f y) ∧ (∀ x, f (k • x) = 1) ∧ ∀ i, f (bas (Pi.single i 1)) = p i := by
  have hf : ∀ x y : L, ∏ i, p i ^ bas.symm (x + y) i = (∏ i, p i ^ bas.symm x i) * ∏ i, p i ^ bas.symm y i := by
    intro x y
    simp only [map_add (f := _), Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  refine ⟨fun x => ∏ i, p i ^ bas.symm x i, hf, fun x => ?_, fun i => ?_⟩
  · refine Finset.prod_eq_one fun i _ => ?_
    rw [map_nsmul, Pi.smul_apply, nsmul_eq_mul, zpow_mul, zpow_natCast, hp, one_zpow]
  · beta_reduce
    rw [LinearEquiv.symm_apply_apply, Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp

end Comb

theorem smul_mem_of_mul {O L : Type} [CommRing O] [AddCommGroup L] [Module O L] {I J : Ideal O} {M : ℕ}
    (h : I * J = Ideal.span {(M : O)}) {u : O} (hu : u ∈ I) {x : L} (hx : x ∈ J • (⊤ : Submodule O L)) :
    ∃ y : L, u • x = M • y := by
  have h1 : u • x ∈ (I * J) • (⊤ : Submodule O L) := by
    rw [Submodule.mul_smul]
    exact Submodule.smul_mem_smul hu hx
  rw [h, Submodule.ideal_span_singleton_smul] at h1
  obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h1
  exact ⟨y, by rw [← hy, Nat.cast_smul_eq_nsmul]⟩

theorem isGrpPullback_of_iso {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] (φ : G' ≅ G) [IsMonHom φ.hom] :
    IsGrpPullback G' G (𝟙 S) φ.hom.left := by
  have : IsIso φ.hom.left := inferInstanceAs (IsIso ((Over.forget S).map φ.hom))
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let j : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have e₁ : x₀ = j ≫ x ≫ φ.hom := Over.OverMorphism.ext (by simp [hx, j])
  have e₂ : y₀ = j ≫ y ≫ φ.hom := Over.OverMorphism.ext (by simp [hy, j])
  rw [e₁, e₂, ← MonObj.comp_mul, ← MonObj.mul_comp]
  simp [j]

theorem exists_obj_under : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (l : Level H) (o : Type) [CommRing o] [Algebra o (KA l)] (b : TBase o l.A) (ρ : o) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (t : TObj g l.A J b (s ≫ spMap (algebraMap o (KA l)))) (τ : SAB H S), l.M ∣ l.A → IsSympBasis D bas → IsFractionRing o (KA l) → algebraMap o (KA l) ρ = (baseKA l).ρ → algebraMap o (KA l) (b.ζ : o) = (baseKA l).ζ → (IsReduced S ∨ IsLocallyNoetherian S) → IsPEL D a bas ρ t τ → ∃ ob : Obj D l (baseKA l) s, ObjUnder ob a bas t := by
  intro _ _ E _ _ _ H D g J a bas l o _ _ b ρ S s t τ hMA _ _ hρ hζ _ hP
  obtain ⟨φ, hmon, hL, hact, hgeo⟩ := hP
  obtain ⟨r, hr⟩ := hMA
  have hrpos : 0 < r := Nat.pos_of_ne_zero fun h => by
    have := l.A_pos
    rw [hr, h] at this
    simp at this
  have hMpos : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨hab, hamp, hk⟩ := PolPull.pol_pull_of_relAmple_local AmpleLocal.relAmple_of_locally S S t.A τ.G (𝟙 S)
    φ.hom.left t.L τ.PP.L t.isLB τ.PP.isLB t.ab (isGrpPullback_of_iso φ) hL
  let j : 𝟙_ (Over S) ⟶ Out.baseOver S := Over.homMk (𝟙 S) (by simp)
  obtain ⟨f, fadd, fker, fbas⟩ := exists_comb (Q := 𝟙_ (Over S) ⟶ τ.G) bas (fun i => j ≫ t.pt i ≫ φ.inv) l.A
    fun i => by
      rw [← MonObj.comp_pow, ← MonObj.pow_comp, t.torsion, MonObj.one_comp, MonObj.comp_one]
  obtain ⟨e', he', e, he, hee⟩ := Submodule.mem_sup.1 (show (1 : 𝓞 E) ∈ _ from l.coprime ▸ Submodule.mem_top)
  refine ⟨⟨τ, hab.proper, hamp t.ample, hk t.ktriv, fun x => f (r • e • x), fun x y => ?_, fun x hx => ?_, f, fadd, fker,
    fun K _ _ x β hβ => ?_⟩, φ, hmon, hL, hact, fun i => ?_⟩
  · rw [smul_add, smul_add, fadd]
  · obtain ⟨y, hy⟩ := smul_mem_of_mul ((mul_comm _ _).trans l.prod) he hx
    rw [hy, smul_smul, mul_comm, ← hr, fker]
  · have : CharZero K := RingHom.charZero_iff β.injective |>.1 inferInstance
    obtain ⟨hd, I, hI, hev⟩ := hgeo K x (β.comp (algebraMap o (KA l))) (by
      rw [← Category.assoc, hβ, ← Spec.map_comp]; rfl)
    have hA : ∀ y, toUnit (Over.mk x) ≫ f y = I.ev l.A y := by
      refine ext_basis (Q := Over.mk x ⟶ τ.G) bas (fun y z => ?_) (I.add _) fun i => ?_
      · rw [fadd, MonObj.comp_mul]
      · rw [fbas, ← cancel_mono φ.hom, hev]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rw [← Category.assoc]
        congr 1
    refine ⟨by rw [← hρ]; exact hd, I, by rw [← hζ]; exact hI, hA, fun y hy => ?_⟩
    obtain ⟨z, hz⟩ := smul_mem_of_mul l.prod he' hy
    have h1 : y = e • y + l.M • z := by rw [← hz, ← add_smul, add_comm, hee, one_smul]
    rw [hA, add_nsmul' (I.add _), hr, I.tower _ _ hMpos hrpos]
    conv_rhs => rw [h1, I.add, (I.ker _ hMpos _).2 ⟨z, rfl⟩, _root_.mul_one]
  · show (f _ ≫ φ.hom).left = _
    rw [fbas]
    simp [j]

end GlobalTheory.ThetaToObj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ActOfGenerators
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.UnderMap

theorem sec_ext_of_pow_eq {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] [LocallyOfFiniteType G.hom]
    (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) (u v : 𝟙_ (Over S) ⟶ G) (h : u ^ n = v ^ n)
    (hg : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S),
      toUnit (Over.mk x) ≫ u = toUnit (Over.mk x) ≫ v) : u = v := by
  have hw : (Out.mulA G n).left ≫ G.hom = G.hom := Over.w _
  have h₁ : FormallyUnramified (Out.mulA G n).left := formallyUnramified_mulA S G n hn
  have h₂ : LocallyOfFiniteType ((Out.mulA G n).left ≫ G.hom) := by rw [hw]; infer_instance
  have h₃ : LocallyOfFiniteType (Out.mulA G n).left := locallyOfFiniteType_of_comp _ G.hom
  have e : ∀ w : 𝟙_ (Over S) ⟶ G, w ≫ Out.mulA G n = w ^ n := fun w => by
    rw [Out.mulA, MonObj.comp_pow, Category.comp_id]
  apply Over.OverMorphism.ext
  refine eq_of_range_equalizer_ι_eq_univ (Out.mulA G n).left
    (by rw [← Over.comp_left, ← Over.comp_left, e, e, h]) (Set.eq_univ_of_forall fun p => ?_)
  let k := AlgebraicClosure (S.residueField p)
  let x : Sp k ⟶ S := spMap (algebraMap (S.residueField p) k) ≫ S.fromSpecResidueField p
  have hx : x ≫ u.left = x ≫ v.left := by
    have := congrArg (fun z => z.left) (hg k x)
    simp only [Over.comp_left, ObjPull.toUnit_left'] at this
    exact this
  refine range_subset_range_equalizer_ι (T := S) x hx ⟨(default : PrimeSpectrum k), ?_⟩
  show S.fromSpecResidueField p _ = p
  exact Scheme.fromSpecResidueField_apply p _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem map_zero_of_add {A Q : Type} [AddGroup A] [Group Q] {F : A → Q} (h : ∀ a c, F (a + c) = F a * F c) :
    F 0 = 1 := by
  have := h 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem map_nsmul_of_add {A Q : Type} [AddGroup A] [Group Q] {F : A → Q} (h : ∀ a c, F (a + c) = F a * F c)
    (n : ℕ) (a : A) : F (n • a) = F a ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, map_zero_of_add h]
  | succ n ih => rw [succ_nsmul, h, ih, pow_succ]

def eqSub {A Q : Type} [AddGroup A] [Group Q] {F F' : A → Q} (h : ∀ a c, F (a + c) = F a * F c)
    (h' : ∀ a c, F' (a + c) = F' a * F' c) : AddSubgroup A :=
  AddMonoidHom.eqLocus (AddMonoidHom.mk' (fun a => Additive.ofMul (F a)) fun a c => congrArg Additive.ofMul (h a c))
    (AddMonoidHom.mk' (fun a => Additive.ofMul (F' a)) fun a c => congrArg Additive.ofMul (h' a c))

theorem mem_eqSub {A Q : Type} [AddGroup A] [Group Q] {F F' : A → Q} (h : ∀ a c, F (a + c) = F a * F c)
    (h' : ∀ a c, F' (a + c) = F' a * F' c) (a : A) : a ∈ eqSub h h' ↔ F a = F' a := Iff.rfl

theorem eta_eq_pow {B : Type} [CommRing B] {bB : Base l B} {S : Scheme.{0}} {sB : S ⟶ Sp B} (ob : Obj D l bB sB)
    (hd : l.M ∣ l.A) (a : D.La) (ha : a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)) :
    ob.eta a = ob.etaA a ^ (l.A / l.M) := by
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hq : 0 < l.A / l.M := Nat.div_pos (Nat.le_of_dvd l.A_pos hd) hM
  have hA : l.M * (l.A / l.M) = l.A := Nat.mul_div_cancel' hd
  have hp := ob.proper
  have hn : IsUnit (l.M : Γ(S, ⊤)) := by
    simpa using (bB.unit l.M hM).map (sB.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
  refine sec_ext_of_pow_eq ob.t.G l.M hn _ _ ?_ fun k _ _ x => ?_
  · rw [← pow_mul, mul_comm, hA, ← map_nsmul_of_add ob.etaA_add, ob.etaA_ker, ← map_nsmul_of_add ob.eta_add]
    apply ob.eta_ker
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    refine Submodule.smul_mem_smul ?_ trivial
    have hle : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb := Ideal.mul_le_left
    rw [l.prod] at hle
    exact hle (Ideal.mem_span_singleton_self _)
  · obtain ⟨β, hβ⟩ : ∃ β : B →+* k, x ≫ sB = spMap β := ⟨(Spec.preimage (x ≫ sB)).hom, (Spec.map_preimage _).symm⟩
    obtain ⟨-, I, -, h₁, h₂⟩ := ob.geom k x β hβ
    rw [h₂ a ha, MonObj.comp_pow, h₁ a, ← I.tower l.M (l.A / l.M) hM hq a, hA]

section Pull

variable {B B' : Type} [CommRing B] [CommRing B'] {bB : Base l B} {bB' : Base l B'} {S S' : Scheme.{0}}
  {sB : S ⟶ Sp B} {sB' : S' ⟶ Sp B'} {f : S' ⟶ S}

theorem eq_secPull {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (u' : 𝟙_ (Over S') ⟶ G') (u : 𝟙_ (Over S) ⟶ G) :
    u' = ObjPull.secPull h u ↔ u'.left ≫ φ = f ≫ u.left := by
  refine ⟨fun e => e ▸ ObjPull.secPull_left h u, fun e => ?_⟩
  apply Over.OverMorphism.ext
  apply h.1.hom_ext
  · rw [e, ObjPull.secPull_left]
  · rw [Over.w, Over.w]

theorem levels_of_basis (ob : Obj D l bB sB) (ob' : Obj D l bB' sB') (hd : l.M ∣ l.A) {n : ℕ}
    (bas : (Fin n → ℤ) ≃ₗ[ℤ] D.La) {φ : ob'.t.G.left ⟶ ob.t.G.left} (h : IsGrpPullback ob'.t.G ob.t.G f φ)
    (hb : ∀ i, (ob'.etaA (bas (Pi.single i 1))).left ≫ φ = f ≫ (ob.etaA (bas (Pi.single i 1))).left) :
    (∀ a, (ob'.eta a).left ≫ φ = f ≫ (ob.eta a).left) ∧ ∀ a, (ob'.etaA a).left ≫ φ = f ≫ (ob.etaA a).left := by
  have hA : ∀ a, ob'.etaA a = ObjPull.secPull h (ob.etaA a) := by
    intro a
    have add : ∀ a c, ObjPull.secPull h (ob.etaA (a + c)) =
        ObjPull.secPull h (ob.etaA a) * ObjPull.secPull h (ob.etaA c) := fun a c => by rw [ob.etaA_add, map_mul]
    refine (mem_eqSub (F' := fun a => ObjPull.secPull h (ob.etaA a)) ob'.etaA_add add a).1 ?_
    obtain ⟨c, rfl⟩ := bas.surjective a
    have hc : c = ∑ i, c i • (Pi.single i 1 : Fin n → ℤ) := by
      ext j; simp [Pi.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hc, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_smul]
    refine zsmul_mem ?_ _
    exact (eq_secPull h _ _).2 (hb i)
  refine ⟨fun a => (eq_secPull h _ _).1 ?_, fun a => (eq_secPull h _ _).1 (hA a)⟩
  have ha : a ∈ (l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [l.coprime, Submodule.top_smul]; trivial
  rw [Submodule.sup_smul] at ha
  obtain ⟨a₁, h₁, a₂, h₂, rfl⟩ := Submodule.mem_sup.1 ha
  rw [ob.eta_add, ob'.eta_add, ob.eta_ker _ h₁, ob'.eta_ker _ h₁, _root_.one_mul, _root_.one_mul,
    eta_eq_pow ob hd _ h₂, eta_eq_pow ob' hd _ h₂, map_pow, hA]

theorem act_of_generators {O : Type} [CommRing O] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    (α : OAct O G) (α' : OAct O G') {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {J : Type} (a : J → O)
    (ha : Subring.closure (Set.range a) = ⊤)
    (hj : ∀ j, (α'.act (a j)).left ≫ φ = φ ≫ (α.act (a j)).left) (c : O) :
    (α'.act c).left ≫ φ = φ ≫ (α.act c).left := by
  have add' : ∀ a c, pushHom h G' (α'.act (a + c)) = pushHom h G' (α'.act a) * pushHom h G' (α'.act c) :=
    fun a c => by rw [α'.add, map_mul]
  have add : ∀ a c, pushHom h G' (𝟙 _) ≫ α.act (a + c) =
      (pushHom h G' (𝟙 _) ≫ α.act a) * (pushHom h G' (𝟙 _) ≫ α.act c) :=
    fun a c => by rw [α.add, MonObj.comp_mul]
  have key : ∀ c, c ∈ eqSub (F := fun c => pushHom h G' (α'.act c))
      (F' := fun c => pushHom h G' (𝟙 _) ≫ α.act c) add' add ↔ (α'.act c).left ≫ φ = φ ≫ (α.act c).left := fun c => by
    rw [mem_eqSub]
    have e : (pushHom h G' (𝟙 _) ≫ α.act c).left = φ ≫ (α.act c).left :=
      congrArg (· ≫ (α.act c).left) (Category.id_comp φ)
    exact ⟨fun H => (congrArg (fun z => z.left) H).trans e, fun H => Over.OverMorphism.ext (H.trans e.symm)⟩
  have hc : c ∈ Subring.closure (Set.range a) := by rw [ha]; trivial
  rw [← key]
  induction hc using Subring.closure_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact (key _).2 (hj j)
  | zero => exact zero_mem _
  | one => rw [key, α.one, α'.one]; simp
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx
  | mul x y _ _ hx hy =>
    rw [key] at hx hy ⊢
    rw [α.mul, α'.mul, Over.comp_left, Over.comp_left, Category.assoc, hy, reassoc_of% hx]

end Pull

theorem objMap_iff_tMap : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (l : Level H) (B o : Type) [CommRing B] [CommRing o] (bB : Base l B) (b : TBase o l.A) (S S' : Scheme.{0}) (sB : S ⟶ Sp B) (sB' : S' ⟶ Sp B) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (ob : Obj D l bB sB) (ob' : Obj D l bB sB') (t : TObj g l.A J b s) (t' : TObj g l.A J b s') (f : S' ⟶ S), l.M ∣ l.A → Subring.closure (Set.range a) = ⊤ → ObjUnder ob a bas t → ObjUnder ob' a bas t' → (Nonempty (ObjMap ob' ob f) ↔ TMap t' t f) := by
  intro hL _ E _ _ _ H D g J a bas l B o _ _ bB b S S' sB sB' s s' ob ob' t t' f hd ha
    ⟨e, he, heL, hea, hep⟩ ⟨e', he', heL', hea', hep'⟩
  have ih : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
  have hi : e.hom.left ≫ e.inv.left = 𝟙 _ := by rw [← Over.comp_left, e.hom_inv_id, Over.id_left]
  have ih' : e'.inv.left ≫ e'.hom.left = 𝟙 _ := by rw [← Over.comp_left, e'.inv_hom_id, Over.id_left]
  have hi' : e'.hom.left ≫ e'.inv.left = 𝟙 _ := by rw [← Over.comp_left, e'.hom_inv_id, Over.id_left]
  have m₁ : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have m₂ : IsMonHom e'.symm.hom := inferInstanceAs (IsMonHom e'.inv)
  have a₁ : ∀ j, (ob.t.act.act (a j)).left ≫ e.hom.left = e.hom.left ≫ (t.act j).left := fun j =>
    congrArg (fun z => z.left) (hea j)
  have a₂ : ∀ j, (ob'.t.act.act (a j)).left ≫ e'.hom.left = e'.hom.left ≫ (t'.act j).left := fun j =>
    congrArg (fun z => z.left) (hea' j)
  have p₁ : ∀ i, (ob.etaA (bas (Pi.single i 1))).left ≫ e.hom.left = (t.pt i).left := hep
  have p₂ : ∀ i, (ob'.etaA (bas (Pi.single i 1))).left ≫ e'.hom.left = (t'.pt i).left := hep'
  constructor
  · rintro ⟨m⟩
    have mL : LBIso ob'.t.PP.L (ob.t.PP.L.pull m.cm.F) := by
      obtain ⟨w, hw, -⟩ := m.lin
      exact ⟨w, hw⟩
    refine ⟨e'.inv.left ≫ m.cm.F ≫ e.hom.left, ?_, ?_, fun i => ?_, fun j => ?_⟩
    · exact (IsGrpPullback.comp (isGrpPullback_of_iso e'.symm)
        (IsGrpPullback.comp m.cart (isGrpPullback_of_iso e))).congr (by simp) rfl
    · have k₁ : LBIso (ob'.t.PP.L.pull e'.inv.left) (t'.L.pull (𝟙 _)) := PELPull.lbIso_pull heL' e'.inv.left ih'.symm
      have k₂ : LBIso t'.L (ob'.t.PP.L.pull e'.inv.left) :=
        k₁.symm.chartPull (chartPullUnpull t'.L _ rfl) (chartPullId _)
      have k₃ : LBIso ob'.t.PP.L (t.L.pull (m.cm.F ≫ e.hom.left)) :=
        mL.trans ob'.t.PP.isLB (pull_isLB ob.t.PP.isLB _) (pull_isLB t.isLB _) (PELPull.lbIso_pull heL m.cm.F rfl)
      exact k₂.trans t'.isLB (pull_isLB ob'.t.PP.isLB _) (pull_isLB t.isLB _) (PELPull.lbIso_pull k₃ e'.inv.left rfl)
    · have := m.etaA (bas (Pi.single i 1))
      rw [← p₂, ← p₁, Category.assoc, reassoc_of% hi']
      exact (reassoc_of% this) _
    · have h₂ : (t'.act j).left ≫ e'.inv.left = e'.inv.left ≫ (ob'.t.act.act (a j)).left := by
        rw [← Category.id_comp (t'.act j).left, ← ih', Category.assoc, Category.assoc, ← reassoc_of% a₂ j, hi',
          Category.comp_id]
      have h₃ := m.act (a j)
      rw [reassoc_of% h₂, reassoc_of% h₃, a₁, Category.assoc, Category.assoc]
  · rintro ⟨ψ, hψ, hψL, hpt, hact⟩
    have hc : IsGrpPullback ob'.t.G ob.t.G f (e'.hom.left ≫ ψ ≫ e.inv.left) :=
      (IsGrpPullback.comp (isGrpPullback_of_iso e')
        (IsGrpPullback.comp hψ (isGrpPullback_of_iso e.symm))).congr (by simp) rfl
    have kL : LBIso ob'.t.PP.L (ob.t.PP.L.pull (e'.hom.left ≫ ψ ≫ e.inv.left)) := by
      have k₁ : LBIso ob'.t.PP.L (t.L.pull (e'.hom.left ≫ ψ)) :=
        heL'.trans ob'.t.PP.isLB (pull_isLB t'.isLB _) (pull_isLB t.isLB _) (PELPull.lbIso_pull hψL e'.hom.left rfl)
      refine k₁.trans ob'.t.PP.isLB (pull_isLB t.isLB _) (pull_isLB ob.t.PP.isLB _)
        (PELPull.lbIso_pull heL _ ?_).symm
      rw [Category.assoc, Category.assoc, ih, Category.comp_id]
    obtain ⟨m, hm⟩ := GlobalTheory.exists_sabMap_of_isProper_of_lbIso hL.globalFns E H S S' ob.t ob'.t f _ ob.proper hc kL
      (act_of_generators ob.t.act ob'.t.act hc a ha fun j => by
        have h₂ : (t.act j).left ≫ e.inv.left = e.inv.left ≫ (ob.t.act.act (a j)).left := by
          rw [← Category.id_comp (t.act j).left, ← ih, Category.assoc, Category.assoc, ← reassoc_of% a₁ j, hi,
            Category.comp_id]
        rw [reassoc_of% a₂ j, reassoc_of% hact j, h₂, Category.assoc, Category.assoc])
    obtain ⟨q₁, q₂⟩ := levels_of_basis ob ob' hd bas hc fun i => by
      have := hpt i
      rw [reassoc_of% p₂ i]
      refine ((reassoc_of% this) _).trans ?_
      rw [← p₁]
      exact congrArg (f ≫ ·) (by rw [Category.assoc, hi, Category.comp_id])
    rw [← hm] at q₁ q₂
    exact ⟨⟨m, q₁, q₂⟩⟩

end GlobalTheory.UnderMap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfDimOfDirectionsLe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SmoothDirections

noncomputable def derivationPoint {k R K : Type} [CommRing k] [CommRing R] [Field K]
    [Algebra k R] [Algebra k K] [Algebra R K] [IsScalarTower k R K] {r : ℕ}
    (D : Fin r → Derivation k R K) : R →+* TrivSqZeroExt K (Fin r → K) where
  toFun a := TrivSqZeroExt.inl (algebraMap R K a) + TrivSqZeroExt.inr fun i ↦ D i a
  map_one' := by
    refine TrivSqZeroExt.ext (by simp) ?_
    funext i
    simp
  map_mul' a b := by
    refine TrivSqZeroExt.ext (by simp) ?_
    funext i
    simp [Algebra.smul_def, mul_comm]
  map_zero' := by
    refine TrivSqZeroExt.ext (by simp) ?_
    funext i
    simp
  map_add' a b := by
    refine TrivSqZeroExt.ext (by simp) ?_
    funext i
    simp

theorem finrank_derivation_le {k R K : Type} [Field k] [CommRing R] [Field K]
    [Algebra k R] [Algebra k K] [Algebra R K] [IsScalarTower k R K] {X : Scheme.{0}}
    (s : X ⟶ Sp k) (j : Sp R ⟶ X) [Mono j] (hj : j ≫ s = spMap (algebraMap k R)) {d : ℕ}
    (ht : ∀ (r : ℕ) (β : k →+* K) (x : Sp (TrivSqZeroExt K (Fin r → K)) ⟶ X),
      x ≫ s = spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) →
      (∀ lam : (Fin r → K) →ₗ[K] K,
        spMap (dirMap lam) ≫ x = constPt (spMap (dirMap lam) ≫ x) → lam = 0) → r ≤ d) :
    Module.finrank K (Derivation k R K) ≤ d := by
  obtain ⟨D, hD⟩ := exists_linearIndependent_of_le_finrank
    (le_refl (Module.finrank K (Derivation k R K)))
  refine ht _ (algebraMap k K) (spMap (derivationPoint D) ≫ j) ?_ ?_
  · rw [Category.assoc, hj, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun a ↦ TrivSqZeroExt.ext ?_ ?_
    · simp [derivationPoint, ← IsScalarTower.algebraMap_apply, TrivSqZeroExt.algebraMap_eq_inl]
    · funext i
      simp [derivationPoint, TrivSqZeroExt.algebraMap_eq_inl]
  · intro lam h
    simp only [constPt, ← Category.assoc, cancel_mono] at h
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp] at h
    have h₁ := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
    have h₂ (a : R) : lam (fun i ↦ D i a) = 0 := by
      have := congrArg TrivSqZeroExt.snd (RingHom.congr_fun h₁ a)
      simpa [dirMap, derivationPoint, TrivSqZeroExt.algebraMap_eq_inl] using this
    have h₃ := Fintype.linearIndependent_iff.mp hD (fun i ↦ lam (Pi.single i 1)) (by
      ext a
      have := h₂ a
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Finset.univ_sum_single (fun i ↦ D i a), map_sum] at this
      rw [Derivation.zero_apply, ← this]
      refine (congrFun (map_sum (Derivation.coeFnAddMonoidHom (R := k) (A := R) (M := K)) _ _) a).trans ?_
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      change lam (Pi.single i 1) • D i a = _
      rw [smul_eq_mul, mul_comm, ← smul_eq_mul, ← map_smul, ← Pi.single_smul, smul_eq_mul,
        _root_.mul_one])
    refine (Pi.basisFun K _).ext fun i ↦ ?_
    simpa using h₃ i

theorem smoothOfRelativeDimension_of_forall_finrank_derivation_le (k : Type) [Field k]
    [PerfectField k] (R : Type) [CommRing R] [Algebra k R] [Algebra.FiniteType k R] (d : ℕ)
    (hd : ∀ q ∈ minimalPrimes R, (d : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q))
    (ht : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra k K] [Algebra R K] [IsScalarTower k R K],
      Module.finrank K (Derivation k R K) ≤ d) :
    SmoothOfRelativeDimension d (spMap (algebraMap k R)) := by
  have : Algebra.FinitePresentation k R := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have key (m : Ideal R) (hm : m.IsMaximal) :
      ∃ f ∉ m, Algebra.IsStandardSmoothOfRelativeDimension d k (Localization.Away f) := by
    have h₁ : (d : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime m) := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)]
      exact_mod_cast SmoothTangent.le_height_of_forall_minimalPrimes k hd m
    have h₂ : Module.finrank (R ⧸ m) m.Cotangent ≤ d := by
      let := Ideal.Quotient.field m
      exact (SmoothTangent.finrank_cotangent_le_finrank_derivation k m
        (AlgebraicClosure (R ⧸ m))).trans (ht _)
    obtain ⟨-, -, -, h₃, -, h₄⟩ := isSmoothAt_of_finrank_cotangent_le_of_perfectField k m h₁ h₂
    exact exists_isStandardSmoothOfRelativeDimension_of_isSmoothAt k m h₄
  refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)).mpr ?_
  refine ⟨{f | Algebra.IsStandardSmoothOfRelativeDimension d k (Localization.Away f)}, ?_, ?_⟩
  · by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨f, hf, hs⟩ := key m hm
    exact hf (hle (Ideal.subset_span hs))
  · intro f hf
    have := (RingHom.isStandardSmoothOfRelativeDimension_algebraMap d).mpr hf
    rwa [IsScalarTower.algebraMap_eq k R] at this

end GlobalTheory.SmoothDirections

namespace GlobalTheory

open SmoothDirections

theorem smoothOfRelativeDimension_of_dim_of_directions_le :
    ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) (s : X ⟶ Sp k) (d : ℕ),
      LocallyOfFiniteType s →
      (∀ (R : Type) [CommRing R] [Algebra k R] (x : Sp R ⟶ X), IsOpenImmersion x →
        x ≫ s = spMap (algebraMap k R) →
        ∀ q ∈ minimalPrimes R, (d : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q)) →
      (∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (β : k →+* K)
        (x : Sp (TrivSqZeroExt K (Fin r → K)) ⟶ X),
        x ≫ s = spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) →
        (∀ lam : (Fin r → K) →ₗ[K] K,
          spMap (dirMap lam) ≫ x = constPt (spMap (dirMap lam) ≫ x) → lam = 0) → r ≤ d) →
      SmoothOfRelativeDimension d s := by
  intro k _ _ X s d _ hd ht
  choose A iA aA j hj q hq hjs using exists_affine_chart_over s
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension d)
  refine IsZariskiLocalAtSource.of_openCover
    (Scheme.Cover.mkOfCovers X (fun x ↦ Sp (A x)) j (fun x ↦ ⟨x, q x, hq x⟩) hj)
    fun (x : X) ↦ ?_
  change SmoothOfRelativeDimension d (j x ≫ s)
  let := iA x
  let := aA x
  have := hj x
  have : Algebra.FiniteType k (A x) := RingHom.finiteType_algebraMap.mp <|
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
      (φ := CommRingCat.ofHom (algebraMap k (A x)))).mp (hjs x ▸ inferInstance)
  rw [hjs]
  exact smoothOfRelativeDimension_of_forall_finrank_derivation_le k (A x) d
    (hd _ (j x) (hj x) (hjs x)) fun K _ _ _ _ _ ↦ finrank_derivation_le s (j x) (hjs x) (ht K)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPrimitiveRootMapOfNatCastNeZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.IntegersAway

theorem isPrimitiveRoot_map_of_natCast_ne_zero {R K : Type} [CommRing R] [IsDomain R] [CharZero R] [Field K] {k : ℕ}
    (hk : 0 < k) {z : R} (hz : IsPrimitiveRoot z k) (β : R →+* K) (hβ : (k : K) ≠ 0) : IsPrimitiveRoot (β z) k := by
  have : NeZero (k : K) := ⟨hβ⟩
  have h : (Polynomial.cyclotomic k R).IsRoot z := hz.isRoot_cyclotomic hk
  apply (Polynomial.isRoot_cyclotomic_iff (n := k) (R := K)).mp
  rw [← Polynomial.map_cyclotomic k β]
  exact h.map β

theorem exists_tBase_of_numberField {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ) {k : ℕ} (hk : 0 < k)
    {z r : F} (hz : IsPrimitiveRoot z k) (hr : IsIntegral ℤ r) :
    ∃ (o : Type) (_ : CommRing o) (b : TBase o k) (em : o →+* ℂ) (ρ : o) (_ : Algebra o F), ArBase em ∧
      IsFractionRing o F ∧ (∀ x, φ (algebraMap o F x) = em x) ∧ algebraMap o F ρ = r ∧
      algebraMap o F (b.ζ : o) = z := by
  obtain ⟨em, hem, hcomp⟩ := exists_arBase_away φ hk.ne'
  have hn' : (k : 𝓞 F) ≠ 0 := by exact_mod_cast hk.ne'
  have hM : Submonoid.powers (k : 𝓞 F) ≤ nonZeroDivisors (𝓞 F) := powers_le_nonZeroDivisors_of_noZeroDivisors hn'
  let o := Localization.Away (k : 𝓞 F)
  have hu : IsUnit (algebraMap (𝓞 F) F (k : 𝓞 F)) := by simpa using hk.ne'
  let j : o →+* F := IsLocalization.Away.lift (k : 𝓞 F) hu
  have hj : ∀ x, j (algebraMap (𝓞 F) o x) = algebraMap (𝓞 F) F x := IsLocalization.Away.lift_eq _ hu
  let alg : Algebra o F := j.toAlgebra
  have : IsScalarTower (𝓞 F) o F := IsScalarTower.of_algebraMap_eq fun x => (hj x).symm
  let z₀ : 𝓞 F := ⟨z, hz.isIntegral hk⟩
  have hz₀ : IsPrimitiveRoot z₀ k :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 F) F) hz RingOfIntegers.coe_injective
  have hko : IsUnit (k : o) := by
    simpa using IsLocalization.Away.algebraMap_isUnit (S := o) (k : 𝓞 F)
  have hzu : IsUnit (algebraMap (𝓞 F) o z₀) := (hz₀.isUnit hk.ne').map _
  refine ⟨o, inferInstance, ⟨hzu.unit, hko, fun K _ β => ?_⟩, em, algebraMap (𝓞 F) o ⟨r, hr⟩, alg, hem,
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers (k : 𝓞 F)) o F, ?_, hj _, hj _⟩
  · refine isPrimitiveRoot_map_of_natCast_ne_zero hk hz₀ (β.comp (algebraMap (𝓞 F) o)) ?_
    simpa using (hko.map β).ne_zero
  · have : φ.comp j = em := by
      refine IsLocalization.ringHom_ext (Submonoid.powers (k : 𝓞 F)) ?_
      rw [hcomp]
      ext x
      simp [hj]
    exact fun x => DFunLike.congr_fun this x

theorem exists_tBase_fractionRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H), ∃ (o : Type) (_ : CommRing o) (b : TBase o l.A) (em : o →+* ℂ) (ρ : o) (_ : Algebra o (KA l)), ArBase em ∧ IsFractionRing o (KA l) ∧ (∀ x, ((algebraMap o (KA l) x : KA l) : ℂ) = em x) ∧ algebraMap o (KA l) ρ = (baseKA l).ρ ∧ algebraMap o (KA l) (b.ζ : o) = (baseKA l).ζ := by
  intro E _ _ _ H l
  have : FiniteDimensional ℚ (KA l) := by
    refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
    rcases hx with rfl | rfl
    · refine IsIntegral.of_pow two_pos ?_
      rw [H.sqrt_neg_disc_sq]
      exact (isIntegral_algebraMap (x := (H.d : ℚ))).neg
    · refine IsIntegral.of_pow l.A_pos ?_
      rw [show zeta l.A ^ l.A = 1 from (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]
      exact isIntegral_one
  have : NumberField (KA l) := {}
  have hr : IsIntegral ℤ (baseKA l).ρ := by
    refine IsIntegral.of_pow two_pos ?_
    rw [(baseKA l).ρ_sq]
    simpa using (isIntegral_algebraMap (R := ℤ) (A := KA l) (x := (H.d : ℤ))).neg
  exact exists_tBase_of_numberField (KA l).val.toRingHom l.A_pos (baseKA l).ζ_prim hr

end GlobalTheory.ZM.IntegersAway
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliPrimePowerFullLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.FullLevel

theorem finiteDimensional_KA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    FiniteDimensional ℚ (KA l) := by
  have hA := l.A_pos
  refine IntermediateField.finiteDimensional_adjoin ?_
  intro x hx
  rcases hx with rfl | hx
  · have h2 : H.rt0 ^ 2 = algebraMap ℚ ℂ (-(H.d : ℚ)) := by
      rw [H.sqrt_neg_disc_sq]; simp
    have hi : IsIntegral ℚ (H.rt0 ^ 2) := by rw [h2]; exact isIntegral_algebraMap
    exact IsIntegral.of_pow two_pos hi
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    have hz : IsPrimitiveRoot (zeta l.A) l.A := by
      unfold zeta; exact Complex.isPrimitiveRoot_exp l.A hA.ne'
    refine IsIntegral.of_pow hA ?_
    rw [hz.pow_eq_one]; exact isIntegral_one

private theorem constPt_comp' {k : Type} [Field k] {X Y : Scheme.{0}} (x : Sp (DualNumber k) ⟶ X)
    (f : X ⟶ Y) : constPt (x ≫ f) = constPt x ≫ f := by
  simp only [constPt, Category.assoc]

theorem moduli_of_family (hL : Out.Laws) (hL2 : Out.Laws2)
    (hth : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {g : ℕ} {J : Type} (a : J → 𝓞 E)
    (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (hbas : IsSympBasis D bas) (hw : a w = H.w0)
    (hw' : a w' = H.bar H.w0) (hgen : Subring.closure (Set.range a) = ⊤) (l : Level H) (hMA : l.M ∣ l.A)
    {o : Type} [CommRing o] [IsDomain o] [Algebra o (KA l)] [hfr : IsFractionRing o (KA l)] (b : TBase o l.A) (ρ : o)
    (hρ : algebraMap o (KA l) ρ = (baseKA l).ρ) (hζ : algebraMap o (KA l) (b.ζ : o) = (baseKA l).ζ)
    {U : Scheme.{0}} (sU : U ⟶ Sp o) (tU : TObj g l.A J b sU) (τU : SAB H U) (hq : IsQProjOver sU)
    (hτ : IsPEL D a bas ρ tU τU)
    (hdim : ∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ U), IsOpenImmersion x →
      x ≫ sU = spMap (algebraMap o R) → ∀ q ∈ minimalPrimes (FractionRing o ⊗[o] R),
        (D.dim : WithBot ℕ∞) ≤ ringKrullDim ((FractionRing o ⊗[o] R) ⧸ q))
    (hinj : ∀ (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ U) (s' : Sp R ⟶ Sp o) (t : TObj g l.A J b s'),
      x ≫ sU = y ≫ sU → TMap t tU x → TMap t tU y → x = y)
    (hrep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (t : TObj g l.A J b s') (τ : SAB H S), IsReduced S →
      IsPEL D a bas ρ t τ → (∀ (K : Type) [Field K], (Sp K ⟶ S) → CharZero K) →
      ∃! f : S ⟶ U, f ≫ sU = s' ∧ TMap t tU f) :
    Nonempty (Moduli D l) := by
  classical
  obtain ⟨X, p, sX, sq⟩ : ∃ (X : Scheme.{0}) (p : X ⟶ U) (sX : X ⟶ Sp (KA l)),
      IsPullback p sX sU (spMap (algebraMap o (KA l))) := ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  have hqX : IsQProjOver sX := isQProjOver_of_isPullback_spMap _ sq hq
  have hlft : LocallyOfFiniteType sX := lft_of_qproj hqX
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : FiniteDimensional ℚ (KA l) := finiteDimensional_KA l
  haveI : Algebra.IsAlgebraic ℚ (KA l) := Algebra.IsAlgebraic.of_finite ℚ (KA l)
  obtain ⟨tX, htX⟩ := tObj_pull o g l.A J b U X sU (sX ≫ spMap (algebraMap o (KA l))) p tU sq.w
  obtain ⟨τX, hτX⟩ := exists_isPEL_of_tmap E H D g J a bas l.A o b ρ U X sU
    (sX ≫ spMap (algebraMap o (KA l))) tU tX τU p sq.w htX hτ
  obtain ⟨ob, hob⟩ := ThetaToObj.exists_obj_under hL hL2 E H D g J a bas l o b ρ X sX tX τX hMA hbas hfr hρ hζ
    (Or.inr inferInstance) hτX
  have hsep : ∀ (R : Type) [CommRing R] [IsLocalRing R] (x1 x2 : Sp R ⟶ X) (s' : Sp R ⟶ Sp o)
      (t' : TObj g l.A J b s'), TMap t' tX x1 → TMap t' tX x2 → x1 ≫ sX = x2 ≫ sX → x1 = x2 := by
    intro R _ _ x1 x2 s' t' h1 h2 hs
    refine sq.hom_ext ?_ hs
    refine hinj R _ _ s' t' ?_ (TMap.comp h1 htX) (TMap.comp h2 htX)
    rw [Category.assoc, Category.assoc, sq.w, ← Category.assoc, hs, Category.assoc]
  refine ⟨{ X := X, s := sX, qproj := hqX, smooth := ?_, univ := ob, rep := ?_, unram := ?_ }⟩
  · refine smoothOfRelativeDimension_of_dim_of_directions_le (KA l) X sX D.dim hlft ?_ ?_
    · intro R _ _ x hx _ q hq'
      haveI : IsOpenImmersion (x ≫ sq.isoPullback.hom) := inferInstance
      exact dim_generic_chart sU _ hdim R (x ≫ sq.isoPullback.hom) q hq'
    · intro K' _ _ r β x hxs hdir
      have hρsq : ρ ^ 2 = -(H.d : o) := by
        apply IsFractionRing.injective o (KA l)
        rw [map_pow, hρ, (baseKA l).ρ_sq]; simp
      have hb : x ≫ sX ≫ spMap (algebraMap o (KA l)) =
          spMap ((algebraMap K' (TrivSqZeroExt K' (Fin r → K'))).comp (β.comp (algebraMap o (KA l)))) := by
        rw [← Category.assoc, hxs, ← spMap_comp]
      obtain ⟨t1, ht1⟩ := tObj_pull o g l.A J b X _ (sX ≫ spMap (algebraMap o (KA l))) _ x tX hb
      obtain ⟨τ1, hτ1⟩ := exists_isPEL_of_tmap E H D g J a bas l.A o b ρ X _
        (sX ≫ spMap (algebraMap o (KA l))) _ tX t1 τX x hb ht1 hτX
      haveI : CharZero K' := charZero_of_hom (spMap β)
      refine T.tangent_le_dim_alt hL hL2 hth E H D g J a w w' bas l.A o b ρ K' r (β.comp (algebraMap o (KA l))) t1 τ1
        hw hw' hρsq hτ1 ?_
      intro lam t' h1 h2
      apply hdir lam
      rw [constPt_comp']
      refine hsep (DualNumber K') _ _ _ t' (TMap.comp h1 ht1) (TMap.comp h2 ht1) ?_
      simpa only [constPt_comp'] using eq_constPt ((spMap (dirMap lam) ≫ x) ≫ sX)
  · intro S s' hS o'
    obtain ⟨t', ht'u, ht'p⟩ := ObjTheta.exists_tObj hL hL2 E H D g J a bas l (KA l) o (baseKA l) b ρ
      (algebraMap o (KA l)) S s' o' hbas hρ hζ
    have hch : ∀ (K : Type) [Field K], (Sp K ⟶ S) → CharZero K := fun K _ y => charZero_of_hom (y ≫ s')
    obtain ⟨f, ⟨hf1, hf2⟩, hfu⟩ := hrep S (s' ≫ spMap (algebraMap o (KA l))) t' o'.t hS ht'p hch
    have hiff := fun (f' : S ⟶ X) => UnderMap.objMap_iff_tMap hL hL2 E H D g J a bas l (KA l) o (baseKA l) b X S
      sX s' (sX ≫ spMap (algebraMap o (KA l))) (s' ≫ spMap (algebraMap o (KA l))) ob o' tX t' f' hMA hgen hob ht'u
    refine ⟨sq.lift f s' hf1, ⟨sq.lift_snd _ _ _, (hiff _).mpr (TMap.cancel htX (by rw [sq.lift_fst]; exact hf2))⟩, ?_⟩
    rintro f2 ⟨hf2s, hm⟩
    have htm : TMap t' tX f2 := (hiff f2).mp hm
    apply sq.hom_ext
    · rw [sq.lift_fst]
      apply hfu
      refine ⟨?_, TMap.comp htm htX⟩
      rw [Category.assoc, sq.w, ← Category.assoc, hf2s]
    · rw [sq.lift_snd, hf2s]
  · intro k _ x o' hm1 hm2
    obtain ⟨t', ht'u, -⟩ := ObjTheta.exists_tObj hL hL2 E H D g J a bas l (KA l) o (baseKA l) b ρ
      (algebraMap o (KA l)) _ (x ≫ sX) o' hbas hρ hζ
    have hiff := fun (f' : Sp (DualNumber k) ⟶ X) => UnderMap.objMap_iff_tMap hL hL2 E H D g J a bas l (KA l) o
      (baseKA l) b X _ sX (x ≫ sX) (sX ≫ spMap (algebraMap o (KA l))) ((x ≫ sX) ≫ spMap (algebraMap o (KA l)))
      ob o' tX t' f' hMA hgen hob ht'u
    refine hsep (DualNumber k) x (constPt x) _ t' ((hiff x).mp hm1) ((hiff _).mp hm2) ?_
    simpa only [constPt_comp'] using eq_constPt (x ≫ sX)

theorem exists_generating_family {E : Type} [Field E] [NumberField E] (u u' : 𝓞 E) :
    ∃ (J : Type) (_ : Finite J) (a : J → 𝓞 E) (w w' : J), a w = u ∧ a w' = u' ∧ Subring.closure (Set.range a) = ⊤ := by
  classical
  let bs := NumberField.RingOfIntegers.basis E
  refine ⟨Option (Option (Module.Free.ChooseBasisIndex ℤ (𝓞 E))), inferInstance,
    fun i => Option.elim i u (fun i' => Option.elim i' u' (fun k => bs k)), none, some none, rfl, rfl, ?_⟩
  rw [eq_top_iff]
  intro x hx0
  clear hx0
  have hx : x ∈ Submodule.span ℤ (Set.range bs) := by rw [bs.span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    exact Subring.subset_closure ⟨some (some k), rfl⟩
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul n y _ hy => exact zsmul_mem hy n

end GlobalTheory.ZM.FullLevel


open GlobalTheory.ZM.FullLevel in
theorem GlobalTheory.ZM.exists_moduli_prime_power_level : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n : ℕ), 1 ≤ D.p + D.q → n.Prime → Odd n → ∃ j : ℕ, ∀ l : Level H, l.M = n → l.A = (n ^ j) ^ 2 → Nonempty (Moduli D l) := by
  intro hL hL2 hth hU E _ _ _ H D n hpq hn hodd
  obtain ⟨bas, hbas⟩ := ZM.exists_isSympBasis E H D
  obtain ⟨J, hJ, a, w, w', hw, hw', hgen⟩ := exists_generating_family (E := E) H.w0 (H.bar H.w0)
  obtain ⟨Mat, κ, hGood⟩ := T.isGoodThetaComplexClass_unitaryFullLevel hL hL2 hth hU E H D _ J a w w' bas hpq hbas hw hw' hgen
  obtain ⟨j₁, hj₁⟩ := hGood n hn hodd
  obtain ⟨j₂, hj₂⟩ := T.nonempty_thetaFamily_over_open_closure hL hL2 _ J Mat κ n w w' hn hodd
  obtain ⟨j₃, hj₃⟩ := T.existsUnique_map_to_thetaFamily_openPart hL hL2 _ J Mat κ n w w' hn hodd
  refine ⟨max (max j₁ j₂) (max j₃ 1), ?_⟩
  intro l hM hA
  have hj1 : j₁ ≤ max (max j₁ j₂) (max j₃ 1) := le_max_of_le_left (le_max_left _ _)
  have hj2 : j₂ ≤ max (max j₁ j₂) (max j₃ 1) := le_max_of_le_left (le_max_right _ _)
  have hj3 : j₃ ≤ max (max j₁ j₂) (max j₃ 1) := le_max_of_le_right (le_max_left _ _)
  have hj0 : 1 ≤ max (max j₁ j₂) (max j₃ 1) := le_max_of_le_right (le_max_right _ _)
  generalize max (max j₁ j₂) (max j₃ 1) = j at hj1 hj2 hj3 hj0 hA
  obtain ⟨o, _, b, em, ρ, _, har, hfr, hem, hρ, hζ⟩ := IntegersAway.exists_tBase_fractionRing E H l
  cases l
  dsimp only at hA hM
  subst hA
  have hM' := hM.symm
  subst hM'
  haveI := har.1
  have hemρ : em ρ = H.rt0 := by rw [← hem, hρ]; rfl
  have h3n : 3 ≤ n := by
    have h2 := hn.two_le
    have hne : n ≠ 2 := by
      rintro rfl
      exact (Nat.not_odd_iff_even.mpr even_two) hodd
    omega
  have hN3 : 3 ≤ n ^ j := le_trans h3n (Nat.le_self_pow (by omega) n)
  have hoddN : Odd (n ^ j) := hodd.pow
  have hGd := hj₁ j hj1 (n ^ j) rfl o b em ρ hemρ
  obtain ⟨F⟩ := hj₂ j hj2 o b em _ D.dim har hGd
  obtain ⟨hqU, -, hredU, hinjU⟩ := T.thetaClosureOpenFamily_qproj_flat_reduced_ext hL hL2 o _ n (n ^ j) J b em _ Mat κ F hoddN
  have hqU' : IsQProjOver (F.U.ι ≫ F.Y.s) := hqU.resolve_right (not_not.mpr inferInstance)
  haveI := hredU
  haveI := lft_of_qproj hqU'
  haveI : IsLocallyNoetherian F.U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (F.U.ι ≫ F.Y.s)
  obtain ⟨τU, hτU⟩ := T.exists_isPELTriple_of_dense_fibres hL hL2 hth E H D _ J a bas w w' hpq hbas hw hw' hgen _ o b em ρ F.U.toScheme
    (F.U.ι ≫ F.Y.s) F.univ hemρ har.2.2 F.dense
  refine moduli_of_family hL hL2 hth D a w w' bas hbas hw hw' hgen _
    (dvd_pow (dvd_pow_self n (by omega)) two_ne_zero) b ρ hρ hζ (F.U.ι ≫ F.Y.s) F.univ τU hqU' hτU
    (T.le_ringKrullDim_thetaFamily_genericFibre hL hL2 _ n (n ^ j) J Mat κ w w' o b em _ D.dim F hN3 hoddN har hGd) hinjU ?_
  intro S s' t τ hS hP hch
  refine hj₃ j hj3 o b em _ D.dim har hGd F S s' t hS ?_ ?_
  · refine Dense.mono ?_ dense_univ
    intro p _
    haveI := hch _ (S.fromSpecResidueField p)
    exact ⟨_, inferInstance, S.fromSpecResidueField p,
      ⟨IsLocalRing.closedPoint _, Scheme.fromSpecResidueField_apply p _⟩,
      T.pelObject_fibre_from_complex_charZero hL hL2 E H D _ J a w w' bas hpq hbas hw hw' hgen (n ^ j) o b em ρ hemρ har S s' t τ hP _ _⟩
  · intro K _ _ x t' hT
    haveI := hch K x
    obtain ⟨K₀, _, β, i, e, t₀, tx, tc, -, -, htx, htx0, htc0, hC⟩ :=
      T.pelObject_fibre_from_complex_charZero hL hL2 E H D _ J a w w' bas hpq hbas hw hw' hgen (n ^ j) o b em ρ hemρ har S s' t τ hP K x
    have s1 := (hGd.shape tc hC).1
    have s2 := ((shape_prim_pull_and_descend o _ _ J b Mat κ w w' _ _ _ _ _ t₀ tc htc0).2.2 K₀ rfl
      inferInstance inferInstance).1 s1
    have s3 := (shape_prim_pull_and_descend o _ _ J b Mat κ w w' _ _ _ _ _ t₀ tx htx0).1 s2
    have htt : TMap t' tx (𝟙 _) := TMap.cancel htx (by rw [Category.id_comp]; exact hT)
    exact (shape_prim_pull_and_descend o _ _ J b Mat κ w w' _ _ _ _ _ tx t' htt).1 s3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliPrimePowerFullLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_moduli_prime_power_fullLevel : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n : ℕ), 1 ≤ D.p + D.q → n.Prime → Odd n → ∃ j : ℕ, ∀ l : Level H, l.M = n → l.A = (n ^ j) ^ 2 → Nonempty (Moduli D l) := by
  first | exact @GlobalTheory.ZM.exists_moduli_prime_power_level | exact GlobalTheory.ZM.exists_moduli_prime_power_level | (intros; apply GlobalTheory.ZM.exists_moduli_prime_power_level <;> assumption)
end
