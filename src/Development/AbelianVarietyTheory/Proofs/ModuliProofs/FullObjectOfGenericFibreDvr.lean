module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullObjectOfGenericFibreDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullObjectOfGenericFibreDvr
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.FullSpread

section Pairing

variable {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) {T : Over S}

theorem weilIs_pow_left (hW : Out.WeilSt) {n : ℕ} {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs P.A P.L n x y c) (m : ℕ) : Out.WeilIs P.A P.L n (x ^ (m + 1)) y (c ^ (m + 1)) := by
  induction m with
  | zero => rwa [zero_add, pow_one, pow_one]
  | succ m ih =>
    rw [pow_succ x, pow_succ c]
    exact (hW S P n T).2.1 _ _ _ _ _ ih h

theorem weilIs_lower (hW : Out.WeilSt) {n m : ℕ} (hm : 0 < m) (hu : IsUnit ((n * m : ℕ) : Γ(T.left, ⊤)))
    {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ} (hx : x ^ (n * m) = 1) (hy : y ^ (n * m) = 1)
    (h : Out.WeilIs P.A P.L ((n * m : ℕ) : ℤ) x y c) : Out.WeilIs P.A P.L n (x ^ m) (y ^ m) (c ^ m) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have h₁ := CommPairing.weilIs_symm P.isLB (weilIs_pow_left P hW (CommPairing.weilIs_symm P.isLB h) m)
  rw [inv_pow, inv_inv, Nat.cast_mul] at h₁
  exact ((hW S P n T).2.2.2 _ x _ _ hu hx (by rw [← pow_mul, mul_comm, hy])).1 h₁

theorem eq_one_of_weilIs_one {K : Type} [Field K] (hW : Out.WeilSt) {x : Sp K ⟶ S} {n : ℕ}
    {y : Over.mk x ⟶ P.A} {c : Kˣ} (h : Out.WeilIs P.A P.L n 1 y (unitOn c)) : c = 1 := by
  have h₁ := (hW S P n _).2.1 _ _ _ _ _ h h
  rw [_root_.mul_one] at h₁
  have e : unitOn (c * c) = unitOn c * unitOn c := map_mul _ _ _
  exact mul_eq_left.1 (weilIs_unique_fieldPoint S P.A P.L P.isLB K x n 1 y _ _ (e ▸ h₁) h)

end Pairing

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {n N : ℕ}

theorem rt_sq (H : Host E) (n N : ℕ) : RZ.rt H n N ^ 2 = -(H.d : RZ H n N) := by
  apply Subtype.ext
  have e : ((RZ.rt H n N : RZ H n N) : ℂ) = H.rt0 := by
    change 2 * ((1 + H.rt0) / 2) - 1 = H.rt0
    ring
  simp [e, H.sqrt_neg_disc_sq]

def GeomAt (D : Datum H) {S : Scheme.{0}} (t : SAB H S) (lev : D.La → (𝟙_ (Over S) ⟶ t.G)) {k : Type} [Field k]
    (x : Sp k ⟶ S) (β : RZ H n N →+* k) : Prop :=
  DetCond D t.act x (β (RZ.rt H n N)) ∧
    ∃ I : TateIso D k (Over.mk x ⟶ t.G) (fun a g => g ≫ t.act.act a)
        (fun m g g' c => Out.WeilIs t.G t.PP.L m g g' (unitOn c)),
      (I.ζ N : k) = β (RZ.ze H n N) ∧ ∀ a, toUnit _ ≫ lev a = I.ev N a

theorem GeomAt.push {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (ν : SABMap t' t f)
    {lev : D.La → (𝟙_ (Over S) ⟶ t.G)} {lev' : D.La → (𝟙_ (Over S') ⟶ t'.G)}
    (hl : ∀ a, (lev' a).left ≫ ν.φ = f ≫ (lev a).left) {k : Type} [Field k] {y : Sp k ⟶ S'} {β : RZ H n N →+* k}
    (h : GeomAt D t' lev' y β) : GeomAt D t lev (y ≫ f) β := by
  obtain ⟨hdet, I, hI, hA⟩ := h
  have hL : LBIso t'.PP.L (t.PP.L.pull ν.cm.F) := by
    obtain ⟨w, hw, -⟩ := ν.lin
    exact ⟨w, hw⟩
  refine ⟨(detCond_iff_of_sabMap E H D S S' t t' f ⟨ν⟩ k y _).1 hdet,
    ObjPull.tateMove (ObjPull.pushEquiv ν.cart (Over.mk y)).symm (fun c g => ?_) (fun m g g' c hc => ?_) I,
    hI, fun a => ?_⟩
  · obtain ⟨g, rfl⟩ := (ObjPull.pushEquiv ν.cart (Over.mk y)).surjective g
    rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_eq]
    apply Over.OverMorphism.ext
    show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
    rw [Category.assoc, ← ν.act, Category.assoc]
  · exact (weilIs_iff_of_isGrpPullback_comm S S' t.G t'.G f ν.cm.F t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB ν.cart hL
      (Over.mk y) m _ _ g g' _ (ObjPull.pushEquiv_symm_left ν.cart (Over.mk y) g).symm
      (ObjPull.pushEquiv_symm_left ν.cart (Over.mk y) g').symm).1 hc
  · apply Over.OverMorphism.ext
    show _ = (I.ev N a).left ≫ ν.φ
    rw [← hA, Over.comp_left, Over.comp_left, ObjPull.toUnit_left', ObjPull.toUnit_left', Category.assoc, hl]
    exact Category.assoc _ _ _

theorem geomAt_of_dense (hL : Out.Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] [IsReduced S] [ConnectedSpace S]
    (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lev : D.La → (𝟙_ (Over S) ⟶ t.G)) (hN : 0 < N)
    (hp : IsProper t.G.hom) (ha : Out.RelAmple t.G t.PP.L) (hk : Out.KTriv t.G t.PP.L)
    (hd : Dense {p : S | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ S)
      (β : RZ H n N →+* K), p ∈ Set.range x ∧ x ≫ s = spMap β ∧ GeomAt D t lev x β})
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : Sp K ⟶ S) (β : RZ H n N →+* K) (hx : x ≫ s = spMap β) :
    GeomAt D t lev x β := by
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace t.G.left := GeometricallyConnected.connectedSpace t.G.hom t.G.hom.isOpenMap
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected t.G.hom (Classical.arbitrary _)
  let P : Out.PolAV S :=
    { A := t.G, g := g, smoothDim := hg, L := t.PP.L, isLB := t.PP.isLB, ample := ha, ktriv := hk
      isAb := ⟨t.semi.comm, t.semi.smooth, hp, t.semi.geomConnected⟩
      rigid := ObjDim.rigidified
      sym := ObjDim.sym }
  have hdet : DetCond D t.act x (β (RZ.rt H n N)) :=
    GlobalTheory.T.determinantCondition_spreads_of_dense_points E H D S t.G g t.act _ s _ hg (rt_sq H n N) (hd.mono fun p hp => by
      obtain ⟨K, _, _, _, x, β, h₁, h₂, h₃, -⟩ := hp
      exact ⟨K, inferInstance, inferInstance, inferInstance, x, β, h₁, h₂, h₃⟩) K x β hx
  refine ⟨hdet, ?_⟩
  have hdim : g = Module.finrank ℚ E / 2 * (D.p + D.q) :=
    ObjDim.dim_eq_of_detCond D t.act x (by rw [← map_pow, rt_sq, map_neg, map_natCast]) hdet
      ((smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback t.G.hom x) hg)
  have e₀ : ∀ {K : Type} [Field K] (x : Sp K ⟶ S),
      (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) = toUnit (Over.mk x) := fun x =>
    Over.OverMorphism.ext (ObjPull.toUnit_left' (Over.mk x)).symm
  have hcard : ∀ m, 0 < m → Nat.card {z : Over.mk x ⟶ t.G // z ^ m = 1} = m ^ Module.finrank ℤ D.La := fun m hm => by
    rw [finrank_int_lattice D, ← hdim]
    exact (hL.mulN S P m hm).2.2.2.2 K x (Nat.cast_ne_zero.2 hm.ne')
  obtain ⟨I, hI, hA⟩ := GlobalTheory.TateTower.tateIso_of_levels E H D K (Over.mk x ⟶ t.G) (fun c z => z ≫ t.act.act c)
    (fun n z z' c => Out.WeilIs t.G t.PP.L n z z' (unitOn c)) N (β (RZ.ze H n N)) _ id
    (fun i => toUnit _ ≫ lev i) hN
    (fun n hn => Nat.finite_of_card_ne_zero (by rw [hcard n hn]; positivity))
    (fun n m z z' c hn hm hz hz' h => by
      have e : unitOn (c ^ m) = unitOn c ^ m := map_pow _ _ _
      have u : IsUnit ((n * m : ℕ) : K) := (Nat.cast_ne_zero.2 (Nat.mul_pos hn hm).ne').isUnit
      have u' := u.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      rw [map_natCast] at u'
      rw [e]
      exact weilIs_lower P hL.weil hm u' hz hz' h)
    (fun m hm => by
      have hn := Nat.mul_pos hN hm
      obtain ⟨ζ, ev, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := GlobalTheory.T.exists_level_isometry_of_dense_geometric_points hL E H D S P t.act.act _ s (RZ.ze H n N) _
        id lev (N * m) m hn (hd.mono fun p hp => by
          obtain ⟨K, _, _, _, x, β, h₁, h₂, -, I, h₃, h₄⟩ := hp
          exact ⟨K, inferInstance, x, β, I.ζ (N * m), I.ev (N * m), Nat.cast_ne_zero.2 hn.ne', h₁, h₂, I.ζ_prim _ hn,
            I.add _, fun v => (I.onto _ hn _).2 ⟨v, rfl⟩, I.lin _, I.isom _ hn,
            by rw [← h₃, ← I.ζ_pow N m hN hm, Units.val_pow_eq_pow_val],
            fun i => (I.tower N m hN hm _).trans ((h₄ i).symm.trans (congrArg (· ≫ lev i) (e₀ x).symm))⟩)
          K x β (Nat.cast_ne_zero.2 hn.ne') hx
      obtain ⟨h₈, h₉⟩ := GlobalTheory.T.torsionIsometry_primitiveRoot_bijective_mod_n E H D K (Over.mk x ⟶ t.G)
        (fun z z' c => Out.WeilIs t.G t.PP.L (N * m : ℕ) z z' (unitOn c)) (N * m) ζ ev hn (hcard _ hn)
        (fun _ _ _ h => eq_one_of_weilIs_one P hL.weil h) h₁ h₂ h₃ h₅
      exact ⟨ζ, ev, h₁, h₂, h₄, h₈, h₉, h₅, h₆, fun i => (h₇ i).trans (congrArg (· ≫ lev i) (e₀ x))⟩)
  exact ⟨I, hI, fun a => (hA a).symm⟩

theorem fullObj_of_genericFibre : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (s : Sp V ⟶ Sp (RZ H n N)) (t : SAB H (Sp V)) (lv : D.La → (𝟙_ (Over (Sp V)) ⟶ t.G)) (tK : SAB H (Sp K)) (ν : SABMap tK t (spMap (algebraMap V K))) (lvK : D.La → (𝟙_ (Over (Sp K)) ⟶ tK.G)), 0 < N → IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ a c, lv (a + c) = lv a * lv c) → (∀ a, lv (N • a) = 1) → (∀ a, (lvK a).left ≫ ν.φ = spMap (algebraMap V K) ≫ (lv a).left) → FullObj D (spMap (algebraMap V K) ≫ s) tK lvK → FullObj D s t lv := by
  intro hL _ E _ _ _ H D n N V K _ _ _ _ _ _ s t lv tK ν lvK hN hp ha hk hadd hker hl o
  refine ⟨hp, ha, hk, hadd, hker, fun k _ _ _ x β hx => ?_⟩
  have : CharZero V := (Spec.preimage x).hom.charZero
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective V K)
  let Ω := AlgebraicClosure K
  let y : Sp Ω ⟶ Sp K := spMap (algebraMap K Ω)
  obtain ⟨b, hb⟩ : ∃ b : RZ H n N →+* Ω, y ≫ spMap (algebraMap V K) ≫ s = spMap b :=
    ⟨(Spec.preimage (y ≫ spMap (algebraMap V K) ≫ s)).hom, (Spec.map_preimage _).symm⟩
  have hΩ : GeomAt D t lv (y ≫ spMap (algebraMap V K)) b := GeomAt.push ν hl (o.geom Ω y b hb)
  have hdense : Dense {(⊥ : PrimeSpectrum V)} := by
    rw [dense_iff_closure_eq, PrimeSpectrum.closure_singleton]
    simp
  refine geomAt_of_dense hL s t lv hN hp ha hk (Dense.mono ?_ hdense) k x β hx
  rintro _ rfl
  refine ⟨Ω, inferInstance, inferInstance, inferInstance, _, b, ⟨(⊥ : PrimeSpectrum Ω), ?_⟩,
    (Category.assoc _ _ _).trans hb, hΩ⟩
  apply PrimeSpectrum.ext
  show Ideal.comap (algebraMap V K) (Ideal.comap (algebraMap K Ω) ⊥) = ⊥
  rw [Ideal.comap_bot_of_injective _ (algebraMap K Ω).injective,
    Ideal.comap_bot_of_injective _ (IsFractionRing.injective V K)]

end GlobalTheory.FullSpread
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullObjectOfGenericFibreDvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullObject_of_genericFibre_dvr : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (s : Sp V ⟶ Sp (RZ H n N)) (t : SAB H (Sp V)) (lv : D.La → (𝟙_ (Over (Sp V)) ⟶ t.G)) (tK : SAB H (Sp K)) (ν : SABMap tK t (spMap (algebraMap V K))) (lvK : D.La → (𝟙_ (Over (Sp K)) ⟶ tK.G)), 0 < N → IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ a c, lv (a + c) = lv a * lv c) → (∀ a, lv (N • a) = 1) → (∀ a, (lvK a).left ≫ ν.φ = spMap (algebraMap V K) ≫ (lv a).left) → FullObj D (spMap (algebraMap V K) ≫ s) tK lvK → FullObj D s t lv := by
  first | exact @GlobalTheory.FullSpread.fullObj_of_genericFibre | exact GlobalTheory.FullSpread.fullObj_of_genericFibre | (intros; apply GlobalTheory.FullSpread.fullObj_of_genericFibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyModuliOfLevelDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyModuliOfLevelDvd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.LevelUp

theorem eq_constPt_of_formallyUnramified {k : Type} [Field k] {X Y : Scheme.{0}} (f : X ⟶ Y) [FormallyUnramified f]
    (x : Sp (DualNumber k) ⟶ X) (h : x ≫ f = Geo.Tor.constPt (x ≫ f)) : x = Geo.Tor.constPt x := by
  let π : CommRingCat.of (DualNumber k) ⟶ CommRingCat.of k := CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom
  have hπ : Function.Surjective π := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hn : IsNilpotent (RingHom.ker π.hom) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro a ha c hc
    have ha' : a.fst = 0 := ha
    have hc' : c.fst = 0 := hc
    rw [Ideal.mem_bot]
    ext <;> simp [ha', hc']
  have := IsClosedImmersion.spec_of_surjective π hπ
  refine FormallyUnramified.hom_ext (Spec.map π) (isNilpotent_ker_specMap π hn) f ?_
    (h.trans (by simp only [Geo.Tor.constPt, Category.assoc]))
  have e : Spec.map π ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  rw [Geo.Tor.constPt, ← Category.assoc, e, Category.id_comp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l₂ : Level H}

theorem finiteDimensional_KA (l : Level H) : FiniteDimensional ℚ (KA l) := by
  refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
  rcases hx with rfl | rfl
  · refine IsIntegral.of_pow two_pos ?_
    rw [H.sqrt_neg_disc_sq]
    exact (isIntegral_algebraMap (x := (H.d : ℚ))).neg
  · refine IsIntegral.of_pow l.A_pos ?_
    rw [show zeta l.A ^ l.A = 1 from (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]
    exact isIntegral_one

theorem formallyUnramified_spMap (j : KA l →+* KA l₂) : FormallyUnramified (spMap j) := by
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
  have := finiteDimensional_KA l₂
  have : Algebra.FormallyUnramified ℚ (KA l₂) := Algebra.FormallyUnramified.of_isSeparable ℚ (KA l₂)
  let _ : Algebra (KA l) (KA l₂) := j.toAlgebra
  exact Algebra.FormallyUnramified.of_restrictScalars ℚ (KA l) (KA l₂)

theorem exists_obj_of_eq {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s s' : S ⟶ Sp B} (e : s = s')
    (o : Obj D l b s) : ∃ o' : Obj D l b s', Nonempty (ObjMap o' o (𝟙 S)) := by
  subst e
  exact ⟨o, ⟨ObjComp.objMapId o⟩⟩

theorem nonempty_objMap_of_eq {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'}
    {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {o : Obj D l b s} {o' : Obj D l b' s'} {f g : S' ⟶ S}
    (e : f = g) (m : ObjMap o' o f) : Nonempty (ObjMap o' o g) := by
  subst e
  exact ⟨m⟩

theorem exists_objMap_lower {B : Type} [CommRing B] {b : Base l B} {b₂ : Base l₂ B} {S S₂ T : Scheme.{0}}
    {s : S ⟶ Sp B} {s₂ : S₂ ⟶ Sp B} {t : T ⟶ Sp B} {o : Obj D l b s} {o₂ : Obj D l₂ b₂ s₂} {o' : Obj D l₂ b₂ t}
    (h : l.Dvd l₂) (hρ : b.ρ = b₂.ρ) (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A)) {π : S₂ ⟶ S} (m : SABMap o₂.t o.t π)
    (h₁ : ∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = π ≫ (o.eta a).left)
    (h₂ : ∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = π ≫ (o.etaA a).left)
    {g : T ⟶ S₂} (u : ObjMap o' o₂ g) :
    ∃ n : ObjMap (ObjLower.lower o' h hρ hζ) o (g ≫ π), n.toSABMap.φ = u.toSABMap.φ ≫ m.φ := by
  obtain ⟨n, hn⟩ := ObjMaps.exists_sab_comp m u.toSABMap
  have hn' : n.cm.F = u.cm.F ≫ m.cm.F := hn
  refine ⟨⟨n, fun a => ?_, fun a => ?_⟩, hn⟩
  · change (o'.eta a ^ (l₂.M / l.M)).left ≫ n.cm.F = _
    rw [hn']
    refine ObjComp.sec_comp (h₁ a) ?_
    rw [← ObjLower.map_nsmul_of_add _ o'.eta_add, ← ObjLower.map_nsmul_of_add _ o₂.eta_add]
    exact u.eta _
  · change (o'.etaA a ^ (l₂.A / l.A)).left ≫ n.cm.F = _
    rw [hn']
    refine ObjComp.sec_comp (h₂ a) ?_
    rw [← ObjLower.map_nsmul_of_add _ o'.etaA_add, ← ObjLower.map_nsmul_of_add _ o₂.etaA_add]
    exact u.etaA _

end GlobalTheory.LevelUp

namespace GlobalTheory

open LevelUp

theorem nonempty_moduli_of_dvd : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H), 1 ≤ D.p + D.q → l.Dvd l₂ → Nonempty (Moduli D l) → Nonempty (Moduli D l₂) := by
  intro hL _ E _ _ _ H D l l₂ hpq hd ⟨Xo⟩
  have hA : l.A ∣ l₂.A := hd.2.2
  let j := levelFieldIncl hA
  let b := baseOfFinerLevel hA
  have hρ : b.ρ = (baseKA l₂).ρ := baseOfFinerLevel_rho hA
  have hζ : b.ζ = (baseKA l₂).ζ ^ (l₂.A / l.A) := baseOfFinerLevel_zeta hA
  have jρ : j (baseKA l).ρ = b.ρ := levelFieldIncl_rho hA
  have jζ : j (baseKA l).ζ = b.ζ := levelFieldIncl_zeta hA
  obtain ⟨o₁, ⟨m₀⟩⟩ := obj_pull E H D l _ _ (baseKA l) b j _ _ Xo.s (pullback.snd Xo.s (spMap j))
    (pullback.fst Xo.s (spMap j)) jρ jζ pullback.condition Xo.univ
  obtain ⟨S₂, π, o₂, m, hfin, het, -, ⟨h₁, h₂⟩, huniv⟩ :=
    GlobalTheory.T.exists_finiteEtale_deeper_level_cover hL E H D l l₂ _ b (baseKA l₂) _ _ o₁ hpq hd hρ hζ
  have hsm : SmoothOfRelativeDimension D.dim (pullback.snd Xo.s (spMap j)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) Xo.smooth
  refine ⟨{ X := S₂, s := π ≫ pullback.snd Xo.s (spMap j), qproj := ?_, smooth := ?_, univ := o₂,
            rep := ?_, unram := ?_ }⟩
  · exact isQProjOver_comp_of_isFinite_noetherian _ _ _ _ _ hfin
      ((isQProjOver_baseChange_and_finite_restrict _ _ j _ Xo.s).1 Xo.qproj)
  · have : SmoothOfRelativeDimension (0 + D.dim) (π ≫ pullback.snd Xo.s (spMap j)) := inferInstance
    rwa [zero_add] at this
  · intro S t hS o
    obtain ⟨f₀, ⟨hf₀, ⟨n⟩⟩, hu₀⟩ := moduli_rep_of_base ObjMaps.id_comp_cancel E H D l Xo _ b j S t
      (ObjLower.lower o hd hρ hζ) hS jρ jζ
    obtain ⟨f, hf₁, hf₂⟩ : ∃ f : S ⟶ pullback Xo.s (spMap j), f ≫ pullback.fst _ _ = f₀ ∧ f ≫ pullback.snd _ _ = t :=
      ⟨pullback.lift f₀ t hf₀, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    subst hf₁ hf₂
    obtain ⟨m', -⟩ := ObjComp.objMap_cancel m₀ n
    obtain ⟨h, ⟨hh, u, -⟩, hu⟩ := huniv S f o m'.toSABMap ⟨m'.eta, m'.etaA⟩
    refine ⟨h, ⟨by rw [← Category.assoc, hh], ⟨u⟩⟩, ?_⟩
    rintro g ⟨hg, ⟨v⟩⟩
    obtain ⟨w, hw⟩ := exists_objMap_lower hd hρ hζ m h₁ h₂ v
    obtain ⟨w', -⟩ := ObjComp.objMap_comp m₀ w
    have e : g ≫ π = f := by
      refine pullback.hom_ext (hu₀ _ ⟨?_, ⟨w'⟩⟩) (by rw [Category.assoc, hg])
      rw [Category.assoc, pullback.condition, ← hg]
      simp only [Category.assoc]
    subst e
    refine hu g ⟨rfl, v, hw.symm.trans ?_⟩
    exact obj_rigid_closed hL E H D l _ _ b b _ _ _ _ o₁ (ObjLower.lower o hd hρ hζ) (g ≫ π) (Or.inl hS)
      w.toSABMap m'.toSABMap fun a => ⟨_, w.eta a, m'.eta a⟩
  · rintro k _ x o ⟨u⟩ ⟨u'⟩
    have hj := formallyUnramified_spMap j
    have hp : FormallyUnramified (pullback.fst Xo.s (spMap j)) :=
      (HasRingHomProperty.isStableUnderBaseChange (P := @FormallyUnramified.{0})
        RingHom.FormallyUnramified.isStableUnderBaseChange).of_isPullback (IsPullback.of_hasPullback _ _).flip hj
    have hr : FormallyUnramified (π ≫ pullback.fst Xo.s (spMap j)) :=
      MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance hp
    refine eq_constPt_of_formallyUnramified (π ≫ pullback.fst Xo.s (spMap j)) x ?_
    obtain ⟨w, -⟩ := exists_objMap_lower hd hρ hζ m h₁ h₂ u
    obtain ⟨w', -⟩ := exists_objMap_lower hd hρ hζ m h₁ h₂ u'
    have e : (x ≫ π ≫ pullback.snd Xo.s (spMap j)) ≫ spMap j = (x ≫ π ≫ pullback.fst Xo.s (spMap j)) ≫ Xo.s := by
      simp only [Category.assoc, pullback.condition]
    obtain ⟨o', ⟨i⟩⟩ := exists_obj_of_eq e (objRestrictBase j (ObjLower.lower o hd hρ hζ) jρ jζ)
    let i' : ObjMap o' (ObjLower.lower o hd hρ hζ) (𝟙 _) := ⟨i.toSABMap, i.eta, i.etaA⟩
    obtain ⟨n, -⟩ := ObjComp.objMap_comp (ObjComp.objMap_comp m₀ w).choose i'
    obtain ⟨n', -⟩ := ObjComp.objMap_comp (ObjComp.objMap_comp m₀ w').choose i'
    exact Xo.unram k _ o' (nonempty_objMap_of_eq (by simp only [Category.assoc, Category.id_comp]) n)
      (nonempty_objMap_of_eq (by simp only [Geo.Tor.constPt, Category.assoc, Category.id_comp]) n')

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyModuliOfLevelDvdStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_moduli_of_level_dvd : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H), 1 ≤ D.p + D.q → l.Dvd l₂ → Nonempty (Moduli D l) → Nonempty (Moduli D l₂) := by
  first | exact @GlobalTheory.nonempty_moduli_of_dvd | exact GlobalTheory.nonempty_moduli_of_dvd | (intros; apply GlobalTheory.nonempty_moduli_of_dvd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KTrivNearGoodPrime
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

namespace GlobalTheory.ZM.NearBuild

private theorem isGrpPullback_pullback_fst {S S' : Scheme.{0}} (G : Over S) [GrpObj G] (f : S' ⟶ S) :
    IsGrpPullback ((Over.pullback f).obj G) G f (pullback.fst G.hom f) := by
  refine ⟨IsPullback.of_hasPullback G.hom f, ?_⟩
  intro T x y x₀ y₀ hx hy
  have h := GlobalTheory.UU.toBase_mul_pullback G f T x y
  have ex : x₀ = Out.toBase (A := G) (A' := (Over.pullback f).obj G) (g := pullback.fst G.hom f) pullback.condition x := by
    ext
    simp [hx, Out.toBase]
  have ey : y₀ = Out.toBase (A := G) (A' := (Over.pullback f).obj G) (g := pullback.fst G.hom f) pullback.condition y := by
    ext
    simp [hy, Out.toBase]
  rw [ex, ey, ← h]
  simp [Out.toBase]

theorem kTriv_near_good_prime : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)) (q₀ : Ideal R), q₀ ∈ objPrimes b Mat κ β v → PolFam b Mat κ β v A L act Q → ∃ f : R, f ∉ q₀ ∧ Out.KTriv ((Over.pullback (spMap (loc f))).obj A) (L.pull (pullback.fst A.hom (spMap (loc f)))) := by
  intro o _ g N' J b Mat κ R _ _ β v A _ L act Q q₀ hq hP
  obtain ⟨K, _, _, x, s, t, hker, hgood⟩ := mem_objPrimes.1 hq
  obtain ⟨hab, -, hLB, -, -, hamp, -, hfib⟩ := hP
  obtain ⟨ψ, hψ, hiso⟩ := hfib K x s t hgood
  obtain ⟨e, he, hcomp⟩ := grpPullback_iso (isGrpPullback_pullback_fst A (spMap x)) hψ.1
  haveI := he
  have hLB' : (L.pull (pullback.fst A.hom (spMap x))).IsLB := pull_isLB hLB _
  have hLt : (t.L.pull e.hom.left).IsLB := pull_isLB t.isLB _
  have hψL : (L.pull ψ).IsLB := pull_isLB hLB ψ
  have hcls : LBIso (L.pull (pullback.fst A.hom (spMap x))) (t.L.pull e.hom.left) := by
    rw [← GlobalTheory.CechPic.cls_eq_iff hLB' hLt, GlobalTheory.CechPic.cls_pull hLB _ hLB', GlobalTheory.CechPic.cls_pull t.isLB _ hLt,
      ← hcomp, GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull hLB ψ hψL,
      ← (GlobalTheory.CechPic.cls_eq_iff t.isLB hψL).2 hiso]
  have hfibK := (amplePt (Sp K) K (𝟙 _) t.A _ e.hom.left (isGrpPullback_of_iso e) t.L _ t.isLB hLB' hcls
    t.ample t.ktriv).2
  obtain ⟨f, hf, hk⟩ := kTriv_away_of_kTriv_fibre globalFns_holds R A L K x hab hLB hamp hfibK
  refine ⟨f, fun h => hf ?_, hk⟩
  rw [← hker, RingHom.mem_ker] at h
  exact h

end GlobalTheory.ZM.NearBuild
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfPolarisedAtEveryPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfPolarisedAtEveryPoint
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.AmpleGlobal

theorem exists_lift_fieldExtension {S S' : Scheme.{0}} (f : S' ⟶ S) {K₀ : Type} [Field K₀] (x : Sp K₀ ⟶ S)
    (a : Sp K₀) (q : S') (h : f q = x a) :
    ∃ (K : Type) (_ : Field K) (i : K₀ →+* K) (u : Sp K ⟶ S'), u ≫ f = spMap i ≫ x := by
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback q a h
  refine ⟨(pullback f x).residueField z, inferInstance,
    (Spec.preimage ((pullback f x).fromSpecResidueField z ≫ pullback.snd f x)).hom,
    (pullback f x).fromSpecResidueField z ≫ pullback.fst f x, ?_⟩
  change _ = Spec.map (CommRingCat.ofHom _) ≫ x
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, Category.assoc, Category.assoc, pullback.condition]

theorem relAmple_of_pointwise {S : Scheme.{0}} [IsLocallyNoetherian S] (G : Over S) [IsProper G.hom] [Flat G.hom]
    (M : LB G.left) (hM : M.IsLB)
    (hproj : ∀ (A : Type) [CommRing A] (y : Sp A ⟶ S) (B : Over (Sp A)) (φ : B.left ⟶ G.left),
      IsPullback φ B.hom G.hom y → IsProjOver B.hom)
    (hpt : ∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (G' : Over S') (φ : G'.left ⟶ G.left) (L' : LB G'.left),
      IsPullback φ G'.hom G.hom f ∧ L'.IsLB ∧ LBIso L' (M.pull φ) ∧ p ∈ Set.range f ∧ Out.RelAmple G' L') :
    Out.RelAmple G M := by
  refine GlobalTheory.AmpleLocal.relAmple_of_locally S G M hM inferInstance inferInstance (fun s => ?_)
  obtain ⟨V, hV, hsV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (by first | exact AlgebraicGeometry.isBasis_affine_open S | exact S.isBasis_affineOpens | exact AlgebraicGeometry.Scheme.isBasis_affineOpens S | exact isBasis_affineOpens S)) (show s ∈ (⊤ : S.Opens) from trivial)
  have hV' : IsAffineOpen V := hV
  have : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV'⟩
  let y : Spec (CommRingCat.of Γ(S, V)) ⟶ S := hV'.fromSpec
  let q := hV'.primeIdealOf ⟨s, hsV⟩
  have hq : hV'.fromSpec q = s := hV'.fromSpec_primeIdealOf ⟨s, hsV⟩
  let g : Γ(S, V) →+* q.asIdeal.ResidueField := algebraMap _ _
  let B : Over (Spec (CommRingCat.of Γ(S, V))) := Over.mk (pullback.snd G.hom y)
  have hB : IsPullback (pullback.fst G.hom y) B.hom G.hom y := IsPullback.of_hasPullback _ _
  have hLB : (M.pull (pullback.fst G.hom y)).IsLB := pull_isLB hM _
  have hflat : Flat B.hom := by
    first | (show Flat (pullback.snd G.hom y); infer_instance) | exact MorphismProperty.pullback_snd _ _ inferInstance
  have hprojB := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver _).2 (hproj _ y B _ hB)
  have hfib : Out.RelAmple ((Over.pullback (Spec.map (CommRingCat.ofHom g))).obj B)
      ((M.pull (pullback.fst G.hom y)).pull (pullback.fst B.hom (Spec.map (CommRingCat.ofHom g)))) := by
    obtain ⟨S', f, G', φ, L', hφ, hL', e, ⟨s', hs'⟩, hA'⟩ := hpt s
    let x : Sp q.asIdeal.ResidueField ⟶ S := Spec.map (CommRingCat.ofHom g) ≫ y
    let a : Sp q.asIdeal.ResidueField := IsLocalRing.closedPoint _
    have ha : x a = s := by
      have hpt' : (Spec.map (CommRingCat.ofHom g)) a = q := by
        apply PrimeSpectrum.ext
        change Ideal.comap g (IsLocalRing.maximalIdeal _) = q.asIdeal
        rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]
      first
        | (show y ((Spec.map (CommRingCat.ofHom g)) a) = s
           rw [hpt']
           exact hq)
        | exact (Scheme.comp_base_apply _ _ _).trans (by rw [hpt']; exact hq)
    obtain ⟨K, _, i, u, hu⟩ := exists_lift_fieldExtension f x a s' (hs'.trans ha.symm)
    have h₂ : IsPullback (pullback.fst G.hom (spMap i ≫ x)) (pullback.snd G.hom (spMap i ≫ x)) G.hom
        (spMap i ≫ x) := IsPullback.of_hasPullback _ _
    have hA₂ := GlobalTheory.FibreAmple.relAmple_of_factor hM hφ h₂ u hu hL' e hA'
    exact GlobalTheory.FibreAmple.relAmple_of_fieldExtension hM i
      ((IsPullback.of_hasPullback B.hom (Spec.map (CommRingCat.ofHom g))).paste_horiz hB) h₂
      (pull_isLB hLB _) (GlobalTheory.FibreAmple.lbIso_pull_pull hM _ _) hA₂
  obtain ⟨r, hr, hA⟩ := GlobalTheory.AmpleNear.relAmple_near_fibre Γ(S, V) B (M.pull (pullback.fst G.hom y)) hflat hprojB hLB
    q.asIdeal.ResidueField g (GlobalTheory.FibreAmple.residueField_fraction q.asIdeal) hfib
  let U₀ : (Spec (CommRingCat.of Γ(S, V))).Opens := PrimeSpectrum.basicOpen r
  let j := U₀.ι
  have : IsOpenImmersion y := by dsimp only [y]; infer_instance
  have : IsOpenImmersion j := by dsimp only [j]; exact inferInstance
  have hqr : q ∈ PrimeSpectrum.basicOpen r :=
    (PrimeSpectrum.mem_basicOpen _ _).2 fun h => hr ((Ideal.algebraMap_residueField_eq_zero).2 h)
  refine ⟨(j ≫ y).opensRange, ⟨⟨q, hqr⟩, ?_⟩, ?_⟩
  · rw [← hq]
    rfl
  · have hu : (j ≫ y).isoOpensRange.inv ≫ (j ≫ y) = (j ≫ y).opensRange.ι := by
      rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
    exact GlobalTheory.FibreAmple.relAmple_of_factor hM ((IsPullback.of_hasPullback B.hom j).paste_horiz hB)
      (isPullback_morphismRestrict G.hom _).flip _ hu (pull_isLB hLB _) (GlobalTheory.FibreAmple.lbIso_pull_pull hM _ _) hA

theorem relAmple_of_polarised_at_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S), IsProper t.G.hom → (∀ (A : Type) [CommRing A] (y : Sp A ⟶ S) (B : Over (Sp A)) (φ : B.left ⟶ t.G.left), IsPullback φ B.hom t.G.hom y → IsProjOver B.hom) → (∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (_ : SABMap t' t f), p ∈ Set.range f ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L) → Out.RelAmple t.G t.PP.L := by
  intro E _ _ _ H S _ t hP hproj hpt
  have hflat : Flat t.G.hom := by
    first
      | exact inferInstance
      | (haveI := t.semi.smooth; infer_instance)
  refine relAmple_of_pointwise t.G t.PP.L t.PP.isLB hproj (fun p => ?_)
  obtain ⟨S', f, t', m, hp, hA, -⟩ := hpt p
  refine ⟨S', f, t'.G, m.cm.F, t'.PP.L, m.cart.1, t'.PP.isLB, ?_, hp, hA⟩
  first
    | (obtain ⟨w, hw, -⟩ := m.lin; exact ⟨w, hw⟩)
    | (obtain ⟨w, hw⟩ := m.lin; exact ⟨w, hw⟩)
    | (obtain ⟨w, hw, -⟩ := m.lin; exact ⟨w, hw.1⟩)
    | (obtain ⟨w, -, hw, -⟩ := m.lin; exact ⟨w, hw⟩)
    | (obtain ⟨w, hw, -⟩ := m.lin; exact (hw : False))

end GlobalTheory.AmpleGlobal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfPolarisedAtEveryPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_of_polarised_at_every_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S), IsProper t.G.hom → (∀ (A : Type) [CommRing A] (y : Sp A ⟶ S) (B : Over (Sp A)) (φ : B.left ⟶ t.G.left), IsPullback φ B.hom t.G.hom y → IsProjOver B.hom) → (∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (_ : SABMap t' t f), p ∈ Set.range f ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L) → Out.RelAmple t.G t.PP.L := by
  first | exact @GlobalTheory.AmpleGlobal.relAmple_of_polarised_at_points | exact GlobalTheory.AmpleGlobal.relAmple_of_polarised_at_points | (intros; apply GlobalTheory.AmpleGlobal.relAmple_of_polarised_at_points <;> assumption)
end
end
