module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SqIsPowGrp
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitive
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelStructureDescendsFieldExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelStructureDescendsFieldExtension
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELDesc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

def tateAlong {k : Type} [Field k]
    {Q Q' : Type} [Group Q] [Group Q'] {act : 𝓞 E → Q → Q} {act' : 𝓞 E → Q' → Q'}
    {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop} (Φ : Q ≃* Q')
    (hact : ∀ c x, Φ (act c x) = act' c (Φ x)) (he : ∀ n x y c, e n x y c → e' n (Φ x) (Φ y) c)
    (I : TateIso D k Q act e) : TateIso D k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev := fun n a => Φ (I.ev n a)
  add := fun n a b => by simp only [I.add, map_mul]
  lin := fun n c a => by rw [← hact, I.lin]
  ker := fun n hn a => (map_eq_one_iff _ Φ.injective).trans (I.ker n hn a)
  onto := fun n hn x => by
    rw [← map_eq_one_iff Φ.symm Φ.symm.injective, map_pow, I.onto n hn]
    exact exists_congr fun a => Φ.eq_symm_apply
  tower := fun n m hn hm a => by rw [← map_pow, I.tower n m hn hm a]
  isom := fun n hn a b => he _ _ _ _ (I.isom n hn a b)

theorem tate_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (h : IsGrpPullback G' G f φ) (hI : LBIso L' (L.pull φ)) (act : 𝓞 E → (G ⟶ G)) (act' : 𝓞 E → (G' ⟶ G'))
    (hact : ∀ c, (act' c).left ≫ φ = φ ≫ (act c).left) {k : Type} [Field k] (x : Sp k ⟶ S') (y : Sp k ⟶ S)
    (hy : y = x ≫ f) :
    (∀ I' : TateIso D k (Over.mk x ⟶ G') (fun c z => z ≫ act' c) (fun n z z' c => Out.WeilIs G' L' n z z' (unitOn c)),
      ∃ I : TateIso D k (Over.mk y ⟶ G) (fun c z => z ≫ act c) (fun n z z' c => Out.WeilIs G L n z z' (unitOn c)),
        I.ζ = I'.ζ ∧ ∀ n v, (I.ev n v).left = (I'.ev n v).left ≫ φ) ∧
    (∀ I : TateIso D k (Over.mk y ⟶ G) (fun c z => z ≫ act c) (fun n z z' c => Out.WeilIs G L n z z' (unitOn c)),
      ∃ I' : TateIso D k (Over.mk x ⟶ G') (fun c z => z ≫ act' c) (fun n z z' c => Out.WeilIs G' L' n z z' (unitOn c)),
        I'.ζ = I.ζ ∧ ∀ n v, (I.ev n v).left = (I'.ev n v).left ≫ φ) := by
  subst hy
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have hA : ∀ (c : 𝓞 E) (z : Over.mk x ⟶ G'), Φ (z ≫ act' c) = Φ z ≫ act c := by
    intro c z
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, hΦ, Category.assoc, hact]
  have hA' : ∀ (c : 𝓞 E) (z : Over.mk (x ≫ f) ⟶ G), Φ.symm (z ≫ act c) = Φ.symm z ≫ act' c := by
    intro c z
    apply Φ.injective
    rw [MulEquiv.apply_symm_apply, hA, MulEquiv.apply_symm_apply]
  have hW : ∀ (n : ℕ) (z z' : Over.mk x ⟶ G') (c : kˣ),
      (Out.WeilIs G' L' n z z' (unitOn c) ↔ Out.WeilIs G L n (Φ z) (Φ z') (unitOn c)) := fun n z z' c =>
    GlobalTheory.weilIs_grpPullback_of_comm S S' G G' f φ L L' hL hL' h hI (Over.mk x) n z z' (Φ z) (Φ z') (unitOn c)
      (hΦ z) (hΦ z')
  refine ⟨fun I' => ⟨tateAlong Φ hA (fun n z z' c hz => (hW n z z' c).1 hz) I', rfl, fun n v => hΦ _⟩,
    fun I => ⟨tateAlong Φ.symm hA' (fun n z z' c hz => ?_) I, rfl, fun n v => ?_⟩⟩
  · rw [hW, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact hz
  · show _ = (Φ.symm (I.ev n v)).left ≫ φ
    rw [← hΦ, MulEquiv.apply_symm_apply]

theorem detCond_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (a : OAct (𝓞 E) G) (a' : OAct (𝓞 E) G')
    (hact : ∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) {k : Type} [Field k] (x : Sp k ⟶ S') (y : Sp k ⟶ S)
    (hy : y = x ≫ f) (ρ : k) : DetCond D a' x ρ ↔ DetCond D a y ρ := by
  subst hy
  have key : ∀ (σ : 𝓞 E →+* k) (n : ℕ), LieMult a' x σ n ↔ LieMult a (x ≫ f) σ n := fun σ n =>
    GlobalTheory.LiePull.lieMult_pull (𝓞 E) S S' G G' f φ a a' h hact k x σ n
  exact forall_congr' fun σ => and_congr (imp_congr_right fun _ => key σ _) (imp_congr_right fun _ => key σ _)

private theorem spMap_comp_var2 {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R')
    (g : R' →+* R'') : spMap g ≫ spMap f = spMap (g.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

private theorem exists_algClosed_amalgam_of_charZero {K₀ K K' : Type} [Field K₀] [Field K] [Field K'] [CharZero K'] (i : K₀ →+* K)
    (κ : K₀ →+* K') : ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : CharZero Ω) (iK : K →+* Ω) (iK' : K' →+* Ω),
      iK.comp i = iK'.comp κ := by
  let := i.toAlgebra
  let := κ.toAlgebra
  have : Nontrivial (K ⊗[K₀] K') :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K₀ K K' i.injective κ.injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[K₀] K')
  let : Field (K ⊗[K₀] K' ⧸ m) := Ideal.Quotient.field m
  let q : K ⊗[K₀] K' →+* AlgebraicClosure (K ⊗[K₀] K' ⧸ m) :=
    (algebraMap (K ⊗[K₀] K' ⧸ m) (AlgebraicClosure (K ⊗[K₀] K' ⧸ m))).comp (Ideal.Quotient.mk m)
  let jL : K →+* K ⊗[K₀] K' := (Algebra.TensorProduct.includeLeft : K →ₐ[K₀] K ⊗[K₀] K').toRingHom
  let jR : K' →+* K ⊗[K₀] K' := (Algebra.TensorProduct.includeRight : K' →ₐ[K₀] K ⊗[K₀] K').toRingHom
  refine ⟨AlgebraicClosure (K ⊗[K₀] K' ⧸ m), inferInstance, inferInstance,
    charZero_of_injective_ringHom (q.comp jR).injective, q.comp jL, q.comp jR, ?_⟩
  ext a
  have hL := (Algebra.TensorProduct.includeLeft : K →ₐ[K₀] K ⊗[K₀] K').commutes a
  have hR := (Algebra.TensorProduct.includeRight : K' →ₐ[K₀] K ⊗[K₀] K').commutes a
  exact congrArg q (hL.trans hR.symm)

theorem isPEL_descends : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g k : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (o : Type) [CommRing o] (b : TBase o k) (ρ : o) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (β₀ : o →+* K₀) (s : Sp K ⟶ Sp o) (t₀ : TObj g k J b (spMap β₀)) (t : TObj g k J b s) (τ : SAB H (Sp K)), Subring.closure (Set.range a) = ⊤ → s = spMap i ≫ spMap β₀ → TMap t t₀ (spMap i) → IsPEL D a bas ρ t τ → ∃ τ₀ : SAB H (Sp K₀), IsPEL D a bas ρ t₀ τ₀ := by
  intro hL E _ _ _ H D g k J a bas o _ b ρ K₀ K _ _ i β₀ s t₀ t τ hcl hs hT hP
  obtain ⟨φ, hφ, hLφ, hactφ, hgeo⟩ := hP
  obtain ⟨ψ, hψ, hLψ, hptψ, hactψ⟩ := hT
  have := t₀.ab.comm
  have := hφ

  have hpb : IsGrpPullback τ.G t₀.A (spMap i) (φ.hom.left ≫ ψ) :=
    IsGrpPullback.congr (IsGrpPullback.comp (isGrpPullback_of_iso φ) hψ) (Category.id_comp _) rfl
  have hLc : LBIso τ.PP.L (t₀.L.pull (φ.hom.left ≫ ψ)) := by
    obtain ⟨w, hw⟩ := hLψ
    have h2 : LBIso (t.L.pull φ.hom.left) (t₀.L.pull (φ.hom.left ≫ ψ)) :=
      iso_linComb ((isGen_iff w).1 hw) (K := PUnit) (fun _ => φ.hom.left) (fun _ => 1)
    exact LBIso.trans τ.PP.isLB (pull_isLB t.isLB _) (pull_isLB t₀.isLB _) hLφ h2
  have hφl : ∀ j, (τ.act.act (a j)).left ≫ φ.hom.left = φ.hom.left ≫ (t.act j).left := fun j => by
    rw [← Over.comp_left, hactφ j, Over.comp_left]
  obtain ⟨r, hr1, hr2⟩ := GlobalTheory.oAct_descend_of_generators (𝓞 E) J a K₀ K i t₀.A τ.G (φ.hom.left ≫ ψ) τ.act t₀.act
    hcl hpb (fun j => by rw [← Category.assoc, hφl j, Category.assoc, hactψ j, Category.assoc])
  obtain ⟨τ₀, e, he, hLe, hacte⟩ :=
    GlobalTheory.exists_triple_of_fieldExtension hL E H K₀ K i τ t₀.A (φ.hom.left ≫ ψ) t₀.L r t₀.ab hpb t₀.isLB hLc hr2
  have := he
  have hel : ∀ c, (τ₀.act.act c).left ≫ e.hom.left = e.hom.left ≫ (r.act c).left := fun c => by
    rw [← Over.comp_left, hacte c, Over.comp_left]
  have hpe : IsGrpPullback τ₀.G t₀.A (𝟙 _) e.hom.left := isGrpPullback_of_iso e
  refine ⟨τ₀, e, he, hLe, fun j => by rw [hacte, hr1], ?_⟩
  intro K' _ _ _ x' β hx'

  set κ : K₀ →+* K' := (Spec.preimage x').hom with hκ
  have hxκ : x' = spMap κ := by
    show x' = Spec.map (CommRingCat.ofHom (Spec.preimage x').hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hβ : κ.comp β₀ = β := by
    have h1 : spMap (κ.comp β₀) = spMap β := by rw [← spMap_comp_var2, ← hxκ, hx']
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      have hu := b.unit.map β
      rw [h0, Nat.cast_zero, map_zero] at hu
      exact not_isUnit_zero hu
    · exact h0

  obtain ⟨Ω, _, _, _, iK, iK', hΩ⟩ := exists_algClosed_amalgam_of_charZero i κ
  have hsq : spMap iK' ≫ x' = spMap iK ≫ spMap i := by
    rw [hxκ, spMap_comp_var2, spMap_comp_var2, hΩ]
  have hsΩ : spMap iK ≫ s = spMap (iK.comp (i.comp β₀)) := by
    rw [hs, ← Category.assoc, spMap_comp_var2, spMap_comp_var2]
  have hbr : ∀ z : o, iK (i (β₀ z)) = iK' (β z) := fun z => by
    rw [← hβ]
    exact congrArg (fun F : K₀ →+* Ω => F (β₀ z)) hΩ
  obtain ⟨hdet, I₀, hI₀ζ, hI₀ev⟩ := hgeo Ω (spMap iK) (iK.comp (i.comp β₀)) hsΩ
  have := t₀.dim
  have : Smooth t₀.A.hom := SmoothOfRelativeDimension.smooth g t₀.A.hom
  refine ⟨?_, ?_⟩
  ·
    have d1 := (detCond_pull hpb r τ.act hr2 (spMap iK) (spMap iK' ≫ x') hsq
      ((iK.comp (i.comp β₀)) ρ)).1 hdet
    have d2 : DetCond D r (spMap iK' ≫ x') (iK' (β ρ)) := by
      rw [← hbr ρ]
      exact d1
    have d3 := (GlobalTheory.detCond_iff_of_field_extension E H D (Sp K₀) t₀.A K' Ω iK' x' r (β ρ) inferInstance).1 d2
    exact (detCond_pull hpe r τ₀.act hel x' x' (Category.comp_id _).symm (β ρ)).2 d3
  ·
    obtain ⟨I₁, hI₁ζ, hI₁ev⟩ := (tate_pull t₀.isLB τ.PP.isLB hpb hLc r.act τ.act.act hr2 (spMap iK)
      (spMap iK' ≫ x') hsq).1 I₀
    obtain ⟨I, hI⟩ := (GlobalTheory.TateIsoFieldExt.tateIso_fieldExt hL E H D (Sp K₀) t₀.pol r.act K' Ω iK' x').2 I₁ r.hom
    obtain ⟨I', hI'ζ, hI'ev⟩ := (tate_pull t₀.isLB τ₀.PP.isLB hpe hLe r.act τ₀.act.act hel x' x'
      (Category.comp_id _).symm).2 I
    refine ⟨I', ?_, fun j => ?_⟩
    · rw [hI'ζ]
      apply iK'.injective
      rw [← (hI k hk).1, hI₁ζ, hI₀ζ]
      simp only [RingHom.comp_apply]
      exact hbr _
    · apply Over.OverMorphism.ext
      rw [Over.comp_left, ← hI'ev]
      show (I.ev k (bas (Pi.single j 1))).left = x' ≫ (t₀.pt j).left
      have ep := ((GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K' Ω iK').1 (Sp K') (Sp Ω) (𝟙 _) (𝟙 _) (spMap iK')
        IsPullback.of_id_snd).1
      apply ep.left_cancellation
      have e1 : (I₁.ev k (bas (Pi.single j 1))).left = spMap iK' ≫ (I.ev k (bas (Pi.single j 1))).left := by
        rw [(hI k hk).2 (bas (Pi.single j 1)), Over.comp_left]
        rfl
      have e2 : (I₀.ev k (bas (Pi.single j 1))).left ≫ φ.hom.left = spMap iK ≫ (t.pt j).left := by
        rw [← Over.comp_left, hI₀ev j, Over.comp_left]
        rfl
      rw [← e1, hI₁ev, ← Category.assoc, e2, Category.assoc, hptψ j, ← Category.assoc, ← hsq, Category.assoc]
      rfl

end GlobalTheory.PELDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelStructureDescendsFieldExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pelStructure_descends_field_extension : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g k : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (o : Type) [CommRing o] (b : TBase o k) (ρ : o) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (β₀ : o →+* K₀) (s : Sp K ⟶ Sp o) (t₀ : TObj g k J b (spMap β₀)) (t : TObj g k J b s) (τ : SAB H (Sp K)), Subring.closure (Set.range a) = ⊤ → s = spMap i ≫ spMap β₀ → TMap t t₀ (spMap i) → IsPEL D a bas ρ t τ → ∃ τ₀ : SAB H (Sp K₀), IsPEL D a bas ρ t₀ τ₀ := by
  first | exact @GlobalTheory.PELDesc.isPEL_descends | exact GlobalTheory.PELDesc.isPEL_descends | (intros; apply GlobalTheory.PELDesc.isPEL_descends <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitiveOfLaws
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ObjPull

theorem objPull_of_lie_of_ample : (∀ (O : Type) [CommRing O] (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (a : OAct O G) (a' : OAct O G'), IsGrpPullback G' G f φ → (∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S') (τ : O →+* k) (n : ℕ), LieMult a' x τ n ↔ LieMult a (x ≫ f) τ n) → (∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsAbelianScheme G → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → IsAbelianScheme G' ∧ (Out.RelAmple G L → Out.RelAmple G' L') ∧ (Out.KTriv G L → Out.KTriv G' L')) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap o' o f) := by
  intro _ hAb
  exact objPull_of_pol hAb

end GlobalTheory.ObjPull

namespace GlobalTheory

theorem obj_rigid_of_laws : Out.Laws → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), (IsReduced S' ∨ IsLocallyNoetherian S') → ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ := by
  intro hL hpol E _ _ _ H D l B B' _ _ b b' S S' s s' o o' f _
  exact obj_rigid_of_pol hL hpol E H D l B B' b b' S S' s s' o o' f

end GlobalTheory

namespace GlobalTheory.LevelFibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

section Main

theorem exists_tate_push_comm
    {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f) {k : Type} [Field k]
    (x : Sp k ⟶ S') (z : Sp k ⟶ S) (hz : x ≫ f = z) (e : (Over.mk x ⟶ t'.G) ≃* (Over.mk z ⟶ t.G))
    (he : ∀ p, (e p).left = p.left ≫ m.φ)
    (I : TateIso D k (Over.mk x ⟶ t'.G) (fun a g => g ≫ t'.act.act a)
      (fun n g g' c => Out.WeilIs t'.G t'.PP.L n g g' (unitOn c))) :
    ∃ J : TateIso D k (Over.mk z ⟶ t.G) (fun a g => g ≫ t.act.act a)
      (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)), J.ζ = I.ζ ∧ ∀ n a, J.ev n a = e (I.ev n a) := by
  exact exists_tate_push m x z hz e he I

variable {l l₂ : Level H} {Xo : Moduli D l} {Xo₂ : Moduli D l₂}

theorem exists_sim_of_fibre_comm
    (hPull : ∀ (k : Type) [Field k] (z : Sp k ⟶ Xo₂.X), ∃ o' : Obj D l₂ (baseKA l₂) (z ≫ Xo₂.s), Nonempty (ObjMap o' Xo₂.univ z))
    {k : Type} [Field k] [IsAlgClosed k]
    (hDiff : ∀ (z : Sp k ⟶ Xo.X) (I I' : TateIso D k (Over.mk z ⟶ Xo.univ.t.G) (fun a g => g ≫ Xo.univ.t.act.act a)
      (fun n g g' c => Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L n g g' (unitOn c))),
      ∃ g : Sim D, ∀ n, 0 < n → (∀ a, I'.ev n a = I.ev n (g.f n a)) ∧ I'.ζ n = I.ζ n ^ g.ν n)
    (hd : l.Dvd l₂) (r : Xo₂.X ⟶ Xo.X) (m : SABMap Xo₂.univ.t Xo.univ.t r)
    (hm : ∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left)
    (hmA : ∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left)
    (hLev : ∀ g : Sim D, g.InGam l l₂ → ∃ ρ : Xo₂.X ≅ Xo₂.X, Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r)
    (x x' : Sp k ⟶ Xo₂.X) (hr : x ≫ r = x' ≫ r) (hs : x ≫ Xo₂.s = x' ≫ Xo₂.s) :
    ∃ (g : Sim D) (ρ : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ ∧ Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r ∧ x' = x ≫ ρ.hom := by
  obtain ⟨β, hβ⟩ := exists_spMap (x ≫ Xo₂.s)
  obtain ⟨-, I, hIζ, hIA, hI⟩ := Xo₂.univ.geom k x β hβ
  obtain ⟨-, I', hIζ', hIA', hI'⟩ := Xo₂.univ.geom k x' β (hs.symm.trans hβ)
  obtain ⟨e, he⟩ := exists_ptEquiv m.cart x _ rfl
  obtain ⟨e', he'⟩ := exists_ptEquiv m.cart x' _ hr.symm
  obtain ⟨J, hJζ, hJ⟩ := exists_tate_push_comm m x _ rfl e he I
  obtain ⟨J', hJζ', hJ'⟩ := exists_tate_push_comm m x' _ hr.symm e' he' I'
  obtain ⟨g, hg⟩ := hDiff _ J J'
  have key : ∀ (σ : 𝟙_ (Over Xo₂.X) ⟶ Xo₂.univ.t.G) (τ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (d : ℕ),
      (σ ^ d).left ≫ m.φ = r ≫ τ.left → e (toUnit _ ≫ σ) ^ d = e' (toUnit _ ≫ σ) ^ d := fun σ τ d h => by
    apply Over.OverMorphism.ext
    rw [← map_pow, ← map_pow, ← MonObj.comp_pow, ← MonObj.comp_pow, he, he', unit_left, unit_left, Category.assoc,
      Category.assoc]
    exact (congrArg _ h).trans (((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ.left) hr).trans
      (Category.assoc _ _ _))).trans (congrArg _ h.symm))
  obtain ⟨hin, hη⟩ := inGam_of_diff l l₂ hd J J' g hg
    (by rw [hJζ, hJζ']; exact Units.ext (hIζ'.trans hIζ.symm))
    (fun a => e (toUnit _ ≫ Xo₂.univ.eta a)) (fun a => e' (toUnit _ ≫ Xo₂.univ.eta a))
    (fun a b => by rw [Xo₂.univ.eta_add, MonObj.comp_mul, map_mul])
    (fun a b => by rw [Xo₂.univ.eta_add, MonObj.comp_mul, map_mul])
    (fun a ha => by rw [Xo₂.univ.eta_ker a ha, MonObj.comp_one, map_one])
    (fun a ha => by rw [Xo₂.univ.eta_ker a ha, MonObj.comp_one, map_one])
    (fun a ha => by rw [hJ, hI a ha]) (fun a ha => by rw [hJ', hI' a ha])
    (fun a => key _ _ _ (hm a)) (fun a => by rw [hJ, hJ', ← hIA, ← hIA']; exact key _ _ _ (hmA a))
  have hηA : ∀ a, e' (toUnit _ ≫ Xo₂.univ.etaA a) = e (toUnit _ ≫ Xo₂.univ.etaA (g.f l₂.A a)) := fun a => by
    rw [hIA, hIA', ← hJ, ← hJ', (hg _ l₂.A_pos).1]
  obtain ⟨ρ, hρ, hρr⟩ := hLev g hin
  refine ⟨g, ρ, hin, hρ, hρr, ?_⟩
  obtain ⟨hρs, ν, hν, hνA⟩ := hρ
  obtain ⟨o, ⟨p⟩⟩ := hPull k x'
  obtain ⟨n₁, hn₁⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m p.toSABMap
  obtain ⟨n₂, hn₂⟩ := sab_cast hr.symm n₁
  obtain ⟨n, hn⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ r x m n₂
  obtain ⟨n₃, hn₃⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν n
  have lev : ∀ (s : 𝟙_ (Over (Sp k)) ⟶ o.t.G) (σ τ : 𝟙_ (Over Xo₂.X) ⟶ Xo₂.univ.t.G),
      s.left ≫ p.toSABMap.φ = x' ≫ σ.left → e' (toUnit _ ≫ σ) = e (toUnit _ ≫ τ) → τ.left ≫ ν.φ = ρ.hom ≫ σ.left →
      s.left ≫ n₃.φ = (x ≫ ρ.hom) ≫ σ.left := fun s σ τ h₁ h₂ h₃ => by
    have h₄ : s.left ≫ n.φ = x ≫ τ.left := by
      apply m.cart.1.hom_ext
      · have := congrArg (fun w => w.left) h₂
        simp only [he, he', unit_left] at this
        refine Eq.trans ?_ this
        rw [← h₁, Category.assoc, Category.assoc]
        exact congrArg _ (hn.symm.trans (hn₂.trans hn₁))
      · rw [Category.assoc, Category.assoc, n.cart.1.w, ← Category.assoc, sec_w, sec_w]
        exact (Category.id_comp x).trans (Category.comp_id x).symm
    rw [hn₃, ← Category.assoc, h₄, Category.assoc, Category.assoc]
    exact congrArg _ h₃
  obtain ⟨f, -, hf⟩ := Xo₂.rep (Sp k) (x' ≫ Xo₂.s) inferInstance o
  rw [hf x' ⟨rfl, ⟨p⟩⟩]
  refine (hf _ ⟨by rw [Category.assoc, hρs, hs], ⟨⟨n₃, fun a => ?_, fun a => ?_⟩⟩⟩).symm
  · exact lev _ _ _ (p.eta a) (hη a) (hν a)
  · exact lev _ _ _ (p.etaA a) (hηA a) (hνA a)

end Main

theorem levelMap_fibre_simply_transitive_of_laws :
    Out.Laws → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l
        : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j
        : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f
        : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap
        o' o f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D
        : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b
        : Base l B) (b' : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s'
        : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o''
        : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f'
        : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫
        f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫
        f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)) → (∀ (E
        : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B
        : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
        : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 *
        (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → (∀ (E
        : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂
        : Level H) (B : Type) [CommRing B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s
        : S ⟶ Sp B) (o₂ : Obj D l₂ b₂ s), l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (o
        : Obj D l b s) (m : SABMap o₂.t o.t (𝟙 S)), (∀ a, (o₂.eta a ^ (l₂.M /
        l.M)).left ≫ m.φ = 𝟙 S ≫ (o.eta a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A /
        l.A)).left ≫ m.φ = 𝟙 S ≫ (o.etaA a).left)) → (∀ (E : Type) [Field E] [NumberField
        E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing
        B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s'
        : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), (IsReduced S' ∨
        IsLocallyNoetherian S') → ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta
        a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ) → (∀ (E : Type) [Field
        E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo
        : Moduli D l) (B : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s
        : S ⟶ Sp B) (o : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA
        l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ
        f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (k
        : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e
        : ℕ → Q → Q → kˣ → Prop), (∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c') → ∀ I I' : TateIso D k Q act e, ∃ g : Sim D, ∀ n, 0 < n → (∀ a, I'.ev n a = I.ev n (g.f
        n a)) ∧ I'.ζ n = I.ζ n ^ g.ν n) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H
        : Host E) (D : Datum H), 1 ≤ D.p + D.q → (∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n
        : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n
        : ℤ)) ∧ (∃ g : Sim D, ∀ n, g.f n = LinearMap.id ∧ g.ν n = 1) ∧ (∀ g g' : Sim D, ∃ g'' : Sim D, ∀ n, g''.f n = g.f n ∘ₗ g'.f n ∧ g''.ν n = g.ν n * g'.ν n) ∧ (∀ g : Sim D, ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f
        n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧ (n : ℤ) ∣ g.ν n * g'.ν n - 1)) → (∀ (E
        : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂
        : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r
        : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x
        : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^
        (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A /
        l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA
        a).left) → ∀ g : Sim D, g.InGam l l₂ → ∃ ρ : Xo₂.X ≅ Xo₂.X, Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r) → ∀ (E
        : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂
        : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r
        : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x
        : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^
        (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A /
        l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ (c : Coeff l) (c₂ : Coeff l₂) (hc
        : c.F = c₂.F) (rF
        : Xo₂.XF c₂ ⟶ Xo.XF c), rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r → rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion
        hc.le).toRingHom → ∀ (k : Type) [Field k] [IsAlgClosed k] (y y'
        : Sp k ⟶ Xo₂.XF c₂), y ≫ rF = y' ≫ rF → (∃ (g : Sim D) (ρ
        : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ ∧ Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r ∧ y' ≫ pullback.fst _ _ = y ≫ pullback.fst _ _ ≫ ρ.hom) ∧ ∀ (g
        : Sim D) (ρ
        : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ → Xo₂.LevAut g ρ → y ≫ pullback.fst _ _ ≫ ρ.hom = y ≫ pullback.fst _ _ → g.TrivAt l₂ := by
  intro hL hPull _ hPol _ hRig _ hDiff _ hLev E _ _ _ H D l l₂ Xo Xo₂ hpq hd r jK m hm c c₂ hc rF hF₁ hF₂ k _ _ y y' hy
  have pull : ∀ (l : Level H) (Xo : Moduli D l) (k : Type) [Field k] (z : Sp k ⟶ Xo.X),
      ∃ o' : Obj D l (baseKA l) (z ≫ Xo.s), Nonempty (ObjMap o' Xo.univ z) := fun l Xo k _ z =>
    hPull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (z ≫ Xo.s) z rfl rfl
      (by rw [spMap_id', Category.comp_id]) Xo.univ
  constructor
  · have hr : (y ≫ pullback.fst _ _) ≫ r = (y' ≫ pullback.fst _ _) ≫ r := by
      rw [Category.assoc, Category.assoc, ← hF₁, ← Category.assoc, ← Category.assoc, hy]
    have hbij : Function.Bijective (IntermediateField.inclusion hc.le).toRingHom :=
      ⟨(IntermediateField.inclusion hc.le).toRingHom.injective, fun a => ⟨⟨a.1, hc.ge a.2⟩, rfl⟩⟩
    have : IsIso (CommRingCat.ofHom (IntermediateField.inclusion hc.le).toRingHom) :=
      (ConcreteCategory.isIso_iff_bijective _).2 hbij
    have hsnd : y ≫ pullback.snd _ _ = y' ≫ pullback.snd _ _ := by
      rw [← cancel_mono (spMap (IntermediateField.inclusion hc.le).toRingHom), Category.assoc, Category.assoc, ← hF₂,
        ← Category.assoc, ← Category.assoc, hy]
    have hs : (y ≫ pullback.fst _ _) ≫ Xo₂.s = (y' ≫ pullback.fst _ _) ≫ Xo₂.s := by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc, hsnd]
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hPol E H D l _ (baseKA l) _ Xo.s Xo.univ
    have := Xo.smooth
    have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
    have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
    let P : Out.PolAV Xo.X :=
      { A := Xo.univ.t.G, isAb := h₁, g := _, smoothDim := h₂, L := Xo.univ.t.PP.L, isLB := Xo.univ.t.PP.isLB,
        rigid := h₃, sym := h₄, ample := Xo.univ.ample, ktriv := Xo.univ.ktriv }
    obtain ⟨g, ρ, a₁, a₂, a₃, a₄⟩ := exists_sim_of_fibre_comm (pull l₂ Xo₂) (k := k)
      (fun z => hDiff E H D k _ _ _ fun n p q a b _ hp hq ha hb =>
        unitOn_injective (((hL.weil _ P n (Over.mk z)).1 p q hp hq).unique ha hb))
      hd r m hm.2.2.1 hm.2.2.2 (hLev E H D l l₂ Xo Xo₂ hpq hd r jK m hm) _ _ hr hs
    exact ⟨g, ρ, a₁, a₂, a₃, a₄.trans (Category.assoc _ _ _)⟩
  · intro g ρ hg hρ hx
    exact trivAt_of_fixed (pull l Xo) (fun k _ z o' => hRig E H D l _ _ _ _ _ _ _ _ Xo.univ o' z (Or.inl inferInstance))
      hd r m hm.2.2.1 _ g ρ hg hρ ((Category.assoc _ _ _).trans hx)

end GlobalTheory.LevelFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfCover
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem relAmple_of_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ∀ (L : LB A.left) (M : ∀ i, LB (G i).left), L.IsLB → (∀ i, (M i).IsLB) → (∀ i, LBIso (M i) (L.pull (ψ i))) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → (∀ i, Out.RelAmple (G i) (M i)) → Out.RelAmple A L := by
  intro S I U A _ G _ ψ hU hψ L M hL hM hiso hA _ hamp
  have : IsProper A.hom := hA.proper
  refine GlobalTheory.AmpleLocal.relAmple_of_locally S A L hL inferInstance inferInstance fun s => ?_
  obtain ⟨i, hi⟩ := exists_mem hU s
  obtain ⟨V, hV, hs, hle⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := U i) (x := s) hi
  have hle' : V ≤ U i := hle
  refine ⟨V, hs, ?_⟩
  have h := (hψ i).1
  have hf : S.homOfLE hle' ≫ (U i).ι = V.ι := S.homOfLE_ι hle'
  have sq : (A.hom ⁻¹ᵁ V).ι ≫ A.hom = ((A.hom ∣_ V) ≫ S.homOfLE hle') ≫ (U i).ι := by
    rw [Category.assoc, hf, morphismRestrict_ι]
  let φ : (A.hom ⁻¹ᵁ V).toScheme ⟶ (G i).left := h.lift _ _ sq
  have hφ : φ ≫ ψ i = (A.hom ⁻¹ᵁ V).ι := h.lift_fst _ _ _
  have H : IsPullback φ (A.hom ∣_ V) (G i).hom (S.homOfLE hle') := by
    refine IsPullback.of_right ?_ (h.lift_snd _ _ _) h
    rw [hφ, hf]
    exact (isPullback_morphismRestrict A.hom V).flip
  obtain ⟨w, hw⟩ : LBIso (L.pull (A.hom ⁻¹ᵁ V).ι) ((M i).pull φ) :=
    LBIso.chartPull (chartPullSame L (fun _ : PUnit => (A.hom ⁻¹ᵁ V).ι) (fun _ => ψ i) (fun _ => 1) φ fun _ => hφ.symm)
      (chartPullPull (M i) φ φ rfl) (hiso i).symm
  refine relAmple_pull (A' := Over.mk (A.hom ∣_ V)) H (hM i) (pull_isLB hL _) ((isGen_iff w).1 hw) ((U i).ι ⁻¹ᵁ V)
    (hV.preimage_of_isOpenImmersion _ (by simpa using hle')) (fun y => by
      have hy := congrArg (fun f : V.toScheme ⟶ S => f y) hf
      change ((S.homOfLE hle') y).val = y.val at hy
      change ((S.homOfLE hle') y).val ∈ V
      rw [hy]
      exact y.property) (hamp i)

end GlobalTheory.CoverGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_of_open_cover_grpPullback_relAmple : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ∀ (L : LB A.left) (M : ∀ i, LB (G i).left), L.IsLB → (∀ i, (M i).IsLB) → (∀ i, LBIso (M i) (L.pull (ψ i))) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → (∀ i, Out.RelAmple (G i) (M i)) → Out.RelAmple A L := by
  first | exact @GlobalTheory.CoverGlue.relAmple_of_cover | exact GlobalTheory.CoverGlue.relAmple_of_cover | (intros; apply GlobalTheory.CoverGlue.relAmple_of_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleOfFiniteQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleOfFiniteQuotient
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.QuotTriple

open GlobalTheory.CechPic

theorem isPullback_lift {X X' : Scheme.{0}} {π : X ⟶ X'} {P Q : Over X} {P' Q' : Over X'} {a : P.left ⟶ P'.left}
    {b : Q.left ⟶ Q'.left} (ha : IsPullback a P.hom P'.hom π) (hb : IsPullback b Q.hom Q'.hom π) :
    IsPullback (lift (pushPt ha.w (fst P Q)) (pushPt hb.w (snd P Q))).left (P ⊗ Q).hom (P' ⊗ Q').hom π := by
  have big : IsPullback ((snd P Q).left ≫ b) (fst P Q).left Q'.hom (P.hom ≫ π) :=
    (IsPullback.of_hasPullback P.hom Q.hom).flip.paste_horiz hb
  have e₁ : (lift (pushPt ha.w (fst P Q)) (pushPt hb.w (snd P Q))).left ≫ (fst P' Q').left = (fst P Q).left ≫ a :=
    congrArg (fun z => z.left) (lift_fst (pushPt ha.w (fst P Q)) (pushPt hb.w (snd P Q)))
  have e₂ : (lift (pushPt ha.w (fst P Q)) (pushPt hb.w (snd P Q))).left ≫ (snd P' Q').left = (snd P Q).left ≫ b :=
    congrArg (fun z => z.left) (lift_snd (pushPt ha.w (fst P Q)) (pushPt hb.w (snd P Q)))
  have h₁ : IsPullback (lift (pushPt ha.w (fst P Q)) (pushPt hb.w (snd P Q))).left (fst P Q).left
      (fst P' Q').left a := by
    refine IsPullback.of_right (h₁₂ := (snd P' Q').left) (v₁₃ := Q'.hom) (h₂₂ := P'.hom) ?_ e₁
      (IsPullback.of_hasPullback P'.hom Q'.hom).flip
    rw [e₂, ha.w]
    exact big
  exact h₁.paste_vert ha

section Cube

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem pull_cls_cube (h : IsGrpPullback G' G f φ) {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hc : pull φ (cls L hL) = cls L' hL') {T' : Over S'} {T : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ G'))
    (x : Fin n → (T ⟶ G)) (U : Over.mk (T'.hom ≫ f) ⟶ T) (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i) :
    pull U.left (cls (cubeLB G x L) (LB.isLB_linComb hL _ _)) = cls (cubeLB G' x' L') (LB.isLB_linComb hL' _ _) := by
  refine (congrArg (pull U.left) (cls_linComb hL _ _ _)).trans (Eq.trans ?_ (cls_linComb hL' _ _ _).symm)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← hc, ← pull_comp]
  exact congrArg (fun q => _ • pull q (cls L hL)) (psum_push h x' x U hx I.down).symm

theorem psum_one {T : Over S} {n : ℕ} (I : Finset (Fin n)) : psum G (fun _ => (1 : T ⟶ G)) I = 1 := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => rfl
  | cons k l ih => exact (congrArg ((1 : T ⟶ G) * ·) ih).trans (_root_.mul_one _)

theorem one_left : (1 : 𝟙_ (Over S) ⟶ G).left = eSec G := by
  rw [Hom.one_def]; simp [eSec]

theorem pull_cls_cube_origin {L : LB G.left} (hL : L.IsLB) (h0 : pull (eSec G) (cls L hL) = 0) {T : Over S} {n : ℕ}
    (x : Fin n → (T ⟶ G)) (o : 𝟙_ (Over S) ⟶ T) (ho : ∀ i, o ≫ x i = 1) :
    pull o.left (cls (cubeLB G x L) (LB.isLB_linComb hL _ _)) = 0 := by
  refine (congrArg (pull o.left) (cls_linComb hL _ _ _)).trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun I _ => ?_
  have e : o ≫ psum G x I.down = 1 :=
    (psum_hom (preHom o) x I.down).trans ((congrArg (fun z => psum G z I.down) (funext ho)).trans (psum_one _))
  rw [map_zsmul, ← pull_comp, ← Over.comp_left, e, one_left, h0, smul_zero]

end Cube

section Quot

variable {Γ : Type} [Group Γ] [Finite Γ] {X X' : Scheme.{0}} {ρ : Γ →* Aut X} {π : X ⟶ X'}

theorem eq_zero_of_pull (hq : IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens,
      Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)),
        ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom)
    {P : Over X} {P' : Over X'} {Φ : P.left ⟶ P'.left} (hΦ : IsPullback Φ P.hom P'.hom π) (hs' : Smooth P'.hom)
    (hs : Smooth P.hom) (hg : GeometricallyIntegral P.hom) (hr : IsReduced X) (hab : genericPoints X ⊆ abLocus P)
    (o : 𝟙_ (Over X) ⟶ P) (o' : 𝟙_ (Over X') ⟶ P') (ho : o.left ≫ Φ = π ≫ o'.left) (c : Pic P'.left)
    (h₀ : pull o'.left c = 0) (h₁ : pull Φ c = 0) : c = 0 := by
  obtain ⟨N, hN, rfl⟩ := cls_surj c
  exact (cls_eq_zero_iff hN).2 (exists_gen_of_quotient_of_rigid Γ X X' ρ π P P' Φ o.left o'.left N hq hΦ
    inferInstance (Over.w o) (Over.w o') ho
    (eq_one_of_appLE_section_eq_one X P o.left (Over.w o) hs hg ⟨hr, hab⟩) hN
    ((cls_eq_zero_iff (pull_isLB hN _)).1 h₀) ((cls_eq_zero_iff (pull_isLB hN _)).1 h₁))

theorem genericPoints_subset_image [Surjective π] : genericPoints X' ⊆ π '' genericPoints X := by
  intro y hy
  obtain ⟨x, rfl⟩ := π.surjective y
  let C : irreducibleComponents X := ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩
  have hs : (genericPoints.ofComponent C).1 ⤳ x :=
    (genericPoints.isGenericPoint_ofComponent C).specializes mem_irreducibleComponent
  exact ⟨_, (genericPoints.ofComponent C).2, eq_of_specializes_of_mem_genericPoints hy (hs.map π.continuous)⟩

end Quot

theorem exists_sab_of_quotient : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X') (t : SAB H X) (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (a' : OAct (𝓞 E) G') (φ : t.G.left ⟶ G'.left) (L' : LB G'.left), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (IsReduced X ∧ genericPoints X ⊆ abLocus t.G) → IsSemiAbelian G' → IsGrpPullback t.G G' π φ → (∀ x, (t.act.act x).left ≫ φ = φ ≫ (a'.act x).left) → L'.IsLB → LBIso t.PP.L (L'.pull φ) → ∃ (t' : SAB H X') (ν : SABMap t t' π) (e : t'.G ≅ G'), ν.φ ≫ e.hom.left = φ := by
  intro E _ _ _ H Γ _ _ X X' ρ π t G' _ _ a' φ L' hq ⟨hr, hab⟩ hG' gp hact hL' hiso
  obtain ⟨-, hsurj, -⟩ := quotient_isIntegral_surjective_orbits Γ X X' ρ π hq
  have hr' : IsReduced X' := ⟨fun V => isReduced_of_injective _ (hq.2.2 V).1⟩
  have hab' : genericPoints X' ⊆ abLocus G' := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := genericPoints_subset_image (π := π) hy
    exact (abLocus_pullback abLocusOne hG' gp.1 x).2 (hab hx)
  have he : eSec t.G ≫ φ = π ≫ eSec G' := (cubeMapOf gp).e_comm
  have hp : eSec G' ≫ G'.hom = 𝟙 X' := Over.w _
  have c₀ : pull (eSec t.G) (cls t.PP.L t.PP.isLB) = 0 :=
    (cls_eq_zero_iff (pull_isLB t.PP.isLB _)).2 ⟨_, t.PP.rigGen⟩
  have cl : cls t.PP.L t.PP.isLB = pull φ (cls L' hL') := (cls_eq_iff _ (pull_isLB hL' φ)).2 hiso
  obtain ⟨M, hM, cM⟩ := cls_surj (cls L' hL' - pull (G'.hom ≫ eSec G') (cls L' hL'))
  have m₀ : pull (eSec G') (cls M hM) = 0 := by
    have e : eSec G' ≫ G'.hom ≫ eSec G' = eSec G' :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ eSec G') hp).trans (Category.id_comp _))
    rw [cM, map_sub, ← pull_comp, e, sub_self]
  have m₁ : pull φ (cls M hM) = cls t.PP.L t.PP.isLB := by
    have e : φ ≫ G'.hom ≫ eSec G' = t.G.hom ≫ eSec t.G ≫ φ := by
      rw [he, ← Category.assoc, gp.1.w, Category.assoc]
    rw [cM, map_sub, ← pull_comp, e, pull_comp, pull_comp, ← cl, c₀, map_zero, sub_zero]
  obtain ⟨r, hrig⟩ := (cls_eq_zero_iff (pull_isLB hM (eSec G'))).1 m₀
  let PP : RigLB G' := ⟨M, r, hM, hrig⟩
  have a₁ := t.semi.smooth
  have := t.semi.geomConnected
  have b₁ := grpObj_geometricallyIntegral_of_smooth X t.G
  obtain ⟨a₂, b₂, c₂⟩ := smooth_geometricallyIntegral_abLocus_tensorObj X t.G t.G a₁ a₁ b₁ b₁
  have d₂ := (Set.subset_inter hab hab).trans c₂
  obtain ⟨a₃, b₃, c₃⟩ := smooth_geometricallyIntegral_abLocus_tensorObj X t.G _ a₁ a₂ b₁ b₂
  have d₃ := (Set.subset_inter hab d₂).trans c₃
  have a₁' := hG'.smooth
  have a₂' : Smooth (G' ⊗ G').hom := smooth_tensorObj_hom _ _
  have a₃' : Smooth (G' ⊗ G' ⊗ G').hom := smooth_tensorObj_hom _ _
  have p₂ := isPullback_lift gp.1 gp.1
  have p₃ := isPullback_lift gp.1 p₂
  have o₁ : (1 : 𝟙_ (Over X) ⟶ t.G).left ≫ φ = π ≫ (1 : 𝟙_ (Over X') ⟶ G').left := by
    rw [one_left, one_left]; exact he
  have pa : ∀ {T : Over X} (x : T ⟶ t.G) a, pushPt gp.1.w (x ≫ t.act.act a) = pushPt gp.1.w x ≫ a'.act a :=
    fun x a => Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  have ol : ∀ {P Q : Over X} {P' Q' : Over X'} {a : P.left ⟶ P'.left} {b : Q.left ⟶ Q'.left}
      (wa : a ≫ P'.hom = P.hom ≫ π) (wb : b ≫ Q'.hom = Q.hom ≫ π) (u : 𝟙_ _ ⟶ P) (v : 𝟙_ _ ⟶ Q) (u' : 𝟙_ _ ⟶ P')
      (v' : 𝟙_ _ ⟶ Q'), u.left ≫ a = π ≫ u'.left → v.left ≫ b = π ≫ v'.left →
      (lift u v).left ≫ (lift (pushPt wa (fst P Q)) (pushPt wb (snd P Q))).left = π ≫ (lift u' v').left := by
    intro P Q P' Q' a b wa wb u v u' v' hu hv
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst P' Q').left = (_ ≫ _) ≫ (fst P' Q').left
      rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, ← hu]
      show _ ≫ (fst P Q).left ≫ a = _
      rw [← Category.assoc, ← Over.comp_left, lift_fst]
    · show (_ ≫ _) ≫ (snd P' Q').left = (_ ≫ _) ≫ (snd P' Q').left
      rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd, ← hv]
      show _ ≫ (snd P Q).left ≫ b = _
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
  have o₂ := ol gp.1.w gp.1.w 1 1 1 1 o₁ o₁
  have o₃ := ol gp.1.w p₂.w 1 _ 1 _ o₁ o₂
  have aone : ∀ a, (1 : 𝟙_ (Over X') ⟶ G') ≫ a'.act a = 1 := fun a => by
    have := a'.hom a
    exact MonObj.one_comp _
  have hΘ : ∃ s : (Theta G' M).Gen, s.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).1 (eq_zero_of_pull hq p₃ a₃' a₃ b₃ hr d₃ _ _ o₃ _
      (pull_cls_cube_origin hM m₀ (x3 G') _ fun i => by fin_cases i <;> simp [x3])
      ((pull_cls_cube gp hM t.PP.isLB m₁ (x3 t.G) (x3 G') _ fun i => ?_).trans
        ((cls_eq_zero_iff _).2 ⟨_, t.cub.isGen⟩)))
    fin_cases i
    · simp [x3]
    · refine Eq.trans ?_ (congrArg (· ≫ fst G' G') (lift_snd _ _).symm |>.trans (Category.assoc _ _ _))
      refine Over.OverMorphism.ext ?_
      exact (Category.assoc _ _ _).trans ((congrArg (fun z => (snd t.G (t.G ⊗ t.G)).left ≫ z.left)
        (lift_fst (pushPt gp.1.w (fst t.G t.G)) (pushPt gp.1.w (snd t.G t.G)))).symm.trans (Category.assoc _ _ _).symm)
    · refine Eq.trans ?_ (congrArg (· ≫ snd G' G') (lift_snd _ _).symm |>.trans (Category.assoc _ _ _))
      refine Over.OverMorphism.ext ?_
      exact (Category.assoc _ _ _).trans ((congrArg (fun z => (snd t.G (t.G ⊗ t.G)).left ≫ z.left)
        (lift_snd (pushPt gp.1.w (fst t.G t.G)) (pushPt gp.1.w (snd t.G t.G)))).symm.trans (Category.assoc _ _ _).symm)
  have hsym : LBIso M (M.pull (GrpObj.inv (X := G')).left) := by
    have e₁ : φ ≫ (GrpObj.inv (X := G')).left = (GrpObj.inv (X := t.G)).left ≫ φ := by
      have e := congrArg (fun z => z.left) (map_inv (pushHom gp t.G) (𝟙 t.G))
      exact (congrArg (· ≫ (GrpObj.inv (X := G')).left) (Category.id_comp φ).symm).trans
        (e.symm.trans (congrArg (· ≫ φ) (Category.id_comp _)))
    have e₂ : (1 : 𝟙_ (Over X') ⟶ G') ≫ GrpObj.inv (X := G') = 1 := inv_one (G := 𝟙_ (Over X') ⟶ G')
    obtain ⟨-, w, hw, -⟩ := t.sym
    have e₃ : cls t.PP.L t.PP.isLB = pull (GrpObj.inv (X := t.G)).left (cls t.PP.L t.PP.isLB) :=
      (cls_eq_iff _ (pull_isLB t.PP.isLB _)).2 ⟨w, hw⟩
    refine (cls_eq_iff hM (pull_isLB hM _)).1 (sub_eq_zero.1 (eq_zero_of_pull hq gp.1 a₁' a₁ b₁ hr hab 1 1 o₁ _ ?_ ?_))
    · rw [map_sub, cls_pull hM, ← pull_comp, ← Over.comp_left, e₂, sub_self]
    · rw [map_sub, cls_pull hM, ← pull_comp, e₁, pull_comp, m₁, ← e₃, sub_self]
  have hadj : ∀ a, LBIso (cubeLB G' ![fst G' G' ≫ a'.act a, snd G' G'] M)
      (cubeLB G' ![fst G' G', snd G' G' ≫ a'.act (H.bar a)] M) := fun a => by
    refine (cls_eq_iff (LB.isLB_linComb hM _ _) (LB.isLB_linComb hM _ _)).1
      (sub_eq_zero.1 (eq_zero_of_pull hq p₂ a₂' a₂ b₂ hr d₂ _ _ o₂ _ ?_ ?_))
    · rw [map_sub, sub_eq_zero]
      exact (pull_cls_cube_origin hM m₀ _ _ fun i => by fin_cases i <;> simp [aone]).trans
        (pull_cls_cube_origin hM m₀ _ _ fun i => by fin_cases i <;> simp [aone]).symm
    · rw [map_sub, sub_eq_zero]
      refine (pull_cls_cube gp hM t.PP.isLB m₁ _ _ _ fun i => ?_).trans
        (((cls_eq_iff _ _).2 (t.adj a)).trans (pull_cls_cube gp hM t.PP.isLB m₁ _ _ _ fun i => ?_).symm)
      · fin_cases i
        · exact (pa _ a).trans (by simp)
        · simp
      · fin_cases i
        · simp
        · exact (pa _ _).trans (by simp)
  have hprim : LBIso M (cubeLB G' ![𝟙 G', a'.act H.w0] M) := by
    refine (cls_eq_iff hM (LB.isLB_linComb hM _ _)).1
      (sub_eq_zero.1 (eq_zero_of_pull hq gp.1 a₁' a₁ b₁ hr hab 1 1 o₁ _ ?_ ?_))
    · rw [map_sub, sub_eq_zero]
      exact (one_left (G := G') ▸ m₀).trans
        (pull_cls_cube_origin hM m₀ _ _ fun i => by fin_cases i <;> simp [aone]).symm
    · rw [map_sub, sub_eq_zero, m₁]
      refine ((cls_eq_iff _ (LB.isLB_linComb t.PP.isLB _ _)).2 t.prim).trans (Eq.trans
        (pull_cls_cube gp hM t.PP.isLB m₁ _ ![𝟙 G', a'.act H.w0] (pushPt gp.1.w (𝟙 t.G)) fun i => ?_).symm ?_)
      · fin_cases i
        · simp
        · exact (congrArg (pushPt gp.1.w) (Category.id_comp _).symm).trans (pa _ _)
      · exact congrArg (fun q => pull q _) (Category.id_comp φ)
  obtain ⟨k₁, k₂⟩ := CubeGen.cubical_and_symmetric X' G' PP hG' ⟨hr', hab'⟩
  obtain ⟨cub⟩ := k₁ hΘ
  let t' : SAB H X' := ⟨G', hG', a', PP, cub, k₂ hsym, hadj, hprim⟩
  obtain ⟨ν, hν⟩ := exists_sabMap_of_lbIso E H X' X t' t π φ ⟨hr, hab⟩ gp hact
    ((cls_eq_iff _ (pull_isLB hM φ)).1 m₁.symm)
  exact ⟨t', ν, Iso.refl _, (Category.comp_id _).trans hν⟩

end GlobalTheory.QuotTriple
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleOfFiniteQuotientStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
theorem _root_.GlobalTheory.T.exists_semiAbelianTriple_of_finiteQuotient : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X') (t : SAB H X) (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (a' : OAct (𝓞 E) G') (φ : t.G.left ⟶ G'.left) (L' : LB G'.left), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (IsReduced X ∧ genericPoints X ⊆ abLocus t.G) → IsSemiAbelian G' → IsGrpPullback t.G G' π φ → (∀ x, (t.act.act x).left ≫ φ = φ ≫ (a'.act x).left) → L'.IsLB → LBIso t.PP.L (L'.pull φ) → ∃ (t' : SAB H X') (ν : SABMap t t' π) (e : t'.G ≅ G'), ν.φ ≫ e.hom.left = φ := by
  first | exact @GlobalTheory.QuotTriple.exists_sab_of_quotient | exact GlobalTheory.QuotTriple.exists_sab_of_quotient | (intros; apply GlobalTheory.QuotTriple.exists_sab_of_quotient <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SurjectiveAppOfPullbackSnd
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.RigidLocal

open GlobalTheory.CechPic

private theorem surjective_app_of_eq_of_surjective_comp_injective {X S : Scheme.{0}} (f : X ⟶ S) {W V : S.Opens} (e : W = V)
    {R : CommRingCat} (g : Γ(X, f ⁻¹ᵁ W) ⟶ R)
    (h : Function.Surjective (f.app W ≫ g).hom) (hg : Function.Injective g.hom) :
    Function.Surjective (f.app V).hom := by
  subst e
  rw [CommRingCat.hom_comp, RingHom.coe_comp] at h
  exact h.of_comp_left hg

theorem surjective_app_of_pullback_snd {X S : Scheme.{0}} (f : X ⟶ S) (V : S.Opens)
    (h : Function.Surjective (pullback.snd f V.ι).appTop.hom) : Function.Surjective (f.app V).hom := by
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict f V, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp, RingHom.coe_comp] at h
  have hi : IsIso (pullbackRestrictIsoRestrict f V).hom.appTop :=
    inferInstanceAs (IsIso ((pullbackRestrictIsoRestrict f V).hom.app ⊤))
  have h2 : Function.Surjective (f ∣_ V).appTop.hom :=
    h.of_comp_left (ConcreteCategory.bijective_of_isIso (pullbackRestrictIsoRestrict f V).hom.appTop).1
  rw [morphismRestrict_appTop] at h2
  refine surjective_app_of_eq_of_surjective_comp_injective f V.ι_image_top _ h2 ?_
  exact (ConcreteCategory.bijective_of_isIso
    (X.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage f V ⊤)).op).hom).1

theorem eSec_comp {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] {φ : A.left ⟶ A'.left}
    (h : IsGrpPullback A A' (𝟙 S) φ) : eSec A ≫ φ = eSec A' :=
  (GlobalTheory.PolBaseChange.eSec_comm h).trans (Category.id_comp _)

theorem lbIso_of_local : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [GrpObj A'] (L : LB A.left) (L' : LB A'.left) (φ : A.left ⟶ A'.left), IsAbelianScheme A → L.IsLB → L'.IsLB → Out.Rigidified A L → Out.Rigidified A' L' → IsGrpPullback A A' (𝟙 S) φ → (∀ p : S, ∃ (V B : Scheme.{0}) (x : V ⟶ S) (q : B ⟶ V) (a : B ⟶ A.left), IsOpenImmersion x ∧ p ∈ Set.range x ∧ IsPullback a q A.hom x ∧ LBIso (L.pull a) (L'.pull (a ≫ φ))) → LBIso L (L'.pull φ) := by
  intro hG S A A' _ _ L L' φ hA hL hL' hR hR' hφ hloc
  have hM : (L'.pull φ).IsLB := LB.isLB_pull hL' φ
  have hN : (LB.div L (L'.pull φ)).IsLB := LB.isLB_div hL hM

  have key : ∀ {Y : Scheme.{0}} (g : Y ⟶ A.left),
      (∃ t : LB.Gen ((LB.div L (L'.pull φ)).pull g), t.IsGen) ↔
        GlobalTheory.CechPic.pull g (GlobalTheory.CechPic.cls L hL) = GlobalTheory.CechPic.pull g (GlobalTheory.CechPic.cls _ hM) := by
    intro Y g
    rw [← cls_eq_zero_iff (LB.isLB_pull hN g), cls_pull hN g (LB.isLB_pull hN g), cls_div hL hM hN,
      map_sub, sub_eq_zero]

  have hsec : ∃ t : LB.Gen ((LB.div L (L'.pull φ)).pull (eSec A)), t.IsGen := by
    rw [key]
    have h1 : GlobalTheory.CechPic.pull (eSec A) (GlobalTheory.CechPic.cls L hL) = 0 := by
      rw [← cls_pull hL (eSec A) (LB.isLB_pull hL _)]
      exact (cls_eq_zero_iff _).2 hR
    have h2 : GlobalTheory.CechPic.pull (eSec A') (GlobalTheory.CechPic.cls L' hL') = 0 := by
      rw [← cls_pull hL' (eSec A') (LB.isLB_pull hL' _)]
      exact (cls_eq_zero_iff _).2 hR'
    rw [h1, cls_pull hL' φ hM, ← pull_comp, eSec_comp hφ, h2]

  have hloc' : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      ∃ t : LB.Gen ((LB.div L (L'.pull φ)).pull (A.hom ⁻¹ᵁ U).ι), t.IsGen := by
    intro s
    obtain ⟨V, B, x, q, a, hx, hs, hpb, hiso⟩ := hloc s
    refine ⟨x.opensRange, hs, ?_⟩
    rw [key]
    have w : (A.hom ⁻¹ᵁ x.opensRange).ι ≫ A.hom = ((A.hom ∣_ x.opensRange) ≫ x.isoOpensRange.inv) ≫ x := by
      rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
    obtain ⟨e, he⟩ : ∃ e, e ≫ a = (A.hom ⁻¹ᵁ x.opensRange).ι := ⟨hpb.lift _ _ w, hpb.lift_fst _ _ w⟩
    have ha : GlobalTheory.CechPic.pull a (GlobalTheory.CechPic.cls L hL) = GlobalTheory.CechPic.pull a (GlobalTheory.CechPic.cls _ hM) := by
      have h := (cls_eq_iff (LB.isLB_pull hL a) (LB.isLB_pull hL' (a ≫ φ))).2 hiso
      rw [cls_pull hL a, cls_pull hL' (a ≫ φ), pull_comp] at h
      rw [h, cls_pull hL' φ hM]
    rw [← he, pull_comp, pull_comp, ha]
  have hσ : eSec A ≫ A.hom = 𝟙 S := by
    unfold eSec
    exact (Over.w _).trans rfl
  have hsurj : ∀ U : S.Opens, Function.Surjective (A.hom.app U).hom := fun U =>
    surjective_app_of_pullback_snd A.hom U (surj_snd hG hA (Over.mk U.ι))
  obtain ⟨t, ht⟩ := exists_gen_of_local_of_section A.left S A.hom (eSec A) _ hN hσ hsurj hloc' hsec
  exact (cls_eq_iff hL hM).1 (sub_eq_zero.1 ((cls_div hL hM hN).symm.trans ((cls_eq_zero_iff hN).2 ⟨t, ht⟩)))

end GlobalTheory.RigidLocal
end
end
