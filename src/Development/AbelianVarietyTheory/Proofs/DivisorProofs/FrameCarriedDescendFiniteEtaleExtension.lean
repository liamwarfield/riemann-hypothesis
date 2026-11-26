module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointActionPeriodValueFractionFiel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionGenericFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftObstructionPullbackNaturality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOpenPartProductMapIrreducibleFibres

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriedSectionOfFrameCarriedAlongLifts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientGermsZeroFiniteFreeBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientGermsZeroFiniteFreeBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FreeCoord

open GlobalTheory.BoxIndep TensorProduct

theorem eq_zero_of_germOf_max {B : CommRingCat.{0}} (a : B)
    (h : ∀ z : Spec B, z.asIdeal.IsMaximal → germOf (𝟙 (Spec B)) z a = 0) : a = 0 := by
  have : (Ideal.span {a}).annihilator = ⊤ := by
    by_contra hne
    obtain ⟨p, hp, hI⟩ := Ideal.exists_le_maximal _ hne
    let z : Spec B := ⟨p, hp.isPrime⟩
    have h1 : algebraMap B ((Spec.structureSheaf B).presheaf.stalk z) a = 0 := h z hp
    have := StructureSheaf.IsLocalization.to_stalk B z
    obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff z.asIdeal.primeCompl _ _).1 h1
    exact c.2 (hI (Submodule.mem_annihilator_span_singleton _ _ |>.2 hc))
  have h1 : (1 : B) ∈ (Ideal.span {a}).annihilator := this ▸ Submodule.mem_top
  exact (one_smul B _).symm.trans ((Submodule.mem_annihilator_span_singleton _ _).1 h1)

theorem gs_comp' {Z Y X : Scheme.{0}} (r : Z ⟶ Y) (F : Y ⟶ X) (z : Z) (U : X.Opens) (h : F (r z) ∈ U) (f : Γ(X, U)) :
    gs (r ≫ F) z U f = (r.stalkMap z).hom (gs F (r z) U f) := by
  rw [← gs_pull r F z U h, gs_stalkMap r z _ h, gs_pull (𝟙 _) F (r z) U h, Category.id_comp]

theorem germ_eq_zero : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁), (∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) → ∀ (X : Scheme.{0}) (f : X ⟶ Sp R) (U : X.Opens) (a : Fin d → Γ(X, U)) (x : X), x ∈ U → (∀ z : (pullback f (spMap ρ₁) : Scheme.{0}), (pullback.fst f (spMap ρ₁)) z = x → ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z U (a l) = 0) → ∀ l, gs (𝟙 X) x U (a l) = 0 := by
  intro R R₁ _ _ ρ₁ d b hb X f U a x hx h
  let _ : Algebra R R₁ := ρ₁.toAlgebra
  let A : CommRingCat.{0} := X.presheaf.stalk x
  let _ : Algebra R A := (germOf (B := CommRingCat.of R) f x).toAlgebra
  have hli : LinearIndependent R b := Fintype.linearIndependent_iff.2 fun c hc =>
    congrFun ((hb 0).unique (y₁ := c) (y₂ := 0) (by simp only [Algebra.smul_def] at hc; exact hc.symm) (by simp))
  have hsp : ⊤ ≤ Submodule.span R (Set.range b) := fun r _ => by
    obtain ⟨c, hc, -⟩ := hb r
    rw [hc]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ (c l) (Submodule.subset_span ⟨l, rfl⟩)
  let β := Module.Basis.mk hli hsp
  have : Module.Finite R R₁ := Module.Finite.of_basis β
  let B : CommRingCat.{0} := CommRingCat.of (A ⊗[R] R₁)
  let iA : A ⟶ B := CommRingCat.ofHom (algebraMap A (A ⊗[R] R₁))
  let iR : CommRingCat.of R₁ ⟶ B := CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := R₁)).toRingHom
  have w : (Spec.map iA ≫ X.fromSpecStalk x) ≫ f = Spec.map iR ≫ spMap ρ₁ := by
    rw [Category.assoc, fromSpecStalk_comp (B := CommRingCat.of R)]
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_comp _ _))
    ext r
    exact (IsScalarTower.algebraMap_apply R A (A ⊗[R] R₁) r).symm.trans
      ((Algebra.TensorProduct.includeRight (R := R) (A := A) (B := R₁)).commutes r).symm
  let r : Spec B ⟶ pullback f (spMap ρ₁) := pullback.lift _ _ w
  have r1 : r ≫ pullback.fst f (spMap ρ₁) = Spec.map iA ≫ X.fromSpecStalk x := pullback.lift_fst _ _ _
  have r2 : r ≫ pullback.snd f (spMap ρ₁) = Spec.map iR := pullback.lift_snd _ _ _
  have key : (∑ l, iR.hom (b l) * iA.hom (gs (𝟙 X) x U (a l)) : B) = 0 := by
    refine eq_zero_of_germOf_max _ fun z hz => ?_
    letI : z.asIdeal.IsMaximal := hz
    have hm : (z.asIdeal.comap (algebraMap A (A ⊗[R] R₁))).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) z.asIdeal
    have hc : Spec.map iA z = closedPoint A := PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hm)
    have hzx : pullback.fst f (spMap ρ₁) (r z) = x := by
      have : (r ≫ pullback.fst f (spMap ρ₁)) z = X.fromSpecStalk x (Spec.map iA z) := by rw [r1]; rfl
      rw [hc, Scheme.fromSpecStalk_closedPoint] at this
      exact this
    have e := congrArg (r.stalkMap z).hom (h (r z) hzx)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum] at e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, map_mul, ← gs_comp' r _ z ⊤ trivial, ← gs_comp' r _ z U (hzx ▸ hx), r1, r2,
      gs_fromSpecStalk x hx, ← germOf_apply, ← germOf_map, ← germOf_map, Category.id_comp, Category.id_comp]
  have hli' := (Algebra.TensorProduct.basis A β).linearIndependent
  refine Fintype.linearIndependent_iff.1 hli' (fun l => gs (𝟙 X) x U (a l)) ?_
  refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) key
  rw [Algebra.smul_def, _root_.mul_comm, Algebra.TensorProduct.basis_apply, Module.Basis.mk_apply]
  rfl

end GlobalTheory.Mum.FreeCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientGermsZeroFiniteFreeBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_germs_zero_finiteFree_baseChange : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁), (∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) → ∀ (X : Scheme.{0}) (f : X ⟶ Sp R) (U : X.Opens) (a : Fin d → Γ(X, U)) (x : X), x ∈ U → (∀ z : (pullback f (spMap ρ₁) : Scheme.{0}), (pullback.fst f (spMap ρ₁)) z = x → ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z U (a l) = 0) → ∀ l, gs (𝟙 X) x U (a l) = 0 := by
  first | exact @GlobalTheory.Mum.FreeCoord.germ_eq_zero | exact GlobalTheory.Mum.FreeCoord.germ_eq_zero | (intros; apply GlobalTheory.Mum.FreeCoord.germ_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriedSectionOfFrameCarriedAlongLifts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem gs_sub' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by simp only [gs_eq f y U h, map_sub]

theorem gs_comp_map {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (h : Y ⟶ X) (z : Z) (V : X.Opens) (hz : h (g z) ∈ V)
    (a : Γ(X, V)) : gs (g ≫ h) z V a = (g.stalkMap z).hom (gs h (g z) V a) := by
  rw [← gs_pull g h z V hz a, gs_eq_map_gs g z (h ⁻¹ᵁ V) hz, gs_pull (𝟙 Y) h (g z) V hz a, Category.id_comp]

theorem secCarriedOver_of_lift {X Z P : Scheme.{0}} (q : Z ⟶ X) (p₁ : Z ⟶ P) (L : LB X) (W O : X.Opens) (hOW : O ≤ W)
    (τ : ∀ k : L.ι, Γ(Z, q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k)ˣ) (d : ℕ) (B : Fin d → Γ(P, ⊤))
    (s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k))
    (hdec : ∀ (z : Z) (k : L.ι), q z ∈ O → q z ∈ L.U k →
      gs (𝟙 Z) z (q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs p₁ z ⊤ (B l) * gs q z (O ⊓ L.U k) (s l k))
    (huniq : ∀ (U : X.Opens) (a : Fin d → Γ(X, U)) (x : X), x ∈ U →
      (∀ z : Z, q z = x → ∑ l, gs p₁ z ⊤ (B l) * gs q z U (a l) = 0) → ∀ l, gs (𝟙 X) x U (a l) = 0)
    (φ : X ⟶ X) (w : LB.Iso L (L.pull φ)) (f' : Z ⟶ Z) (hf'q : f' ≫ q = q ≫ φ) (hf'p : f' ≫ p₁ = p₁)
    (hcar : FrameCarriedAlong L q (q ⁻¹ᵁ W) τ φ w f') (l : Fin d) : SecCarriedOver L O (s l) φ w := by
  have hpt : ∀ z, q (f' z) = φ (q z) := fun z => by
    rw [← Scheme.Hom.comp_apply, hf'q, Scheme.Hom.comp_apply]
  intro x j k hxO hφxO hxk hφxj
  let U' : X.Opens := O ⊓ L.U k ⊓ φ ⁻¹ᵁ (O ⊓ L.U j) ⊓ ((L.pull φ).U (fun _ => j) ⊓ L.U k)
  have h1 : U' ≤ φ ⁻¹ᵁ (O ⊓ L.U j) := fun _ h => h.1.2
  have h2 : U' ≤ (L.pull φ).U (fun _ => j) ⊓ L.U k := fun _ h => h.2
  have h3 : U' ≤ O ⊓ L.U k := fun _ h => h.1.1
  let a : Fin d → Γ(X, U') := fun l' =>
    (X.presheaf.map (homOfLE h1).op).hom ((φ.app (O ⊓ L.U j)).hom (s l' j)) -
      (X.presheaf.map (homOfLE h2).op).hom (w.s (fun _ => j, k)).val * (X.presheaf.map (homOfLE h3).op).hom (s l' k)
  have ha : ∀ {Y : Scheme.{0}} (g : Y ⟶ X) (y : Y) (hy : g y ∈ U') (l' : Fin d),
      gs g y U' (a l') = gs (g ≫ φ) y (O ⊓ L.U j) (s l' j) -
        (gm g y ((L.pull φ).U (fun _ => j) ⊓ L.U k) (w.s (fun _ => j, k))).val * gs g y (O ⊓ L.U k) (s l' k) := by
    intro Y g y hy l'
    have e1 : gs g y U' ((X.presheaf.map (homOfLE h1).op).hom ((φ.app (O ⊓ L.U j)).hom (s l' j))) =
        gs (g ≫ φ) y (O ⊓ L.U j) (s l' j) :=
      (gs_res g y h1 hy _).trans (gs_pull g φ y (O ⊓ L.U j) (h1 hy) _)
    have e2 : gs g y U' ((X.presheaf.map (homOfLE h2).op).hom (w.s (fun _ => j, k)).val) =
        (gm g y ((L.pull φ).U (fun _ => j) ⊓ L.U k) (w.s (fun _ => j, k))).val :=
      (gs_res g y h2 hy _).trans (gs_unit g y _ (h2 hy) _)
    have e3 : gs g y U' ((X.presheaf.map (homOfLE h3).op).hom (s l' k)) = gs g y (O ⊓ L.U k) (s l' k) :=
      gs_res g y h3 hy _
    rw [gs_sub' g y U' hy, gs_mul g y U' hy, e1, e2, e3]
  have hxU : x ∈ U' := ⟨⟨⟨hxO, hxk⟩, hφxO, hφxj⟩, mem_pull.2 hφxj, hxk⟩
  have key := huniq U' a x hxU (by
    intro z hz
    have hzU : q z ∈ U' := hz ▸ hxU
    have hzO : q z ∈ O := hz ▸ hxO
    have hzk : q z ∈ L.U k := hz ▸ hxk
    have hzW : z ∈ q ⁻¹ᵁ W := hOW hzO
    have hf'zO : q (f' z) ∈ O := by rw [hpt, hz]; exact hφxO
    have hf'zj : q (f' z) ∈ L.U j := by rw [hpt, hz]; exact hφxj
    have hmj : q (f' z) ∈ O ⊓ L.U j := ⟨hf'zO, hf'zj⟩
    have hmWj : f' z ∈ q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U j := ⟨hOW hf'zO, hf'zj⟩
    have hmWk : (𝟙 Z) z ∈ q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k := ⟨hzW, hzk⟩
    have hcz := hcar z j k hzW (hOW hf'zO) hzk hf'zj
    have S1 : ∑ l', gs p₁ z ⊤ (B l') * gs (q ≫ φ) z (O ⊓ L.U j) (s l' j) =
        (gm f' z (q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U j) (τ j)).val := by
      have e1 : ∀ l', gs p₁ z ⊤ (B l') = (f'.stalkMap z).hom (gs p₁ (f' z) ⊤ (B l')) := fun l' => by
        conv_lhs => rw [← hf'p]
        exact gs_comp_map f' p₁ z ⊤ trivial _
      have e2 : ∀ l', gs (q ≫ φ) z (O ⊓ L.U j) (s l' j) = (f'.stalkMap z).hom (gs q (f' z) (O ⊓ L.U j) (s l' j)) :=
        fun l' => by rw [← hf'q]; exact gs_comp_map f' q z _ hmj _
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [e1, e2, ← map_mul, ← map_sum]
      rw [← hdec (f' z) j hf'zO hf'zj, ← gs_eq_map_gs f' z _ hmWj, gs_unit f' z _ hmWj]
    have S3 := hdec z k hzO hzk
    rw [gs_unit (𝟙 Z) z _ hmWk] at S3
    have e4 : ∀ l', gs p₁ z ⊤ (B l') * gs q z U' (a l') =
        gs p₁ z ⊤ (B l') * gs (q ≫ φ) z (O ⊓ L.U j) (s l' j) -
          (gw w q z j k).val * (gs p₁ z ⊤ (B l') * gs q z (O ⊓ L.U k) (s l' k)) := fun l' => by
      rw [ha q z hzU l', gw]; ring
    rw [Finset.sum_congr rfl (fun l' _ => e4 l'), Finset.sum_sub_distrib, ← Finset.mul_sum, S1, ← S3, hcz,
      Units.val_mul, sub_self])
  have e := key l
  rw [ha (𝟙 X) x hxU l, Category.id_comp, sub_eq_zero] at e
  exact e

theorem secCarriedOver_of_frameCarriedAlong : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁), (∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) → ∀ (X : Scheme.{0}) (f : X ⟶ Sp R) (L : LB X) (W O : X.Opens), O ≤ W → ∀ (τ : ∀ k : L.ι, Γ((pullback f (spMap ρ₁)), (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k)ˣ) (s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k)), (∀ (z : (pullback f (spMap ρ₁) : Scheme.{0})) (k : L.ι), (pullback.fst f (spMap ρ₁)) z ∈ O → (pullback.fst f (spMap ρ₁)) z ∈ L.U k → gs (𝟙 (pullback f (spMap ρ₁))) z ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z (O ⊓ L.U k) (s l k)) → ∀ (φ : X ⟶ X) (w : LB.Iso L (L.pull φ)), φ ≫ f = f → (∀ f' : (pullback f (spMap ρ₁)) ⟶ (pullback f (spMap ρ₁)), f' ≫ (pullback.fst f (spMap ρ₁)) = (pullback.fst f (spMap ρ₁)) ≫ φ → f' ≫ (pullback.snd f (spMap ρ₁)) = (pullback.snd f (spMap ρ₁)) → FrameCarriedAlong L (pullback.fst f (spMap ρ₁)) ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W) τ φ w f') → ∀ l, SecCarriedOver L O (s l) φ w := by
  intro R R₁ _ _ ρ₁ d b hb X f L W O hOW τ s hdec φ w hφ hcar l
  have hcond : (pullback.fst f (spMap ρ₁) ≫ φ) ≫ f = pullback.snd f (spMap ρ₁) ≫ spMap ρ₁ := by
    rw [Category.assoc, hφ, pullback.condition]
  have hf'q : pullback.lift _ _ hcond ≫ pullback.fst f (spMap ρ₁) = pullback.fst f (spMap ρ₁) ≫ φ :=
    pullback.lift_fst _ _ _
  have hf'p : pullback.lift _ _ hcond ≫ pullback.snd f (spMap ρ₁) = pullback.snd f (spMap ρ₁) :=
    pullback.lift_snd _ _ _
  exact secCarriedOver_of_lift (pullback.fst f (spMap ρ₁)) (pullback.snd f (spMap ρ₁)) L W O hOW τ d
    (fun l => (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) s hdec
    (fun U a x hx hz => GlobalTheory.T.coefficient_germs_zero_finiteFree_baseChange R R₁ ρ₁ d b hb X f U a x hx hz) φ w _ hf'q hf'p (hcar _ hf'q hf'p) l

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriedSectionOfFrameCarriedAlongLiftsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carried_section_of_frame_carried_along_lifts : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁), (∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) → ∀ (X : Scheme.{0}) (f : X ⟶ Sp R) (L : LB X) (W O : X.Opens), O ≤ W → ∀ (τ : ∀ k : L.ι, Γ((pullback f (spMap ρ₁)), (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k)ˣ) (s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k)), (∀ (z : (pullback f (spMap ρ₁) : Scheme.{0})) (k : L.ι), (pullback.fst f (spMap ρ₁)) z ∈ O → (pullback.fst f (spMap ρ₁)) z ∈ L.U k → gs (𝟙 (pullback f (spMap ρ₁))) z ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z (O ⊓ L.U k) (s l k)) → ∀ (φ : X ⟶ X) (w : LB.Iso L (L.pull φ)), φ ≫ f = f → (∀ f' : (pullback f (spMap ρ₁)) ⟶ (pullback f (spMap ρ₁)), f' ≫ (pullback.fst f (spMap ρ₁)) = (pullback.fst f (spMap ρ₁)) ≫ φ → f' ≫ (pullback.snd f (spMap ρ₁)) = (pullback.snd f (spMap ρ₁)) → FrameCarriedAlong L (pullback.fst f (spMap ρ₁)) ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W) τ φ w f') → ∀ l, SecCarriedOver L O (s l) φ w := by
  first | exact @GlobalTheory.Mum.secCarriedOver_of_frameCarriedAlong | exact GlobalTheory.Mum.secCarriedOver_of_frameCarriedAlong | (intros; apply GlobalTheory.Mum.secCarriedOver_of_frameCarriedAlong <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameCoefficientUnitGermsFiniteFree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameCoefficientUnitGermsFiniteFree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_isUnit_gs_of_frame_eq_sum : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁) (X : Scheme.{0}) (f : X ⟶ Sp R) (L : LB X), L.IsLB → ∀ (W O : X.Opens), O ≤ W → ∀ (τ : ∀ k : L.ι, Γ((pullback f (spMap ρ₁)), (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k)ˣ) (s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k)), (∀ l, IsSecOver L O (s l)) → (∀ (z : (pullback f (spMap ρ₁) : Scheme.{0})) (k : L.ι), (pullback.fst f (spMap ρ₁)) z ∈ O → (pullback.fst f (spMap ρ₁)) z ∈ L.U k → gs (𝟙 (pullback f (spMap ρ₁))) z ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z (O ⊓ L.U k) (s l k)) → ∀ z : (pullback f (spMap ρ₁) : Scheme.{0}), (pullback.fst f (spMap ρ₁)) z ∈ O → ∃ l, ∀ k, (pullback.fst f (spMap ρ₁)) z ∈ L.U k → IsUnit (gs (𝟙 X) ((pullback.fst f (spMap ρ₁)) z) (O ⊓ L.U k) (s l k)) := by
  intro R R₁ _ _ ρ₁ d b X f L hL W O hOW τ s hs hτ z hz
  obtain ⟨k₀, hk₀⟩ := exists_chart hL ((pullback.fst f (spMap ρ₁)) z)
  have hm : (𝟙 (pullback f (spMap ρ₁) : Scheme.{0})) z ∈
      (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k₀ := ⟨hOW hz, hk₀⟩
  have hm' : (pullback.fst f (spMap ρ₁)) z ∈ O ⊓ L.U k₀ := ⟨hz, hk₀⟩
  have hu : IsUnit (gs (𝟙 (pullback f (spMap ρ₁))) z
      ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k₀) (τ k₀).val) := by
    rw [gs_unit _ z _ hm]
    exact Units.isUnit _
  rw [hτ z k₀ hz hk₀] at hu
  obtain ⟨l, -, hl⟩ := IsLocalRing.exists_of_isUnit_sum hu
  have hl2 := isUnit_of_mul_isUnit_right hl
  rw [gs_eq_map_gs _ z _ hm'] at hl2
  have hl3 := (isUnit_map_iff _ _).1 hl2
  refine ⟨l, fun k hk => ?_⟩
  rw [hs l _ k k₀ hz hk hk₀]
  exact (Units.isUnit _).mul hl3

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameCoefficientUnitGermsFiniteFreeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frameCoefficient_unitGerms_finiteFree : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁) (X : Scheme.{0}) (f : X ⟶ Sp R) (L : LB X), L.IsLB → ∀ (W O : X.Opens), O ≤ W → ∀ (τ : ∀ k : L.ι, Γ((pullback f (spMap ρ₁)), (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k)ˣ) (s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k)), (∀ l, IsSecOver L O (s l)) → (∀ (z : (pullback f (spMap ρ₁) : Scheme.{0})) (k : L.ι), (pullback.fst f (spMap ρ₁)) z ∈ O → (pullback.fst f (spMap ρ₁)) z ∈ L.U k → gs (𝟙 (pullback f (spMap ρ₁))) z ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z (O ⊓ L.U k) (s l k)) → ∀ z : (pullback f (spMap ρ₁) : Scheme.{0}), (pullback.fst f (spMap ρ₁)) z ∈ O → ∃ l, ∀ k, (pullback.fst f (spMap ρ₁)) z ∈ L.U k → IsUnit (gs (𝟙 X) ((pullback.fst f (spMap ρ₁)) z) (O ⊓ L.U k) (s l k)) := by
  first | exact @GlobalTheory.Mum.exists_isUnit_gs_of_frame_eq_sum | exact GlobalTheory.Mum.exists_isUnit_gs_of_frame_eq_sum | (intros; apply GlobalTheory.Mum.exists_isUnit_gs_of_frame_eq_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoefficientsDescendFiniteFreeAffineOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoefficientsDescendFiniteFreeAffineOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FrameCoeff

variable {R R₁ : Type} [CommRing R] [CommRing R₁]

theorem exists_basis (ρ₁ : R →+* R₁) {d : ℕ} (b : Fin d → R₁)
    (hb : ∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) :
    letI := ρ₁.toAlgebra; ∃ B : Module.Basis (Fin d) R R₁, ⇑B = b := by
  letI := ρ₁.toAlgebra
  have hs : ∀ (c : R) (x : R₁), c • x = ρ₁ c * x := fun c x => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  have hli : LinearIndependent R b := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    have h1 : (0 : R₁) = ∑ l, ρ₁ (g l) * b l := by
      rw [← hg]; simp only [hs]
    have h2 : (0 : R₁) = ∑ l, ρ₁ ((0 : Fin d → R) l) * b l := by simp
    exact congrFun ((hb 0).unique h1 h2) i
  refine ⟨Module.Basis.mk hli ?_, Module.Basis.coe_mk _ _⟩
  intro r _
  obtain ⟨c, hc, -⟩ := hb r
  rw [hc]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [← hs]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

theorem gs_zero0 {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

variable {X Z : Scheme.{0}}

theorem aff_coeff (ρ₁ : R →+* R₁) {d : ℕ} (b : Fin d → R₁)
    (hb : ∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l)
    {f : X ⟶ Sp R} {q : Z ⟶ X} {p : Z ⟶ Sp R₁} (H : IsPullback q p f (spMap ρ₁))
    {V : X.Opens} (hV : IsAffineOpen V) :
    (∀ t : Γ(Z, q ⁻¹ᵁ V), ∃ a : Fin d → Γ(X, V),
      t = ∑ l, GlobalTheory.AbLaw.cst p (q ⁻¹ᵁ V) (b l) * (q.app V).hom (a l)) ∧
    (∀ a : Fin d → Γ(X, V), ∑ l, GlobalTheory.AbLaw.cst p (q ⁻¹ᵁ V) (b l) * (q.app V).hom (a l) = 0 → a = 0) := by
  classical
  letI := ρ₁.toAlgebra
  obtain ⟨B, hB⟩ := exists_basis ρ₁ b hb
  have hg : ρ₁.Flat := by
    have : Module.Free R R₁ := Module.Free.of_basis B
    exact (inferInstance : Module.Flat R R₁)
  letI : Algebra R Γ(X, V) := (GlobalTheory.AbLaw.cst f V).toAlgebra
  obtain ⟨e, he⟩ := GlobalTheory.FlatSec.exists_equiv_of_isPushout (R := R) (q.app V) (GlobalTheory.AbLaw.cst p (q ⁻¹ᵁ V))
    (GlobalTheory.FlatSec.isPushout_app hg H hV.isCompact hV.isQuasiSeparated)
  have hsum : ∀ a : Fin d → Γ(X, V), e (∑ l, B l ⊗ₜ[R] a l) =
      ∑ l, GlobalTheory.AbLaw.cst p (q ⁻¹ᵁ V) (b l) * (q.app V).hom (a l) := by
    intro a; rw [map_sum]; simp only [he, hB]
  constructor
  · intro t
    refine ⟨fun l => TensorProduct.equivFinsuppOfBasisLeft B (e.symm t) l, ?_⟩
    rw [← hsum]
    have h := TensorProduct.equivFinsuppOfBasisLeft_symm_apply B (TensorProduct.equivFinsuppOfBasisLeft B (e.symm t))
    rw [LinearEquiv.symm_apply_apply, Finsupp.sum_fintype _ _ (by simp)] at h
    rw [← h, AddEquiv.apply_symm_apply]
  · intro a ha
    rw [← hsum] at ha
    have h0 : ∑ l, B l ⊗ₜ[R] a l = 0 := e.injective (ha.trans (map_zero e).symm)
    funext k
    have := congrArg (fun w => TensorProduct.equivFinsuppOfBasisLeft B w k) h0
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, Module.Basis.repr_self,
      Finsupp.single_apply] using this

end GlobalTheory.FrameCoeff

namespace GlobalTheory.FrameCoeff

variable {R R₁ : Type} [CommRing R] [CommRing R₁] {X Z : Scheme.{0}}

theorem gs_cst_top (p : Z ⟶ Sp R₁) (z : Z) (c : R₁) :
    gs (𝟙 Z) z ⊤ (GlobalTheory.AbLaw.cst p ⊤ c) = gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom c) := by
  have h1 := gs_res (𝟙 Z) z (le_top : (⊤ : Z.Opens) ≤ p ⁻¹ᵁ ⊤) trivial ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom c))
  have h2 := gs_pull (𝟙 Z) p z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom c)
  rw [Category.id_comp] at h2
  exact h1.trans h2

theorem gs_comb_pt {d : ℕ} (b : Fin d → R₁) (p : Z ⟶ Sp R₁) (q : Z ⟶ X) (V : X.Opens) (z : Z) (hz : q z ∈ V)
    (a : Fin d → Γ(X, V)) :
    gs (𝟙 Z) z (q ⁻¹ᵁ V) (∑ l, GlobalTheory.AbLaw.cst p (q ⁻¹ᵁ V) (b l) * (q.app V).hom (a l)) =
      ∑ l, gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs q z V (a l) := by
  rw [GlobalTheory.FlatSec.gs_comb p q V z hz b a]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [gs_cst_top]

theorem exists_aff (U : X.Opens) (x : X) (hx : x ∈ U) : ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ U := by
  obtain ⟨V, hV, hxV, hVU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx
  exact ⟨V, hV, hxV, hVU⟩

end GlobalTheory.FrameCoeff

namespace GlobalTheory.FrameCoeff

variable {R R₁ : Type} [CommRing R] [CommRing R₁] {X Z : Scheme.{0}}

theorem inj_gen (ρ₁ : R →+* R₁) {d : ℕ} (b : Fin d → R₁)
    (hb : ∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l)
    {f : X ⟶ Sp R} {q : Z ⟶ X} {p : Z ⟶ Sp R₁} (H : IsPullback q p f (spMap ρ₁))
    (U : X.Opens) (a : Fin d → Γ(X, U))
    (h : ∀ z : Z, q z ∈ U →
      ∑ l, gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs q z U (a l) = 0) :
    ∀ l, a l = 0 := by
  intro l
  apply fn_ext
  intro x hx
  obtain ⟨V, hV, hxV, hVU⟩ := exists_aff U x hx
  have h0 := (aff_coeff ρ₁ b hb H hV).2 (fun l => GlobalTheory.AbLaw.rs X hVU (a l)) (fn_ext fun z hz => by
    rw [gs_comb_pt b p q V z hz, gs_zero0]
    refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) (h z (hVU hz))
    rw [gs_res q z hVU hz])
  have e := congrFun h0 l
  have e2 := gs_res (𝟙 X) x hVU hxV (a l)
  simp only [Pi.zero_apply] at e
  rw [← e2]
  erw [e]
  rw [gs_zero0, gs_zero0]

theorem surj_gen (ρ₁ : R →+* R₁) {d : ℕ} (b : Fin d → R₁)
    (hb : ∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l)
    {f : X ⟶ Sp R} {q : Z ⟶ X} {p : Z ⟶ Sp R₁} (H : IsPullback q p f (spMap ρ₁))
    (U : X.Opens) (t : Γ(Z, q ⁻¹ᵁ U)) :
    ∃ a : Fin d → Γ(X, U), ∀ z : Z, q z ∈ U →
      gs (𝟙 Z) z (q ⁻¹ᵁ U) t =
        ∑ l, gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs q z U (a l) := by
  classical
  choose V hV hxV hVU using fun x : U => exists_aff U x.1 x.2
  have hle : ∀ x, q ⁻¹ᵁ V x ≤ q ⁻¹ᵁ U := fun x z hz => hVU x hz
  choose c hc using fun x : U => (aff_coeff ρ₁ b hb H (hV x)).1 (GlobalTheory.AbLaw.rs Z (hle x) t)
  have hcg : ∀ x z, q z ∈ V x → gs (𝟙 Z) z (q ⁻¹ᵁ U) t =
      ∑ l, gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs q z (V x) (c x l) := by
    intro x z hz
    rw [← gs_res (𝟙 Z) z (hle x) hz t, ← gs_comb_pt b p q (V x) z hz]
    exact congrArg _ (hc x)
  have hcomp : ∀ l x y, GlobalTheory.AbLaw.rs X (inf_le_left : V x ⊓ V y ≤ V x) (c x l) =
      GlobalTheory.AbLaw.rs X (inf_le_right : V x ⊓ V y ≤ V y) (c y l) := by
    intro l x y
    refine sub_eq_zero.1 (inj_gen ρ₁ b hb H (V x ⊓ V y)
      (fun l => GlobalTheory.AbLaw.rs X inf_le_left (c x l) - GlobalTheory.AbLaw.rs X inf_le_right (c y l)) (fun z hz => ?_) l)
    have e : ∀ l, gs q z (V x ⊓ V y) (GlobalTheory.AbLaw.rs X inf_le_left (c x l) - GlobalTheory.AbLaw.rs X inf_le_right (c y l)) =
        gs q z (V x) (c x l) - gs q z (V y) (c y l) := fun l => by
      rw [gs_eq q z _ hz, map_sub, map_sub, ← gs_eq q z _ hz, ← gs_eq q z _ hz, gs_res q z _ hz, gs_res q z _ hz]
    simp only [e, mul_sub, Finset.sum_sub_distrib]
    rw [← hcg x z hz.1, ← hcg y z hz.2, sub_self]
  have hcov : U ≤ iSup V := fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  choose s hs using fun l => X.sheaf.existsUnique_gluing' V U (fun x => homOfLE (hVU x)) hcov
    (fun x => c x l) (fun x y => hcomp l x y)
  refine ⟨s, fun z hz => ?_⟩
  rw [hcg ⟨q z, hz⟩ z (hxV ⟨q z, hz⟩)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← (hs l).1 ⟨q z, hz⟩]
  exact congrArg _ (gs_res q z (hVU ⟨q z, hz⟩) (hxV ⟨q z, hz⟩) (s l))

end GlobalTheory.FrameCoeff

namespace GlobalTheory.FrameCoeff

variable {R R₁ : Type} [CommRing R] [CommRing R₁] {X Z : Scheme.{0}}

theorem main_gen (ρ₁ : R →+* R₁) {d : ℕ} (b : Fin d → R₁)
    (hb : ∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l)
    {f : X ⟶ Sp R} {q : Z ⟶ X} {p : Z ⟶ Sp R₁} (H : IsPullback q p f (spMap ρ₁))
    (L : LB X) (W O : X.Opens) (hOW : O ≤ W)
    (τ : ∀ k : L.ι, Γ(Z, q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k)ˣ) (hτ : FrameAlong L q (q ⁻¹ᵁ W) τ) :
    ∃ s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k), (∀ l, IsSecOver L O (s l)) ∧
      ∀ (z : Z) (k : L.ι), q z ∈ O → q z ∈ L.U k →
        gs (𝟙 Z) z (q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k) (τ k).val =
          ∑ l, gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs q z (O ⊓ L.U k) (s l k) := by
  have hle : ∀ k, q ⁻¹ᵁ (O ⊓ L.U k) ≤ q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k := fun k z hz => ⟨hOW hz.1, hz.2⟩
  choose a ha using fun k => surj_gen ρ₁ b hb H (O ⊓ L.U k) (GlobalTheory.AbLaw.rs Z (hle k) (τ k).val)
  have hτg : ∀ k z, q z ∈ O ⊓ L.U k → gs (𝟙 Z) z (q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k) (τ k).val =
      ∑ l, gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs q z (O ⊓ L.U k) (a k l) := by
    intro k z hz
    rw [← gs_res (𝟙 Z) z (hle k) hz]
    exact ha k z hz
  refine ⟨fun l k => a k l, fun l => ?_, fun z k hO hk => hτg k z ⟨hO, hk⟩⟩
  intro x k k' hx hk hk'
  have hV : O ⊓ L.U k ≤ L.U k := inf_le_right
  have hW : O ⊓ L.U k' ≤ L.U k' := inf_le_right
  have h0 := inj_gen ρ₁ b hb H ((O ⊓ L.U k) ⊓ (O ⊓ L.U k'))
    (fun l => GlobalTheory.AbLaw.rs X inf_le_left (a k l) -
      GlobalTheory.AbLaw.rs X (inf_le_inf hV hW) (L.g k k').val * GlobalTheory.AbLaw.rs X inf_le_right (a k' l)) (fun z hz => ?_) l
  · have e := congrArg (gs (𝟙 X) x _) h0
    rw [GlobalTheory.FlatSec.gs_diff hV hW (a k l) (a k' l) (𝟙 X) x ⟨⟨hx, hk⟩, ⟨hx, hk'⟩⟩, gs_zero0] at e
    exact sub_eq_zero.1 e
  · have e1 : ∀ l, gs q z _ (GlobalTheory.AbLaw.rs X inf_le_left (a k l) -
        GlobalTheory.AbLaw.rs X (inf_le_inf hV hW) (L.g k k').val * GlobalTheory.AbLaw.rs X inf_le_right (a k' l)) =
        gs q z _ (a k l) - (gm q z (L.U k ⊓ L.U k') (L.g k k')).val * gs q z _ (a k' l) :=
      fun l => GlobalTheory.FlatSec.gs_diff hV hW _ _ q z hz
    simp only [e1, mul_sub, Finset.sum_sub_distrib]
    have hfr := congrArg Units.val (hτ z k k' (hOW hz.1.1) hz.1.2 hz.2.2)
    rw [Units.val_mul, ← gs_unit (𝟙 Z) z (q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k) ⟨hOW hz.1.1, hz.1.2⟩ (τ k),
      ← gs_unit (𝟙 Z) z (q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k') ⟨hOW hz.1.1, hz.2.2⟩ (τ k'),
      hτg k z hz.1, hτg k' z hz.2] at hfr
    rw [hfr, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun l _ => by ring

end GlobalTheory.FrameCoeff

theorem GlobalTheory.FrameCoeff.frame_coeff : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁), (∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) → ∀ (X : Scheme.{0}) (f : X ⟶ Sp R) (L : LB X), L.IsLB → ∀ (W O : X.Opens), O ≤ W → IsAffineOpen O → ∀ (τ : ∀ k : L.ι, Γ((pullback f (spMap ρ₁)), (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k)ˣ), FrameAlong L (pullback.fst f (spMap ρ₁)) ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W) τ → ∃ s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k), (∀ l, IsSecOver L O (s l)) ∧ ∀ (z : (pullback f (spMap ρ₁) : Scheme.{0})) (k : L.ι), (pullback.fst f (spMap ρ₁)) z ∈ O → (pullback.fst f (spMap ρ₁)) z ∈ L.U k → gs (𝟙 (pullback f (spMap ρ₁))) z ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z (O ⊓ L.U k) (s l k) := by
  intro R R₁ _ _ ρ₁ d b hb X f L hL W O hOW hO τ hτ
  exact GlobalTheory.FrameCoeff.main_gen ρ₁ b hb (IsPullback.of_hasPullback f (spMap ρ₁)) L W O hOW τ hτ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoefficientsDescendFiniteFreeAffineOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_coefficients_descend_finiteFree_affineOpen : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁), (∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) → ∀ (X : Scheme.{0}) (f : X ⟶ Sp R) (L : LB X), L.IsLB → ∀ (W O : X.Opens), O ≤ W → IsAffineOpen O → ∀ (τ : ∀ k : L.ι, Γ((pullback f (spMap ρ₁)), (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k)ˣ), FrameAlong L (pullback.fst f (spMap ρ₁)) ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W) τ → ∃ s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k), (∀ l, IsSecOver L O (s l)) ∧ ∀ (z : (pullback f (spMap ρ₁) : Scheme.{0})) (k : L.ι), (pullback.fst f (spMap ρ₁)) z ∈ O → (pullback.fst f (spMap ρ₁)) z ∈ L.U k → gs (𝟙 (pullback f (spMap ρ₁))) z ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z (O ⊓ L.U k) (s l k) := by
  first | exact @GlobalTheory.FrameCoeff.frame_coeff | exact GlobalTheory.FrameCoeff.frame_coeff | (intros; apply GlobalTheory.FrameCoeff.frame_coeff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisActsTransitivelyFibresFlatBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisActsTransitivelyFibresFlatBaseChange
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.GalFibre

theorem exists_act_apply_eq : ∀ (R R' : Type) [CommRing R] [CommRing R'] (ρ : R →+* R'), ρ.Finite → IsGal ρ →
    ∀ (Y X : Scheme.{0}) (p : Y ⟶ Sp R) (p' : X ⟶ Sp R') (β : X ⟶ Y), Flat p → IsPullback β p' p (spMap ρ) →
    ∀ (act : Gal ρ → (X ⟶ X)), (∀ σ, act σ ≫ p' = p' ≫ spMap (Gal.hom σ)) → (∀ σ, act σ ≫ β = β) →
    ∀ z₀ z : X, β z₀ = β z → ∃ σ : Gal ρ, act σ z₀ = z := by
  intro R R' _ _ ρ _ hG Y X p p' β hfl hpb act hact hactβ z₀ z hz
  have : Flat p := hfl
  let π : R →+* ρ.range := ρ.rangeRestrict
  have hπ : Function.Surjective π := ρ.rangeRestrict_surjective
  have hfac : spMap ρ = spMap (algebraMap ρ.range R') ≫ spMap π := by
    rw [← Spec.map_comp]; rfl
  have hsq : IsPullback (pullback.fst p (spMap π)) (pullback.snd p (spMap π)) p (spMap π) :=
    IsPullback.of_hasPullback _ _
  let p₀ : X ⟶ pullback p (spMap π) :=
    hsq.lift β (p' ≫ spMap (algebraMap ρ.range R')) (by rw [hpb.w, hfac, Category.assoc])
  have hp₀ : p₀ ≫ pullback.fst p (spMap π) = β := hsq.lift_fst _ _ _
  have hp₀' : p₀ ≫ pullback.snd p (spMap π) = p' ≫ spMap (algebraMap ρ.range R') := hsq.lift_snd _ _ _
  have outer : IsPullback (p₀ ≫ pullback.fst p (spMap π)) p' p (spMap (algebraMap ρ.range R') ≫ spMap π) := by
    rw [hp₀, ← hfac]; exact hpb
  have hpb₀ : IsPullback p₀ p' (Over.mk (pullback.snd p (spMap π))).hom (spMap (algebraMap ρ.range R')) :=
    IsPullback.of_right outer hp₀' hsq
  have hinj : Function.Injective (algebraMap ρ.range R') := Subtype.val_injective
  let toG : Gal (algebraMap ρ.range R') → Gal ρ := fun σ => ⟨σ.1, fun r => σ.2 (π r)⟩
  have hG₀ : IsGal (algebraMap ρ.range R') := by
    refine ⟨?_, fun x hx => ?_⟩
    · have : Finite (Gal ρ) := hG.1
      exact Finite.of_injective toG (fun a b h => Subtype.ext (show a.1 = b.1 from congrArg (fun s : Gal ρ => s.1) h))
    · have hx' : ∀ σ ∈ Gal ρ, σ x = x := fun σ hσ => by
        refine hx σ ?_
        rintro ⟨_, r, rfl⟩
        exact hσ r
      exact ⟨⟨x, hG.2 x hx'⟩, rfl⟩
  have hflat : Flat (Over.mk (pullback.snd p (spMap π))).hom := by
    change Flat (pullback.snd p (spMap π)); infer_instance
  have : IsClosedImmersion (spMap π) := IsClosedImmersion.spec_of_surjective _ hπ
  have hz₀ : p₀ z₀ = p₀ z := by
    apply (pullback.fst p (spMap π)).isClosedEmbedding.injective
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hp₀, hz]
  obtain ⟨σ', h, h₁, h₂, h₃⟩ := gal_transitive_on_fibres ρ.range R' hinj hG₀ (Over.mk (pullback.snd p (spMap π)))
    hflat X p₀ p' hpb₀ z₀ z hz₀
  refine ⟨toG σ', ?_⟩
  have he : act (toG σ') = h := by
    refine hpb.hom_ext ?_ ?_
    · rw [hactβ, ← hp₀, ← Category.assoc, h₁]
    · rw [hact, h₂]; rfl
  rw [he, h₃]

end GlobalTheory.Mum.GalFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisActsTransitivelyFibresFlatBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_acts_transitively_fibres_flat_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (ρ : R →+* R'), ρ.Finite → IsGal ρ → ∀ (Y X : Scheme.{0}) (p : Y ⟶ Sp R) (p' : X ⟶ Sp R') (β : X ⟶ Y), Flat p → IsPullback β p' p (spMap ρ) → ∀ (act : Gal ρ → (X ⟶ X)), (∀ σ, act σ ≫ p' = p' ≫ spMap (Gal.hom σ)) → (∀ σ, act σ ≫ β = β) → ∀ z₀ z : X, β z₀ = β z → ∃ σ : Gal ρ, act σ z₀ = z := by
  first | exact @GlobalTheory.Mum.GalFibre.exists_act_apply_eq | exact GlobalTheory.Mum.GalFibre.exists_act_apply_eq | (intros; apply GlobalTheory.Mum.GalFibre.exists_act_apply_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCarriedDescendFiniteEtaleExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum


set_option maxHeartbeats 1000000 in
theorem FrameCarried.descend_finiteEtale : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β) (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ₁ : R →+* R₁), FinExt ρ₁ → ρ₁.Etale → ∀ (V₀ : G.left.Opens) (y : G.left), y ∈ V₀ → ∀ τ : ∀ k : U'.LG.L.ι, Γ(pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀) ⊓ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ U'.LG.L.U k)ˣ, FrameAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ → (∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → ∀ f' : (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁) : Scheme.{0}) ⟶ pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), f' ≫ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ≫ a.act σ → f' ≫ (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) → FrameCarriedAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ _ (Classical.choose hP.lg) f') → ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact R₁ _ _ _ ρ₁ hF₁ hE₁ V₀ y hy τ hτ hτc
  have hL : U'.LG.L.IsLB := U'.LG.isLB
  haveI : IsNoetherianRing R := hB.1.1
  have hfl : ρ₁.Flat := (RingHom.Etale.iff_flat_and_formallyUnramified.1 hE₁).1
  obtain ⟨-, -, -, hqs, -, -, -, d, b, hb⟩ := GlobalTheory.finiteFlat_proper_baseChange_facts R R₁ ρ₁ hF₁.2.1 hF₁.2.2 hfl
    G'.left G'.left (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁)) (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁)) (𝟙 _) (𝟙 _)
    (G'.hom ≫ spMap ρ) (pullback.snd _ _) (pullback.fst _ _) (pullback.fst _ _) (IsPullback.of_hasPullback _ _)
    (IsPullback.id_vert _) inferInstance
  have hβf : IsFinite β :=
    MorphismProperty.of_isPullback (P := @IsFinite) hβ.1.flip ((IsFinite.SpecMap_iff _).2 hF.2.2)
  have hβc : IsClosedMap β.base := β.isClosedMap
  have hGfl : Flat G.hom := by haveI := hS.smooth; infer_instance
  obtain ⟨V₁, hV₁a, hyV₁, hV₁⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp G.left.isBasis_affineOpens) hy
  have hOa : IsAffineOpen (β ⁻¹ᵁ V₁) := IsAffineOpen.preimage hV₁a β
  have hOW : β ⁻¹ᵁ V₁ ≤ β ⁻¹ᵁ V₀ := fun x hx => hV₁ hx
  obtain ⟨s, hs, hdec⟩ := GlobalTheory.T.frame_coefficients_descend_finiteFree_affineOpen R R₁ ρ₁ d b hb G'.left (G'.hom ≫ spMap ρ) U'.LG.L hL (β ⁻¹ᵁ V₀) (β ⁻¹ᵁ V₁) hOW hOa τ hτ
  have hcar : ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre)
      (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'),
      bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U',
      PullOver hD h → ∀ l, SecCarriedOver U'.LG.L (β ⁻¹ᵁ V₁) (s l) _ (Classical.choose hP.lg) := by
    intro σ h bc hbc hP hPO
    refine GlobalTheory.T.carried_section_of_frame_carried_along_lifts R R₁ ρ₁ d b hb G'.left (G'.hom ≫ spMap ρ) U'.LG.L (β ⁻¹ᵁ V₀) (β ⁻¹ᵁ V₁) hOW τ s hdec _
      (Classical.choose hP.lg) ?_ ?_
    · rw [hbc, ← hβ.1.w, ← Category.assoc, hact]
    · intro f' h1 h2
      exact hτc σ h bc hbc hP hPO f' (h1.trans (by rw [hbc])) h2
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0
      obtain ⟨c, hc, -⟩ := hb 1
      simp at hc
    · exact h0
  have key : ∃ l, ∀ (z : G'.left) (k : U'.LG.L.ι), β z = y → z ∈ U'.LG.L.U k →
      IsUnit (gs (𝟙 G'.left) z (β ⁻¹ᵁ V₁ ⊓ U'.LG.L.U k) (s l k)) := by
    by_cases hne : ∃ z₀, β z₀ = y
    · obtain ⟨z₀, hz₀⟩ := hne
      obtain ⟨z', hz'⟩ := hqs z₀
      have hz'O : (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) z' ∈ β ⁻¹ᵁ V₁ := by
        show β ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)).base z') ∈ V₁
        rw [hz', hz₀]; exact hyV₁
      obtain ⟨l, hl⟩ := GlobalTheory.T.exists_frameCoefficient_unitGerms_finiteFree R R₁ ρ₁ d b G'.left (G'.hom ≫ spMap ρ) U'.LG.L hL (β ⁻¹ᵁ V₀) (β ⁻¹ᵁ V₁) hOW τ s hs
        hdec z' hz'O
      have hl' : ∀ k, z₀ ∈ U'.LG.L.U k → IsUnit (gs (𝟙 G'.left) z₀ (β ⁻¹ᵁ V₁ ⊓ U'.LG.L.U k) (s l k)) := by
        intro k hk
        have := hl k (by show (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)).base z' ∈ _; rw [hz']; exact hk)
        revert this
        show IsUnit (gs (𝟙 G'.left) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)).base z') _ _) → _
        rw [hz']; exact id
      refine ⟨l, fun z k hz hk => ?_⟩
      obtain ⟨σ, hσ⟩ := GlobalTheory.T.galois_acts_transitively_fibres_flat_baseChange R R' ρ hF.2.2 hG G.left G'.left G.hom G'.hom β hGfl hβ.1 a.act
        (fun σ => (a.cart σ).1.w) hact z₀ z (hz₀.trans hz.symm)
      obtain ⟨h, bc, hbc, hP, hPO⟩ := a.unif σ
      obtain ⟨k₀, hk₀⟩ := exists_chart hL z₀
      have hz₀O : z₀ ∈ β ⁻¹ᵁ V₁ := show β z₀ ∈ V₁ from hz₀ ▸ hyV₁
      have hφ : (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) z₀ = z := by rw [hbc]; exact hσ
      subst hφ
      have hzO : (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) z₀ ∈ β ⁻¹ᵁ V₁ :=
        show β _ ∈ V₁ from hz ▸ hyV₁
      have e := hcar σ h bc hbc hP hPO l z₀ k k₀ hz₀O hzO hk₀ hk
      have hu : IsUnit (gs (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) z₀ _ (s l k)) := by
        rw [e]; exact (Units.isUnit _).mul (hl' k₀ hk₀)
      rw [gs_eq_map_gs (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) z₀ (β ⁻¹ᵁ V₁ ⊓ U'.LG.L.U k) ⟨hzO, hk⟩] at hu
      exact (isUnit_map_iff _ _).1 hu
    · push_neg at hne
      exact ⟨⟨0, hd⟩, fun z k hz _ => absurd hz (hne z)⟩
  obtain ⟨l, hl⟩ := key
  obtain ⟨V, hyV, -, T, hT, hTc⟩ :=
    GlobalTheory.Mum.exists_frame_of_isUnit_on_fibre G'.left G.left β hβc U'.LG.L hL V₁ (s l) (hs l) y hyV₁ hl
  exact ⟨V, hyV, T, hT, fun σ h bc hbc hP hPO => hTc _ _ (hcar σ h bc hbc hP hPO l)⟩

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCarriedDescendFiniteEtaleExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameCarried_descend_finiteEtale_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β) (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ₁ : R →+* R₁), FinExt ρ₁ → ρ₁.Etale → ∀ (V₀ : G.left.Opens) (y : G.left), y ∈ V₀ → ∀ τ : ∀ k : U'.LG.L.ι, Γ(pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀) ⊓ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ U'.LG.L.U k)ˣ, FrameAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ → (∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → ∀ f' : (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁) : Scheme.{0}) ⟶ pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), f' ≫ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ≫ a.act σ → f' ≫ (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) → FrameCarriedAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ _ (Classical.choose hP.lg) f') → ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
  first | exact @GlobalTheory.Mum.FrameCarried.descend_finiteEtale | exact GlobalTheory.Mum.FrameCarried.descend_finiteEtale | (intros; apply GlobalTheory.Mum.FrameCarried.descend_finiteEtale <;> assumption)
end
