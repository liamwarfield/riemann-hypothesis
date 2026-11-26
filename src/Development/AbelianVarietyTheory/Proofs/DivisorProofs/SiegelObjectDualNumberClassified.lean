module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesPrincipalAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalSiegelObjectGlueArtinFibreProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectDeterminedOverArtinianPinch

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialSquareZeroExtensionPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialSquareZeroExtensionPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SqZeroPb

def liftHom {K : Type} [Field K] {V W₁ W₂ : Type} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V] [AddCommGroup W₁] [Module K W₁] [Module Kᵐᵒᵖ W₁] [IsCentralScalar K W₁]
    [AddCommGroup W₂] [Module K W₂] [Module Kᵐᵒᵖ W₂] [IsCentralScalar K W₂]
    (e : V ≃ₗ[K] W₁ × W₂) {T : Type} [CommRing T]
    (a : T →+* TrivSqZeroExt K W₁) (b : T →+* TrivSqZeroExt K W₂)
    (h : ∀ t, (a t).fst = (b t).fst) : T →+* TrivSqZeroExt K V where
  toFun t := TrivSqZeroExt.inl (a t).fst + TrivSqZeroExt.inr (e.symm ((a t).snd, (b t).snd))
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp
  map_mul' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp only [map_mul, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, add_zero, zero_add, smul_eq_mul, op_smul_eq_smul, smul_zero]
      rw [← map_smul, ← map_smul, ← map_add (f := _)]
      congr 1
      ext <;> simp [h]
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp
  map_add' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp only [map_add (f := _), TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_inr, zero_add]
      rw [show ((a x).snd + (a y).snd, (b x).snd + (b y).snd)
          = ((a x).snd, (b x).snd) + ((a y).snd, (b y).snd) from rfl, map_add]

end GlobalTheory.SqZeroPb

open GlobalTheory.SqZeroPb in
theorem GlobalTheory.SqZeroPb.isPullback_trivSqZeroExt : ∀ (K : Type) [Field K] (V W₁ W₂ : Type) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V] [AddCommGroup W₁] [Module K W₁] [Module Kᵐᵒᵖ W₁] [IsCentralScalar K W₁] [AddCommGroup W₂] [Module K W₂] [Module Kᵐᵒᵖ W₂] [IsCentralScalar K W₂] (p : V →ₗ[K] W₁) (q : V →ₗ[K] W₂), Function.Bijective (LinearMap.prod p q) → IsPullback (CommRingCat.ofHom (TrivSqZeroExt.map p).toRingHom) (CommRingCat.ofHom (TrivSqZeroExt.map q).toRingHom) (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₁).toRingHom) (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₂).toRingHom) := by
  intro K _ V W₁ W₂ _ _ _ _ _ _ _ _ _ _ _ _ p q hpq
  let e := LinearEquiv.ofBijective (LinearMap.prod p q) hpq
  have he : ∀ v, e v = (p v, q v) := fun v => rfl
  have hw : CommRingCat.ofHom (TrivSqZeroExt.map p).toRingHom ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₁).toRingHom =
      CommRingCat.ofHom (TrivSqZeroExt.map q).toRingHom ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₂).toRingHom := by
    ext x; simp
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun s => CommRingCat.ofHom (liftHom e s.fst.hom s.snd.hom ?_)) ?_ ?_ ?_)
  · intro t
    have := congrArg (fun φ => φ.hom t) s.condition
    simpa using this
  · intro s
    ext t : 2
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [liftHom]
    · simp [liftHom]
      exact congrArg Prod.fst (e.apply_symm_apply _)
  · intro s
    ext t : 2
    have hc := congrArg (fun φ => φ.hom t) s.condition
    simp at hc
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [liftHom, hc]
    · simp [liftHom]
      exact congrArg Prod.snd (e.apply_symm_apply _)
  · intro s m hm1 hm2
    ext t : 2
    have h1 := congrArg (fun φ => φ.hom t) hm1
    have h2 := congrArg (fun φ => φ.hom t) hm2
    simp at h1 h2
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [liftHom, ← h1]
    · simp [liftHom, ← h1, ← h2]
      rw [LinearEquiv.eq_symm_apply]
      rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialSquareZeroExtensionPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivial_square_zero_extension_pullback : ∀ (K : Type) [Field K] (V W₁ W₂ : Type) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V] [AddCommGroup W₁] [Module K W₁] [Module Kᵐᵒᵖ W₁] [IsCentralScalar K W₁] [AddCommGroup W₂] [Module K W₂] [Module Kᵐᵒᵖ W₂] [IsCentralScalar K W₂] (p : V →ₗ[K] W₁) (q : V →ₗ[K] W₂), Function.Bijective (LinearMap.prod p q) → IsPullback (CommRingCat.ofHom (TrivSqZeroExt.map p).toRingHom) (CommRingCat.ofHom (TrivSqZeroExt.map q).toRingHom) (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₁).toRingHom) (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₂).toRingHom) := by
  first | exact @GlobalTheory.SqZeroPb.isPullback_trivSqZeroExt | exact GlobalTheory.SqZeroPb.isPullback_trivSqZeroExt | (intros; apply GlobalTheory.SqZeroPb.isPullback_trivSqZeroExt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPointLiftsToDualNumbers
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectTangentShiftConstancyDirectionIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectTangentShiftConstancyDirectionIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegTanShift

theorem spMap_comp_spMap' {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (f : A →+* B) (g : A' →+* A) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := Spec.map_id _

theorem isLocalRing_sq (K : Type) [Field K] : IsLocalRing (TrivSqZeroExt K (K × K)) :=
  haveI : Nontrivial (TrivSqZeroExt K (K × K)) := TrivSqZeroExt.inl_injective.nontrivial
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact IsLocalRing.isUnit_or_isUnit_one_sub_self _

theorem isArtinianRing_sq (K : Type) [Field K] : IsArtinianRing (TrivSqZeroExt K (K × K)) := by
  haveI : Module.Finite K (TrivSqZeroExt K (K × K)) := inferInstanceAs (Module.Finite K (K × (K × K)))
  exact IsArtinianRing.of_finite K _

theorem pbEq {h k : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S S' : Scheme.{0}}
    {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {c' : SiegPre h k ζ' s'} {c : SiegPre h k ζ s} {f f' : S' ⟶ S}
    (hc : SiegPB c' c f) (e : f = f') : SiegPB c' c f' := e ▸ hc

theorem shift : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (K : Type) [Field K] (r : ℕ) (β : cycAway n →+* K) (G : SiegPre g n (zetaAway n) (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β))), G.Principal → ∀ (lam κ κ' : (Fin r → K) →ₗ[K] K) (t : K) (c₃ c₁ : SiegPre g n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β))), κ = κ' + t • lam → SiegPB c₃ G (spMap (dirMap lam)) → SiegPB c₃ G (constPt (spMap (dirMap lam))) → SiegPB c₁ G (spMap (dirMap κ)) → SiegPB c₁ G (spMap (dirMap κ')) := by
  intro g n h3 hodd K _ r β G hG lam κ κ' t c₃ c₁ hκ h₁ h₂ h₃
  subst hκ
  have pull : ∀ {S S' : Scheme.{0}} (s : S ⟶ Sp (cycAway n)) (s' : S' ⟶ Sp (cycAway n)) (f : S' ⟶ S), f ≫ s = s' →
      ∀ c : SiegPre g n (zetaAway n) s, c.Principal →
        ∃ c' : SiegPre g n (zetaAway n) s', SiegPB c' c f ∧ c'.Principal := by
    intro S S' s s' f hf c hc
    have hf' : f ≫ s = s' ≫ spMap (RingHom.id (cycAway n)) := by rw [spMap_id', Category.comp_id]; exact hf
    have pr := GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n)
      (RingHom.id _) S S' s s' f rfl hf'
    obtain ⟨c', hcc⟩ := pr.1 c
    exact ⟨c', hcc, pr.2.1 c c' hcc hc⟩
  have base : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra K R] [Algebra K R'] (f : R →ₐ[K] R'),
      spMap f.toRingHom ≫ spMap ((algebraMap K R).comp β) = spMap ((algebraMap K R').comp β) := by
    intro R R' _ _ _ _ f
    rw [spMap_comp_spMap', ← RingHom.comp_assoc]
    congr 2
    ext x
    simp
  let Φ := TrivSqZeroExt.map (LinearMap.prod κ' (t • lam))
  let p₁ := TrivSqZeroExt.map (LinearMap.fst K K K)
  let p₂ := TrivSqZeroExt.map (LinearMap.snd K K K)
  let ι₁ := TrivSqZeroExt.map (LinearMap.inl K K K)
  let sm := TrivSqZeroExt.map (LinearMap.fst K K K + LinearMap.snd K K K)
  let mt := TrivSqZeroExt.map (t • LinearMap.id : K →ₗ[K] K)
  let cst : TrivSqZeroExt K (Fin r → K) →+* DualNumber K :=
    (algebraMap K (DualNumber K)).comp (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom
  let cD : DualNumber K →+* DualNumber K := (algebraMap K (DualNumber K)).comp (TrivSqZeroExt.fstHom K K K).toRingHom
  have e1 : p₁.toRingHom.comp Φ.toRingHom = dirMap κ' := by
    ext x <;> simp [p₁, Φ, dirMap]
  have e2 : p₂.toRingHom.comp Φ.toRingHom = dirMap (t • lam) := by
    ext x <;> simp [p₂, Φ, dirMap]
  have e3 : mt.toRingHom.comp (dirMap lam) = dirMap (t • lam) := by
    ext x <;> simp [mt, dirMap]
  have e4 : mt.toRingHom.comp cst = cst := by
    ext x <;> simp [mt, cst]
  have e6 : p₁.toRingHom.comp ι₁.toRingHom = RingHom.id _ := by
    ext x <;> simp [p₁, ι₁]
  have e7 : p₂.toRingHom.comp ι₁.toRingHom = cD := by
    ext x <;> simp [p₂, ι₁, cD]
  have e8 : sm.toRingHom.comp Φ.toRingHom = dirMap (κ' + t • lam) := by
    ext x <;> simp [sm, Φ, dirMap]
  have e9 : sm.toRingHom.comp ι₁.toRingHom = RingHom.id _ := by
    ext x <;> simp [sm, ι₁]
  have e10 : cD.comp (dirMap κ') = cst := by
    ext x <;> simp [cD, cst, dirMap]
  have hconst : constPt (spMap (dirMap lam)) = spMap cst := by
    simp only [constPt, spMap_comp_spMap']
    congr 1
  obtain ⟨c', hc', hc'p⟩ := pull _ _ (spMap (dirMap κ')) (base (TrivSqZeroExt.map κ')) G hG
  obtain ⟨H, hH, hHp⟩ := pull _ _ (spMap Φ.toRingHom) (base Φ) G hG
  obtain ⟨H'', hH'', hH''p⟩ := pull _ _ (spMap ι₁.toRingHom) (base ι₁) c' hc'p
  obtain ⟨C1, hC1, -⟩ := pull _ (spMap p₁.toRingHom ≫ spMap ((algebraMap K (TrivSqZeroExt K (K × K))).comp β))
    (spMap p₁.toRingHom) rfl H hHp
  obtain ⟨C2, hC2, -⟩ := pull _ (spMap p₂.toRingHom ≫ spMap ((algebraMap K (TrivSqZeroExt K (K × K))).comp β))
    (spMap p₂.toRingHom) rfl H hHp
  have hC1G : SiegPB C1 G (spMap (dirMap κ')) :=
    pbEq (GlobalTheory.SiegelPullComp.pb_comp hH hC1) (by rw [spMap_comp_spMap', e1])
  have hC1c' : SiegPB C1 c' (𝟙 _) := GlobalTheory.SiegelPullComp.pb_cancel hc' (pbEq hC1G (by rw [Category.id_comp]))
  have hC1H'' : SiegPB C1 H'' (spMap p₁.toRingHom) :=
    GlobalTheory.SiegelPullComp.pb_cancel hH'' (pbEq hC1c' (by rw [spMap_comp_spMap', e6, spMap_id']))
  have hC2G : SiegPB C2 G (spMap (dirMap (t • lam))) :=
    pbEq (GlobalTheory.SiegelPullComp.pb_comp hH hC2) (by rw [spMap_comp_spMap', e2])
  have h₂' : SiegPB c₃ G (spMap cst) := pbEq h₂ hconst
  have hC2m : SiegPB C2 c₃ (spMap mt.toRingHom) :=
    GlobalTheory.SiegelPullComp.pb_cancel h₁ (pbEq hC2G (by rw [spMap_comp_spMap', e3]))
  have hC2Gc : SiegPB C2 G (spMap cst) :=
    pbEq (GlobalTheory.SiegelPullComp.pb_comp h₂' hC2m) (by rw [spMap_comp_spMap', e4])
  have hC2c₃ : SiegPB C2 c₃ (𝟙 _) := GlobalTheory.SiegelPullComp.pb_cancel h₂' (pbEq hC2Gc (by rw [Category.id_comp]))
  have hc₃c' : SiegPB c₃ c' (spMap cD) :=
    GlobalTheory.SiegelPullComp.pb_cancel hc' (pbEq h₂' (by rw [spMap_comp_spMap', e10]))
  have hC2c' : SiegPB C2 c' (spMap cD) := pbEq (GlobalTheory.SiegelPullComp.pb_comp hc₃c' hC2c₃) (by rw [Category.id_comp])
  have hC2H'' : SiegPB C2 H'' (spMap p₂.toRingHom) :=
    GlobalTheory.SiegelPullComp.pb_cancel hH'' (pbEq hC2c' (by rw [spMap_comp_spMap', e7]))
  have hpb := GlobalTheory.T.trivial_square_zero_extension_pullback K (K × K) K K (LinearMap.fst K K K) (LinearMap.snd K K K)
    ⟨fun a b hab => by simpa using hab, fun y => ⟨y, by simp⟩⟩
  have hsurj : Function.Surjective (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) :=
    fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  have hHH : SiegPB H'' H (𝟙 _) :=
    GlobalTheory.T.principalSiegelObject_determined_over_artinianPinch g n h3 hodd (CommRingCat.of (TrivSqZeroExt K (K × K))) (CommRingCat.of (DualNumber K))
      (CommRingCat.of (DualNumber K)) (CommRingCat.of K) _ _ _ _ hpb (isLocalRing_sq K) (isArtinianRing_sq K)
      hsurj hsurj (CommRingCat.ofHom ((algebraMap K (TrivSqZeroExt K (K × K))).comp β)) H H'' C1 C2 hHp hH''p
      hC1 hC1H'' hC2 hC2H''
  have hc₁H : SiegPB c₁ H (spMap sm.toRingHom) :=
    GlobalTheory.SiegelPullComp.pb_cancel hH (pbEq h₃ (by rw [spMap_comp_spMap', e8]))
  have hc₁H'' : SiegPB c₁ H'' (spMap sm.toRingHom) :=
    GlobalTheory.SiegelPullComp.pb_cancel hHH (pbEq hc₁H (by rw [Category.comp_id]))
  have hc₁c' : SiegPB c₁ c' (𝟙 _) :=
    pbEq (GlobalTheory.SiegelPullComp.pb_comp hH'' hc₁H'') (by rw [spMap_comp_spMap', e9, spMap_id'])
  exact pbEq (GlobalTheory.SiegelPullComp.pb_comp hc' hc₁c') (by rw [Category.id_comp])

end GlobalTheory.SiegTanShift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectTangentShiftConstancyDirectionIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelObject_tangentShift_constancy_direction_iso : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (K : Type) [Field K] (r : ℕ) (β : cycAway n →+* K) (G : SiegPre g n (zetaAway n) (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β))), G.Principal → ∀ (lam κ κ' : (Fin r → K) →ₗ[K] K) (t : K) (c₃ c₁ : SiegPre g n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β))), κ = κ' + t • lam → SiegPB c₃ G (spMap (dirMap lam)) → SiegPB c₃ G (constPt (spMap (dirMap lam))) → SiegPB c₁ G (spMap (dirMap κ)) → SiegPB c₁ G (spMap (dirMap κ')) := by
  first | exact @GlobalTheory.SiegTanShift.shift | exact GlobalTheory.SiegTanShift.shift | (intros; apply GlobalTheory.SiegTanShift.shift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyTangentBoundNonconstant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyTangentBoundNonconstant
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.SiegelTangentBound

def acts (W : Matrix (Fin 8) (Fin 8) ℤ) : (Fin 8 × Fin 8) ⊕ Bool → Matrix (Fin 8) (Fin 8) ℤ
  | .inl uv => Matrix.single uv.1 uv.2 1
  | .inr true => (W + W.transpose).adjugate * W
  | .inr false => (W + W.transpose).adjugate * W.transpose

theorem main : ∀ (h n : ℕ), 1 ≤ h → 3 ≤ n → Odd n → ∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (β : cycAway n →+* K) (c : SiegPre h n (zetaAway n) (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β))), c.Principal → (∀ (lam : (Fin r → K) →ₗ[K] K) (c' : SiegPre h n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β))), SiegPB c' c (spMap (dirMap lam)) → SiegPB c' c (constPt (spMap (dirMap lam))) → lam = 0) → r ≤ h * (h + 1) / 2 := by
  intro h n _ h3 hodd K _ _ r β c hc hun
  have hn : n ≠ 0 := by omega
  obtain ⟨L1, L2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨W, hW, hbasAll⟩ := GlobalTheory.ZM.exists_isE8_isSharpBasis
  obtain ⟨bas, hbas⟩ := hbasAll h
  have hζ : (cycBase hn).ζ ^ n = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, cycBase_ζ]
    exact Subtype.ext (Complex.isPrimitiveRoot_exp n hn).pow_eq_one)
  have hdet : (W + W.transpose).det = 1 := hW.2
  have hw : (W + W.transpose) * acts W (.inr true) = W := by
    simp only [acts]; rw [← Matrix.mul_assoc, Matrix.mul_adjugate, hdet, one_smul, Matrix.one_mul]
  have hw' : (W + W.transpose) * acts W (.inr false) = W.transpose := by
    simp only [acts]; rw [← Matrix.mul_assoc, Matrix.mul_adjugate, hdet, one_smul, Matrix.one_mul]
  have he : ∀ u v : Fin 8, ∃ j, acts W j = Matrix.single u v 1 := fun u v => ⟨.inl (u, v), rfl⟩
  obtain ⟨t, ht⟩ := GlobalTheory.SiegelPower.exists_tObj_isSharp L1 L2 h (8 * h) W _ (acts W) bas hW hbas n (cycAway n)
    (cycBase hn) _ _ c hodd h3 hζ hc
  refine GlobalTheory.PowerTangent.main L1 L2 GlobalTheory.Moduli.cube_of_isLB h (8 * h) W _ (acts W) bas hW hbas (.inr true) (.inr false)
    hw hw' n (cycAway n) (cycBase hn) K r β t c hc ht ?_
  intro lam t' m₁ m₂
  have hf : spMap (dirMap lam) ≫ spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) =
      spMap ((algebraMap K (DualNumber K)).comp β) ≫ spMap (RingHom.id (cycAway n)) := by
    rw [← spMap_comp, ← spMap_comp]
    exact congrArg spMap (RingHom.ext fun z => by
      simp [dirMap, TrivSqZeroExt.algebraMap_eq_inl])
  obtain ⟨c', hc'⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h n _ _ (zetaAway n) (zetaAway n) (RingHom.id _) _ _ _ _
    (spMap (dirMap lam)) rfl hf).1 c
  have hc'P := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h n _ _ (zetaAway n) (zetaAway n) (RingHom.id _) _ _ _ _
    (spMap (dirMap lam)) rfl hf).2.1 c c' hc' hc
  obtain ⟨t'', ht''⟩ := GlobalTheory.SiegelPower.exists_tObj_isSharp L1 L2 h (8 * h) W _ (acts W) bas hW hbas n (cycAway n)
    (cycBase hn) _ _ c' hodd h3 hζ hc'P
  have m₃ : TMap t'' t (spMap (dirMap lam)) :=
    (GlobalTheory.PowerPullback.main L1 L2 h (8 * h) W _ (acts W) bas hW hbas n _ (cycBase hn) _ _ _ _ c c' t t''
      (spMap (dirMap lam)) hc hc'P ht ht'').1 hc'
  have m₄ : TMap t'' t' (𝟙 _) :=
    ((GlobalTheory.ZM.tmap_id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ t t' t'').2 _ (𝟙 _) m₁).2 (by rwa [Category.id_comp])
  have m₅ : TMap t'' t (constPt (spMap (dirMap lam))) := by
    have := ((GlobalTheory.ZM.tmap_id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ t t' t'').2 _ (𝟙 _) m₂).1 m₄
    rwa [Category.id_comp] at this
  exact hun lam c' hc' ((GlobalTheory.PowerPullback.main L1 L2 h (8 * h) W _ (acts W) bas hW hbas n _ (cycBase hn) _ _ _ _ c c' t t''
    _ hc hc'P ht ht'').2 he m₅)

end GlobalTheory.SiegelTangentBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyTangentBoundNonconstantStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelFamily_tangentBound_nonconstant : ∀ (h n : ℕ), 1 ≤ h → 3 ≤ n → Odd n → ∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (β : cycAway n →+* K) (c : SiegPre h n (zetaAway n) (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β))), c.Principal → (∀ (lam : (Fin r → K) →ₗ[K] K) (c' : SiegPre h n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β))), SiegPB c' c (spMap (dirMap lam)) → SiegPB c' c (constPt (spMap (dirMap lam))) → lam = 0) → r ≤ h * (h + 1) / 2 := by
  first | exact @GlobalTheory.SiegelTangentBound.main | exact GlobalTheory.SiegelTangentBound.main | (intros; apply GlobalTheory.SiegelTangentBound.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFirstOrderTangentPointSmooth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFirstOrderTangentPointSmooth
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor GlobalTheory.TangentOrigin
open scoped CategoryTheory.Obj

namespace GlobalTheory.TanPt

theorem exists_coords_derivs' {k A : Type} [CommRing k] [CommRing A] {α : k →+* A} {D : ℕ}
    (h : α.IsStandardSmoothOfRelativeDimension D) :
    ∃ (x : Fin D → A) (d : Fin D → A →+ A),
      (∀ c a b, d c (a * b) = a * d c b + b * d c a) ∧
      (∀ a c, d c (x a) = if a = c then 1 else 0) ∧ ∀ c r, d c (α r) = 0 := by
  classical
  letI := α.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension D k A := h
  obtain ⟨ιv, σv, _, _, P, hP⟩ := ‹Algebra.IsStandardSmoothOfRelativeDimension D k A›.out
  letI := Fintype.ofFinite ιv
  letI := Fintype.ofFinite σv
  have hc : Fintype.card ((Set.range P.map)ᶜ : Set ιv) = D := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj, ← hP]
    simp [Algebra.Presentation.dimension]
  let e := Fintype.equivFinOfCardEq hc
  let B := P.basisKaehler.reindex e
  have hB : ∀ i, KaehlerDifferential.D k A (P.val (e.symm i)) = B i := fun i => by
    simp [B]
  refine ⟨fun i => P.val (e.symm i), fun c =>
    { toFun := fun s => B.coord c (KaehlerDifferential.D k A s)
      map_zero' := by simp
      map_add' := fun s t => by simp }, fun c a b => ?_, fun a c => ?_, fun c r => ?_⟩
  · change B.coord c (KaehlerDifferential.D k A (a * b)) =
      a * B.coord c (KaehlerDifferential.D k A b) + b * B.coord c (KaehlerDifferential.D k A a)
    rw [Derivation.leibniz, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  · change B.coord c (KaehlerDifferential.D k A (P.val (e.symm a))) = _
    rw [hB, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  · change B.coord c (KaehlerDifferential.D k A (algebraMap k A r)) = 0
    rw [Derivation.map_algebraMap, map_zero]

def jetVec {A K : Type} [CommRing A] [Field K] {D : ℕ} (φ : A →+* K) (d : Fin D → A →+ A)
    (hd : ∀ c a b, d c (a * b) = a * d c b + b * d c a) : A →+* TrivSqZeroExt K (Fin D → K) where
  toFun s := (φ s, fun c => φ (d c s))
  map_one' := by
    refine TrivSqZeroExt.ext (map_one φ) ?_
    funext c
    have h1 : d c 1 = 0 := by simpa using hd c 1 1
    change φ (d c 1) = 0
    rw [h1, map_zero]
  map_zero' := by
    refine TrivSqZeroExt.ext (map_zero φ) ?_
    funext c
    change φ (d c 0) = 0
    rw [map_zero, map_zero]
  map_add' s t := by
    refine TrivSqZeroExt.ext (map_add φ s t) ?_
    funext c
    change φ (d c (s + t)) = φ (d c s) + φ (d c t)
    rw [map_add (f := _), map_add (f := _)]
  map_mul' s t := by
    refine TrivSqZeroExt.ext (map_mul φ s t) ?_
    refine Eq.trans ?_ (TrivSqZeroExt.snd_mul _ _).symm
    funext c
    show φ (d c (s * t)) = (φ s • (fun c => φ (d c t)) + MulOpposite.op (φ t) • (fun c => φ (d c s))) c
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, hd c, map_add, map_mul, map_mul, mul_comm (φ (d c s))]

theorem evalPt_congr {R : Type} [CommRing R] {X : Scheme.{0}} {x y : Sp R ⟶ X} (e : x = y) (U : X.Opens)
    (hx : ⊤ ≤ x ⁻¹ᵁ U) (hy : ⊤ ≤ y ⁻¹ᵁ U) (f : Γ(X, U)) : evalPt x U hx f = evalPt y U hy f := by
  subst e; rfl

end GlobalTheory.TanPt

namespace GlobalTheory.TanPt

theorem exists_tangent_point : ∀ {o : Type} [CommRing o] (X : Scheme.{0}) (s : X ⟶ Sp o) (D : ℕ), SmoothOfRelativeDimension D s → ∀ (K : Type) [Field K] (β : o →+* K) (x₀ : Sp K ⟶ X), x₀ ≫ s = spMap β → ∃ y : Sp (TrivSqZeroExt K (Fin D → K)) ⟶ X, spMap (TrivSqZeroExt.fstHom K K (Fin D → K)).toRingHom ≫ y = x₀ ∧ y ≫ s = spMap ((algebraMap K (TrivSqZeroExt K (Fin D → K))).comp β) ∧ ∀ mu : (Fin D → K) →ₗ[K] K, spMap (dirMap mu) ≫ y = constPt (spMap (dirMap mu) ≫ y) → mu = 0 := by
  intro o _ Y p D hsm K _ β z hz
  haveI := hsm
  obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (GlobalTheory.Adelic.ptOf z))
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) p ‹_›
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  obtain ⟨S, hS, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (S : Set Γ(Y, V)), GlobalTheory.Adelic.ptOf z ∈ Y.basicOpen (t : Γ(Y, V)) :=
    TopologicalSpace.Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hV).2 hS).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen hV (t : Γ(Y, V))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of o)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(Y, Y.basicOpen (t : Γ(Y, V))))
  have h₂ : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (Y.basicOpen (t : Γ(Y, V)))).IsStandardSmoothOfRelativeDimension D := by
    rw [← GlobalTheory.TopForm.resG_comp_algX (p := p) (Y.basicOpen_le (t : Γ(Y, V)))]
    exact h₁
  obtain ⟨x, d, hl, hd, h0⟩ := exists_coords_derivs' h₂
  have hO : IsAffineOpen (Y.basicOpen (t : Γ(Y, V))) := IsAffineOpen.basicOpen hV _
  have hzO : ⊤ ≤ z ⁻¹ᵁ Y.basicOpen (t : Γ(Y, V)) := (GlobalTheory.Adelic.le_iff_ptOf_mem z _).2 hxt
  obtain ⟨w, hw, he⟩ := exists_evalPt_eq hO (jetVec (evalPt z _ hzO) d hl)
  refine ⟨w, ?_, ?_, fun mu hmu => ?_⟩
  · have h' : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom K K (Fin D → K)).toRingHom ≫ w) ⁻¹ᵁ
        Y.basicOpen (t : Γ(Y, V)) := fun q _ => hw (Set.mem_univ _)
    refine ext_evalPt hO h' hzO (RingHom.ext fun f => ?_)
    refine (evalPt_spMap_comp _ w _ hw h' f).trans ?_
    rw [he]
    rfl
  · refine eq_spMap_of_evalPt _ _ fun a => ?_
    rw [← evalPt_constFn p w _ hw a, he]
    have hza : evalPt z _ hzO (constFn p (Y.basicOpen (t : Γ(Y, V))) a) = β a := by
      rw [evalPt_constFn]
      exact (evalPt_congr hz (⊤ : (Sp o).Opens) _ le_rfl _).trans (evalPt_spMap β a)
    refine TrivSqZeroExt.ext ?_ ?_
    · exact hza
    · funext c
      change evalPt z _ hzO (d c (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p _ a)) = _
      rw [h0 c a, map_zero]
      rfl
  · refine (Pi.basisFun K (Fin D)).ext fun a => ?_
    have h1 : ⊤ ≤ (spMap (dirMap mu) ≫ w) ⁻¹ᵁ Y.basicOpen (t : Γ(Y, V)) := fun q _ => hw (Set.mem_univ _)
    have h2 : ⊤ ≤ (constPt (spMap (dirMap mu) ≫ w)) ⁻¹ᵁ Y.basicOpen (t : Γ(Y, V)) :=
      fun q _ => hw (Set.mem_univ _)
    have h3 : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (dirMap mu) ≫ w) ⁻¹ᵁ
        Y.basicOpen (t : Γ(Y, V)) := fun q _ => hw (Set.mem_univ _)
    have e := congrArg TrivSqZeroExt.snd (evalPt_congr hmu _ h1 h2 (x a))
    have e2 : (evalPt (constPt (spMap (dirMap mu) ≫ w)) _ h2 (x a)).snd = 0 := by
      rw [evalPt_congr (show constPt (spMap (dirMap mu) ≫ w) = spMap (algebraMap K (DualNumber K)) ≫
        (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (dirMap mu) ≫ w) from rfl) _ h2 h2,
        evalPt_spMap_comp _ _ _ h3 h2]
      rfl
    rw [e2, evalPt_spMap_comp _ w _ hw h1, he] at e
    have hv : (fun c => evalPt z _ hzO (d c (x a))) = Pi.basisFun K (Fin D) a := by
      funext c
      rw [hd, Pi.basisFun_apply]
      by_cases hac : a = c
      · subst hac
        simp
      · simp [hac, Pi.single_apply, Ne.symm hac]
    rw [LinearMap.zero_apply, ← hv]
    rw [dirMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, TrivSqZeroExt.snd_map] at e
    exact e

end GlobalTheory.TanPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFirstOrderTangentPointSmoothStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_firstOrder_tangentPoint_smooth : ∀ {o : Type} [CommRing o] (X : Scheme.{0}) (s : X ⟶ Sp o) (D : ℕ), SmoothOfRelativeDimension D s → ∀ (K : Type) [Field K] (β : o →+* K) (x₀ : Sp K ⟶ X), x₀ ≫ s = spMap β → ∃ y : Sp (TrivSqZeroExt K (Fin D → K)) ⟶ X, spMap (TrivSqZeroExt.fstHom K K (Fin D → K)).toRingHom ≫ y = x₀ ∧ y ≫ s = spMap ((algebraMap K (TrivSqZeroExt K (Fin D → K))).comp β) ∧ ∀ mu : (Fin D → K) →ₗ[K] K, spMap (dirMap mu) ≫ y = constPt (spMap (dirMap mu) ≫ y) → mu = 0 := by
  first | exact @GlobalTheory.TanPt.exists_tangent_point | exact GlobalTheory.TanPt.exists_tangent_point | (intros; apply GlobalTheory.TanPt.exists_tangent_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPointLiftsToDualNumbers
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.FirstOrderSiegel

open GlobalTheory.SiegelPullComp GlobalTheory.SiegelRingChange

variable {h k : ℕ}

theorem isLocalRing_tsze (K : Type) [Field K] (r : ℕ) : IsLocalRing (TrivSqZeroExt K (Fin r → K)) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact IsLocalRing.isUnit_or_isUnit_one_sub_self _

theorem isArtinianRing_tsze (K : Type) [Field K] (r : ℕ) : IsArtinianRing (TrivSqZeroExt K (Fin r → K)) :=
  haveI : Module.Finite K (TrivSqZeroExt K (Fin r → K)) := inferInstanceAs (Module.Finite K (K × (Fin r → K)))
  IsArtinianRing.of_finite K _

theorem pull_exists {B : Type} [CommRing B] {ζ : B} {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B}
    (f : S' ⟶ S) (hf : f ≫ s = s') (c : SiegPre h k ζ s) :
    ∃ c' : SiegPre h k ζ s', SiegPB c' c f ∧ (c.Principal → c'.Principal) := by
  have e : f ≫ s = s' ≫ spMap (RingHom.id B) := by
    rw [hf]
    simp [spMap]
  have H := siegPre_pull_ringChange h k B B ζ ζ (RingHom.id B) S S' s s' f rfl e
  obtain ⟨c', hc'⟩ := H.1 c
  exact ⟨c', hc', H.2.1 c c' hc'⟩

theorem pb_symm {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S : Scheme.{0}} {s : S ⟶ Sp B}
    {s' : S ⟶ Sp B'} {c : SiegPre h k ζ s} {c' : SiegPre h k ζ' s'} (m : SiegPB c' c (𝟙 S)) : SiegPB c c' (𝟙 S) :=
  pb_cancel m (by rw [Category.comp_id]; exact pb_id c)

theorem constPt_comp {K : Type} [Field K] {X Y : Scheme.{0}} (x : Sp (DualNumber K) ⟶ X) (z : X ⟶ Y) :
    constPt (x ≫ z) = constPt x ≫ z := by
  unfold constPt
  simp only [Category.assoc]

theorem base_map {K o V W : Type} [Field K] [CommRing o] [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V] [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W] (β : o →+* K)
    (L : V →ₗ[K] W) : spMap (TrivSqZeroExt.map L).toRingHom ≫ spMap ((algebraMap K (TrivSqZeroExt K V)).comp β) =
      spMap ((algebraMap K (TrivSqZeroExt K W)).comp β) := by
  rw [← spMap_comp']
  congr 1 <;> exact RingHom.ext fun z => (TrivSqZeroExt.map L).commutes (β z)

theorem fst_base {K o V : Type} [Field K] [CommRing o] [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V] (β : o →+* K) :
    spMap (TrivSqZeroExt.fstHom K K V).toRingHom ≫ spMap ((algebraMap K (TrivSqZeroExt K V)).comp β) = spMap β := by
  rw [← spMap_comp']
  congr 1 <;> exact RingHom.ext fun z => (TrivSqZeroExt.fstHom K K V).commutes (β z)

theorem constPt_base {K o : Type} [Field K] [CommRing o] {X : Scheme.{0}} (β : o →+* K) (x : Sp (DualNumber K) ⟶ X)
    (s : X ⟶ Sp o) (hx : x ≫ s = spMap ((algebraMap K (DualNumber K)).comp β)) :
    constPt x ≫ s = x ≫ s := by
  unfold constPt
  rw [Category.assoc, Category.assoc, hx, fst_base, ← spMap_comp']

theorem dirMap_comp {K : Type} [Field K] {r m : ℕ} (mu : (Fin m → K) →ₗ[K] K) (L : (Fin r → K) →ₗ[K] (Fin m → K)) :
    spMap (dirMap (mu ∘ₗ L)) = spMap (dirMap mu) ≫ spMap (TrivSqZeroExt.map L).toRingHom := by
  rw [← spMap_comp']
  congr 1 <;> exact RingHom.ext fun x => TrivSqZeroExt.ext (by simp [dirMap]) (by simp [dirMap])

def drop (K : Type) [Field K] (d : ℕ) : (Fin (d + 1) → K) →ₗ[K] (Fin d → K) := GlobalTheory.InnerAutomorphism.dropLast K d

def lastC (K : Type) [Field K] (d : ℕ) : (Fin (d + 1) → K) →ₗ[K] K := LinearMap.proj (Fin.last d)

def incl (K : Type) [Field K] (d : ℕ) : (Fin d → K) →ₗ[K] (Fin (d + 1) → K) where
  toFun w := Fin.snoc w 0
  map_add' w w' := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' a w := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem bij_drop_last (K : Type) [Field K] (d : ℕ) : Function.Bijective ((drop K d).prod (lastC K d)) := by
  refine ⟨fun v w hvw => ?_, fun p => ⟨Fin.snoc p.1 p.2, ?_⟩⟩
  · have h1 := congrArg Prod.fst hvw
    have h2 := congrArg Prod.snd hvw
    simp only [LinearMap.prod_apply] at h1 h2
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact h2
    · exact congrFun h1 j
  · ext j <;> simp [drop, lastC, GlobalTheory.InnerAutomorphism.dropLast]

theorem lam_decomp (K : Type) [Field K] (d : ℕ) (lam : (Fin (d + 1) → K) →ₗ[K] K) :
    lam = (lam ∘ₗ incl K d) ∘ₗ drop K d + lam (Pi.single (Fin.last d) 1) • lastC K d := by
  refine LinearMap.ext fun v => ?_
  have hv : v = incl K d (drop K d v) + v (Fin.last d) • Pi.single (Fin.last d) 1 := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [incl]
    · simp [incl, drop, GlobalTheory.InnerAutomorphism.dropLast, Pi.single_apply, Fin.castSucc_ne_last]
  conv_lhs => rw [hv]
  simp [lastC, mul_comm]

theorem classified_dualNumber_of_algClosed : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (K : Type) [Field K] [IsAlgClosed K] (β₀ : cycAway n →+* K) (c : SiegPre g n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β₀))), c.Principal → ∃ f : Sp (DualNumber K) ⟶ F.X, f ≫ F.s = spMap ((algebraMap K (DualNumber K)).comp β₀) ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F K _ _ β₀ c hc

  obtain ⟨c₀, hc₀, hc₀p⟩ := pull_exists (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (fst_base β₀) c
  obtain ⟨x₀, hx₀s, hx₀⟩ := GlobalTheory.T.siegel_family_classifies_principal_algClosed g n hg hn hodd F K β₀ c₀ (hc₀p hc)

  obtain ⟨y, hy₀, hys, hyinj⟩ := GlobalTheory.T.exists_firstOrder_tangentPoint_smooth F.X F.s (g * (g + 1) / 2) F.smooth K β₀ x₀ hx₀s
  obtain ⟨cy, hcy, hcyp⟩ := pull_exists y hys F.univ
  have h0y : SiegPB c₀ cy (spMap (TrivSqZeroExt.fstHom K K (Fin (g * (g + 1) / 2) → K)).toRingHom) :=
    pb_cancel hcy (by rw [hy₀]; exact hx₀)

  have hsq := GlobalTheory.T.trivial_square_zero_extension_pullback K (Fin (g * (g + 1) / 2 + 1) → K) (Fin (g * (g + 1) / 2) → K) K (drop K _) (lastC K _)
    (bij_drop_last K _)
  let β : CommRingCat.of (cycAway n) ⟶ CommRingCat.of (TrivSqZeroExt K (Fin (g * (g + 1) / 2 + 1) → K)) :=
    CommRingCat.ofHom ((algebraMap K (TrivSqZeroExt K (Fin (g * (g + 1) / 2 + 1) → K))).comp β₀)
  obtain ⟨c₁, hc₁, hc₁p⟩ := pull_exists (𝟙 _)
    (s' := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (drop K (g * (g + 1) / 2))).toRingHom) ≫ Spec.map β)
    (by rw [Category.id_comp]; exact (base_map β₀ _).symm) cy
  obtain ⟨c₂, hc₂, hc₂p⟩ := pull_exists (𝟙 _)
    (s' := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (lastC K (g * (g + 1) / 2))).toRingHom) ≫ Spec.map β)
    (by rw [Category.id_comp]; exact (base_map β₀ _).symm) c
  obtain ⟨c₀', hc₀', -⟩ := pull_exists (𝟙 _)
    (s' := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K (Fin (g * (g + 1) / 2) → K)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (drop K (g * (g + 1) / 2))).toRingHom) ≫ Spec.map β)
    (by
      rw [Category.id_comp]
      exact ((congrArg (spMap (TrivSqZeroExt.fstHom K K (Fin (g * (g + 1) / 2) → K)).toRingHom ≫ ·)
        (base_map β₀ (drop K _))).trans (fst_base β₀)).symm) c₀
  have h01 : SiegPB c₀' c₁ (spMap (TrivSqZeroExt.fstHom K K (Fin (g * (g + 1) / 2) → K)).toRingHom) := by
    have := pb_comp (pb_comp (pb_symm hc₁) h0y) hc₀'
    rwa [Category.comp_id, Category.id_comp] at this
  have h02 : SiegPB c₀' c₂ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    have := pb_comp (pb_comp (pb_symm hc₂) hc₀) hc₀'
    rwa [Category.comp_id, Category.id_comp] at this
  obtain ⟨G, hGp, hG1, hG2⟩ := GlobalTheory.T.exists_principalSiegelObject_glue_artinFibreProduct g n hn hodd _ _ (CommRingCat.of (DualNumber K)) (CommRingCat.of K) _ _ _ _
    hsq (isLocalRing_tsze K _) (isArtinianRing_tsze K _) (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩)
    (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩) β c₁ c₂ (hc₁p (hcyp F.princ)) (hc₂p hc) ⟨c₀', h01, h02⟩
  have hGy : SiegPB cy G (spMap (TrivSqZeroExt.map (drop K (g * (g + 1) / 2))).toRingHom) := by
    have := pb_comp hG1 (pb_symm hc₁)
    rwa [Category.id_comp] at this
  have hGc : SiegPB c G (spMap (dirMap (lastC K (g * (g + 1) / 2)))) := by
    have := pb_comp hG2 (pb_symm hc₂)
    rwa [Category.id_comp] at this

  have htb := GlobalTheory.T.siegelFamily_tangentBound_nonconstant g n hg hn hodd K (g * (g + 1) / 2 + 1) β₀ G hGp
  obtain ⟨lam, c', h1, h2, hlam⟩ : ∃ (lam : (Fin (g * (g + 1) / 2 + 1) → K) →ₗ[K] K)
      (c' : SiegPre g n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β₀))),
      SiegPB c' G (spMap (dirMap lam)) ∧ SiegPB c' G (constPt (spMap (dirMap lam))) ∧ lam ≠ 0 := by
    by_contra hne
    push_neg at hne
    have := htb fun lam c' h1 h2 => hne lam c' h1 h2
    omega
  obtain ⟨mu, a, hdec⟩ : ∃ (mu : (Fin (g * (g + 1) / 2) → K) →ₗ[K] K) (a : K),
      lam = mu ∘ₗ drop K _ + a • lastC K _ := ⟨_, _, lam_decomp K _ lam⟩
  by_cases ha : a = 0
  ·
    exfalso
    rw [ha, zero_smul, add_zero] at hdec
    subst hdec
    rw [dirMap_comp] at h1 h2
    rw [constPt_comp] at h2
    have k1 : SiegPB c' F.univ (spMap (dirMap mu) ≫ y) := pb_comp hcy (pb_cancel hGy h1)
    have k2 : SiegPB c' F.univ (constPt (spMap (dirMap mu) ≫ y)) := by
      rw [constPt_comp]
      exact pb_comp hcy (pb_cancel hGy h2)
    have hxs : (spMap (dirMap mu) ≫ y) ≫ F.s = spMap ((algebraMap K (DualNumber K)).comp β₀) := by
      rw [Category.assoc, hys]
      exact base_map β₀ mu
    obtain ⟨c'', hc'', -⟩ := pull_exists (𝟙 _) (s' := (spMap (dirMap mu) ≫ y) ≫ F.s)
      (by rw [Category.id_comp, hxs]) c'
    have e := F.eq_constPt K (spMap (dirMap mu) ≫ y) c'' (constPt_base β₀ _ _ hxs).symm
      (by have := pb_comp k1 hc''; rwa [Category.id_comp] at this)
      (by have := pb_comp k2 hc''; rwa [Category.id_comp] at this)
    have := hyinj mu e
    subst this
    exact hlam (by simp)
  ·
    have hκ : lastC K (g * (g + 1) / 2) = ((-a⁻¹) • mu) ∘ₗ drop K _ + a⁻¹ • lam := by
      rw [hdec]
      refine LinearMap.ext fun v => ?_
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, neg_mul]
      field_simp
      ring
    have k := GlobalTheory.T.siegelObject_tangentShift_constancy_direction_iso g n hn hodd K _ β₀ G hGp lam _ _ a⁻¹ c' c hκ h1 h2 hGc
    rw [dirMap_comp] at k
    refine ⟨spMap (dirMap ((-a⁻¹) • mu)) ≫ y, ?_, pb_comp hcy (pb_cancel hGy k)⟩
    rw [Category.assoc, hys]
    exact base_map β₀ _

end GlobalTheory.FirstOrderSiegel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPointLiftsToDualNumbersStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_point_lifts_to_dual_numbers : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (K : Type) [Field K] [IsAlgClosed K] (β₀ : cycAway n →+* K) (c : SiegPre g n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β₀))), c.Principal → ∃ f : Sp (DualNumber K) ⟶ F.X, f ≫ F.s = spMap ((algebraMap K (DualNumber K)).comp β₀) ∧ SiegPB c F.univ f := by
  first | exact @GlobalTheory.FirstOrderSiegel.classified_dualNumber_of_algClosed | exact GlobalTheory.FirstOrderSiegel.classified_dualNumber_of_algClosed | (intros; apply GlobalTheory.FirstOrderSiegel.classified_dualNumber_of_algClosed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectDualNumberClassified
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.SiegelTangent

theorem cycAway_dualNumber_factor {n : ℕ} (hn : n ≠ 0) (K : Type) [Field K] (β : cycAway n →+* DualNumber K) :
    ∃ β₀ : cycAway n →+* K, β = (algebraMap K (DualNumber K)).comp β₀ := by
  let π : DualNumber K →+* K := (TrivSqZeroExt.fstHom K K K).toRingHom
  have hnK : (n : K) ≠ 0 := by
    have := ((isUnit_natCast hn).map (π.comp β)).ne_zero
    simpa using this
  let S : Subring (cycAway n) :=
    { carrier := {x | TrivSqZeroExt.snd (β x) = 0}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul, TrivSqZeroExt.snd_mul] at *
        simp [ha, hb]
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add (f := _), TrivSqZeroExt.snd_add] at *
        simp [ha, hb]
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq, map_neg, TrivSqZeroExt.snd_neg] at *
        simp [ha] }
  have hζ : zetaAway n ∈ S := by
    have hz : zetaAway n ^ n = 1 := Subtype.ext (Complex.isPrimitiveRoot_exp n hn).pow_eq_one
    have h1 : β (zetaAway n) ^ n = 1 := by rw [← map_pow, hz, map_one]
    have h2 := congrArg TrivSqZeroExt.snd h1
    have h3 := congrArg TrivSqZeroExt.fst h1
    rw [TrivSqZeroExt.snd_pow] at h2
    rw [TrivSqZeroExt.fst_pow] at h3
    simp only [TrivSqZeroExt.snd_one, TrivSqZeroExt.fst_one] at h2 h3
    have ha : TrivSqZeroExt.fst (β (zetaAway n)) ≠ 0 := by
      intro h0; rw [h0, zero_pow hn] at h3; exact zero_ne_one h3
    show TrivSqZeroExt.snd (β (zetaAway n)) = 0
    rw [nsmul_eq_mul, smul_eq_mul] at h2
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hnK
    · rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' (pow_ne_zero _ ha)
      · exact h'
  have hinv : (⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ : cycAway n) ∈ S := by
    set u : cycAway n := ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩
    have hu : (n : cycAway n) * u = 1 :=
      Subtype.ext (by simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn : (n : ℂ) ≠ 0))
    have h1 : (n : DualNumber K) * β u = 1 := by rw [← map_natCast β, ← map_mul, hu, map_one]
    have h2 := congrArg TrivSqZeroExt.snd h1
    simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_one, TrivSqZeroExt.fst_natCast,
      TrivSqZeroExt.snd_natCast, smul_zero, add_zero, smul_eq_mul] at h2
    show TrivSqZeroExt.snd (β u) = 0
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hnK
    · exact h
  have hall : ∀ x : cycAway n, x ∈ S := by
    rintro ⟨x, hx⟩
    induction hx using Subring.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact hζ
      · exact hinv
    | zero => exact S.zero_mem
    | one => exact S.one_mem
    | add y z _ _ hy hz => exact S.add_mem hy hz
    | neg y _ hy => exact S.neg_mem hy
    | mul y z _ _ hy hz => exact S.mul_mem hy hz
  refine ⟨π.comp β, RingHom.ext fun x => ?_⟩
  ext
  · rfl
  · exact (hall x).trans (TrivSqZeroExt.snd_inl _ _).symm

theorem classified_dualNumber : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (K : Type) [Field K]
    (β : cycAway n →+* DualNumber K) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal →
    ∃ f : Sp (DualNumber K) ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F K _ β c hc
  have hn0 : n ≠ 0 := by omega
  obtain ⟨β₀, rfl⟩ := cycAway_dualNumber_factor hn0 K β
  let L := AlgebraicClosure K
  obtain ⟨ψ, h1, -, hfl, hsurj⟩ := GlobalTheory.DualOpen.dualNumber_map_flat_surjective K L (algebraMap K L)
  have hff : ψ.FaithfullyFlat := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom ψ)).1 ⟨hfl, hsurj⟩
  letI : Algebra (DualNumber K) (DualNumber L) := ψ.toAlgebra
  haveI : Module.FaithfullyFlat (DualNumber K) (DualNumber L) := RingHom.faithfullyFlat_algebraMap_iff.1 hff
  refine GlobalTheory.T.siegelFamily_classified_of_faithfullyFlat g n hg hn hodd F (DualNumber K) (DualNumber L) _ c hc ?_
  intro c' hc'
  have hp : c'.Principal := by
    refine (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n)
      (RingHom.id _) _ _ (spMap ((algebraMap K (DualNumber K)).comp β₀))
      (spMap ((algebraMap (DualNumber K) (DualNumber L)).comp ((algebraMap K (DualNumber K)).comp β₀)))
      (spMap (algebraMap (DualNumber K) (DualNumber L))) rfl ?_).2.1 c c' hc' hc
    rw [GlobalTheory.SiegelRingChange.spMap_comp']
    simp [spMap]
  have e : (algebraMap (DualNumber K) (DualNumber L)).comp ((algebraMap K (DualNumber K)).comp β₀) =
      (algebraMap L (DualNumber L)).comp ((algebraMap K L).comp β₀) := by
    rw [← RingHom.comp_assoc, ← RingHom.comp_assoc]
    exact congrArg (fun q => q.comp β₀) h1
  have key : ∀ b : cycAway n →+* DualNumber L, b = (algebraMap L (DualNumber L)).comp ((algebraMap K L).comp β₀) →
      ∀ c' : SiegPre g n (zetaAway n) (spMap b), c'.Principal →
      ∃ f : Sp (DualNumber L) ⟶ F.X, f ≫ F.s = spMap b ∧ SiegPB c' F.univ f := by
    rintro b rfl c' hc'
    exact GlobalTheory.T.siegel_point_lifts_to_dual_numbers g n hg hn hodd F L ((algebraMap K L).comp β₀) c' hc'
  exact key _ e c' hp

end GlobalTheory.SiegelTangent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectDualNumberClassifiedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelObject_dualNumber_classified : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (K : Type) [Field K] (β : cycAway n →+* DualNumber K) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp (DualNumber K) ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  first | exact @GlobalTheory.SiegelTangent.classified_dualNumber | exact GlobalTheory.SiegelTangent.classified_dualNumber | (intros; apply GlobalTheory.SiegelTangent.classified_dualNumber <;> assumption)
end
