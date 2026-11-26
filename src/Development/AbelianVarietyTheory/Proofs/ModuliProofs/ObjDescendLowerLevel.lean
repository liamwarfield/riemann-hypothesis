module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjDescendLowerLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.ObjDesc

open GlobalTheory.ObjPull

theorem exists_geomPt_lift {X Y : Scheme.{0}} (π : X ⟶ Y) [LocallyOfFiniteType π] [Surjective π]
    (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y) : ∃ y : Sp k ⟶ X, y ≫ π = x := by

  have hJ := LocallyOfFiniteType.jacobsonSpace (pullback.snd π x)
  obtain ⟨p, -⟩ := (pullback.snd π x).surjective (IsLocalRing.closedPoint k)
  obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints (Set.nonempty_of_mem (Set.mem_univ p))
    isOpen_univ.isLocallyClosed
  have hc' : IsClosed {c} := hc
  have hpt := pointOfClosedPoint_comp (pullback.snd π x) c hc'
  refine ⟨pointOfClosedPoint (pullback.snd π x) c hc' ≫ pullback.fst π x, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hpt, Category.id_comp]

section Sections

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem secPull_injective [Epi f] (h : IsGrpPullback G' G f φ) : Function.Injective (secPull h) := by
  intro e₁ e₂ he
  have key : f ≫ e₁.left = f ≫ e₂.left := by
    rw [← secPull_left h e₁, ← secPull_left h e₂, he]
  exact Over.OverMorphism.ext ((cancel_epi f).1 key)

theorem secPull_eq (h : IsGrpPullback G' G f φ) {e : 𝟙_ (Over S) ⟶ G} {e' : 𝟙_ (Over S') ⟶ G'}
    (he : e'.left ≫ φ = f ≫ e.left) : secPull h e = e' := by

  refine Over.OverMorphism.ext (h.1.hom_ext ?_ ?_)
  · rw [secPull_left, he]
  · exact (Over.w _).trans (Over.w e').symm

theorem exists_sec [Epi f] (h : IsGrpPullback G' G f φ) (e' : 𝟙_ (Over S') ⟶ G') (g : S ⟶ G.left)
    (hg : f ≫ g = e'.left ≫ φ) : ∃ e : 𝟙_ (Over S) ⟶ G, e'.left ≫ φ = f ≫ e.left := by

  have hsec : g ≫ G.hom = (𝟙_ (Over S)).hom := by
    apply (cancel_epi f).1
    rw [← Category.assoc, hg, Category.assoc, h.1.w, ← Category.assoc, Over.w e']
    simp
  exact ⟨Over.homMk g hsec, hg.symm⟩

end Sections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'} {X Y : Scheme.{0}}
  {s : Y ⟶ Sp B} {s' : X ⟶ Sp B'} {π : X ⟶ Y}

def descend [Epi π] [LocallyOfFiniteType π] [Surjective π] (j : B →+* B') (hρ : j b.ρ = b'.ρ) (hζ : j b.ζ = b'.ζ)
    (hs : π ≫ s = s' ≫ spMap j) (o : Obj D l b' s') (t : SAB H Y) (m : SABMap o.t t π)
    (hp : IsProper t.G.hom) (ha : Out.RelAmple t.G t.PP.L) (hk : Out.KTriv t.G t.PP.L)
    (e eA : D.La → (𝟙_ (Over Y) ⟶ t.G)) (he : ∀ a, secPull m.cart (e a) = o.eta a)
    (heA : ∀ a, secPull m.cart (eA a) = o.etaA a) : Obj D l b s where
  t := t
  proper := hp
  ample := ha
  ktriv := hk
  eta := e
  eta_add a c := secPull_injective m.cart (by rw [map_mul, he, he, he, o.eta_add])
  eta_ker a h := secPull_injective m.cart (by rw [map_one, he, o.eta_ker a h])
  etaA := eA
  etaA_add a c := secPull_injective m.cart (by rw [map_mul, heA, heA, heA, o.etaA_add])
  etaA_ker a := secPull_injective m.cart (by rw [map_one, heA, o.etaA_ker a])
  geom k _ _ x β hx := by
    obtain ⟨y, rfl⟩ := exists_geomPt_lift π k x
    obtain ⟨β', hβ'⟩ : ∃ β' : B' →+* k, y ≫ s' = spMap β' :=
      ⟨(Spec.preimage (y ≫ s')).hom, (Spec.map_preimage _).symm⟩
    obtain rfl : β = β'.comp j := by
      have : spMap β = spMap (β'.comp j) := by
        rw [← hx, Category.assoc, hs, ← Category.assoc, hβ', spMap_comp]
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
    have hL : LBIso o.t.PP.L (t.PP.L.pull m.cm.F) := by
      obtain ⟨w, hw, -⟩ := m.lin
      exact ⟨w, hw⟩
    obtain ⟨hdet, I, hI, hA, hM⟩ := o.geom k y β' hβ'
    rw [RingHom.comp_apply, RingHom.comp_apply, hρ, hζ]
    refine ⟨fun τ => ?_, tateMove (pushEquiv m.cart (Over.mk y)).symm (fun c g => ?_) (fun n g g' c hc => ?_) I,
      hI, fun a => ?_, fun a ha => ?_⟩
    · rw [← GlobalTheory.LiePull.lieMult_pull _ Y X t.G o.t.G π m.cm.F t.act o.t.act m.cart m.act k y τ,
        ← GlobalTheory.LiePull.lieMult_pull _ Y X t.G o.t.G π m.cm.F t.act o.t.act m.cart m.act k y τ]
      exact hdet τ
    · obtain ⟨g, rfl⟩ := (pushEquiv m.cart (Over.mk y)).surjective g
      rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_eq]
      apply Over.OverMorphism.ext
      show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
      rw [Category.assoc, ← m.act, Category.assoc]
    · exact (GlobalTheory.weilIs_grpPullback_of_comm Y X t.G o.t.G π m.cm.F t.PP.L o.t.PP.L t.PP.isLB o.t.PP.isLB m.cart hL
        (Over.mk y) n _ _ g g' _ (pushEquiv_symm_left m.cart (Over.mk y) g).symm
        (pushEquiv_symm_left m.cart (Over.mk y) g').symm).1 hc
    · refine (pushEquiv_secPull m.cart (Over.mk y) _).symm.trans ?_
      rw [heA, hA]
      rfl
    · refine (pushEquiv_secPull m.cart (Over.mk y) _).symm.trans ?_
      rw [he, hM a ha]
      rfl

def lowerBase {l₂ : Level H} (h : l.Dvd l₂) (b₂ : Base l₂ B') : Base l B' where
  unit := b₂.unit
  ρ := b₂.ρ
  ρ_sq := b₂.ρ_sq
  ζ := b₂.ζ ^ (l₂.A / l.A)
  ζ_prim := b₂.ζ_prim.pow l₂.A_pos (Nat.div_mul_cancel h.2.2).symm

end GlobalTheory.ObjDesc

theorem GlobalTheory.obj_descend_lower_level : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B B₂ : Type) [CommRing B] [CommRing B₂] (b : Base l B) (b₂ : Base l₂ B₂) (j : B →+* B₂) (X Y : Scheme.{0}) (π : X ⟶ Y) (s : Y ⟶ Sp B) (s₂ : X ⟶ Sp B₂) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (ob₂ : Obj D l₂ b₂ s₂) (ν : Ga → (ob₂.t.G.left ⟶ ob₂.t.G.left)) (t' : SAB H Y) (m : SABMap ob₂.t t' π), l.Dvd l₂ → j b.ρ = b₂.ρ → j b.ζ = b₂.ζ ^ (l₂.A / l.A) → π ≫ s = s₂ ≫ spMap j → IsGaloisCover Ga ρ π → (∀ a, ν a ≫ m.φ = m.φ) → (∀ a, Lowers l ob₂ (fun x => ob₂.eta x ^ (l₂.M / l.M)) (fun x => ob₂.etaA x ^ (l₂.A / l.A)) (ρ a) (ν a)) → IsProper t'.G.hom → Out.RelAmple t'.G t'.PP.L → Out.KTriv t'.G t'.PP.L → ∃ (ob : Obj D l b s) (m' : SABMap ob₂.t ob.t π), (∀ a, (ob₂.eta a ^ (l₂.M / l.M)).left ≫ m'.φ = π ≫ (ob.eta a).left) ∧ ∀ a, (ob₂.etaA a ^ (l₂.A / l.A)).left ≫ m'.φ = π ≫ (ob.etaA a).left := by
  intro _ _ E _ _ _ H D l l₂ B B₂ _ _ b b₂ j X Y π s s₂ Ga _ ρ ob₂ ν t' m hdvd hρ hζ hs hG hν hlow hp ha hk

  have : Epi π := ⟨fun g₁ g₂ hg => (hG.existsUnique_desc (π ≫ g₁)
    (fun a => by rw [← Category.assoc, hG.inv])).unique rfl hg.symm⟩
  have : IsFinite π := hG.fin
  have : Surjective π := hG.onto

  let o := GlobalTheory.ObjLower.lower (b := GlobalTheory.ObjDesc.lowerBase hdvd b₂) ob₂ hdvd rfl rfl

  have desc : ∀ u : D.La → (𝟙_ (Over X) ⟶ ob₂.t.G), (∀ c a, ρ c ≫ (u a).left = (u a).left ≫ ν c) →
      ∃ w : D.La → (𝟙_ (Over Y) ⟶ t'.G), ∀ a, (u a).left ≫ m.φ = π ≫ (w a).left := by
    intro u hu
    have hex : ∀ a, ∃ w : 𝟙_ (Over Y) ⟶ t'.G, (u a).left ≫ m.φ = π ≫ w.left := by
      intro a
      obtain ⟨g, hg, -⟩ := hG.existsUnique_desc ((u a).left ≫ m.φ)
        (fun c => by rw [← Category.assoc, hu c a, Category.assoc, hν c])
      exact GlobalTheory.ObjDesc.exists_sec m.cart (u a) g hg
    exact ⟨fun a => (hex a).choose, fun a => (hex a).choose_spec⟩
  obtain ⟨e, he⟩ := desc (fun a => ob₂.eta a ^ (l₂.M / l.M)) (fun c a => ((hlow c).1 a).symm)
  obtain ⟨eA, heA⟩ := desc (fun a => ob₂.etaA a ^ (l₂.A / l.A)) (fun c a => ((hlow c).2 a).symm)
  exact ⟨GlobalTheory.ObjDesc.descend (b' := GlobalTheory.ObjDesc.lowerBase hdvd b₂) j hρ hζ hs o t' m hp ha hk e eA
    (fun a => GlobalTheory.ObjDesc.secPull_eq m.cart (he a)) (fun a => GlobalTheory.ObjDesc.secPull_eq m.cart (heA a)),
    m, he, heA⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionPointsOfGeometric
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem torsionSection_eq_labelled_of_isDomain : ∀ (R : Type) [CommRing R] [IsDomain R] (P : PolAV (Sp R)) (M : ℕ) (I : Type) (pt : I → (baseOver (Sp R) ⟶ P.A)), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (z : Over.mk x ⟶ P.A), z ^ M = 1 → ∃ a, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R)) ≫ pt a = z) → ∀ y : baseOver (Sp R) ⟶ P.A, y ^ M = 1 → ∃ a, pt a = y := by
  intro R _ _ P M I pt h y hy
  let K := AlgebraicClosure (FractionRing R)
  let j : R →+* K := (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))
  have hj : Function.Injective j :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  have hdom : IsDominant (Geo.Tor.spMap j) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot j).1 hj]; exact bot_le)⟩
  have hprop : IsProper P.A.hom := P.isAb.proper
  obtain ⟨a, ha⟩ := h K (Geo.Tor.spMap j)
    ((Over.homMk (Geo.Tor.spMap j) (by simp) : Over.mk (Geo.Tor.spMap j) ⟶ baseOver (Sp R)) ≫ y)
    (by rw [← MonObj.comp_pow, hy, MonObj.comp_one])
  exact ⟨a, Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp R) P.A.hom
    ((Over.w (pt a)).trans (Over.w y).symm) (Geo.Tor.spMap j) (congrArg Over.Hom.left ha))⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ImportsBis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.UnitBallVal

theorem dvd_of_norm_le {C O : Type} [NormedField C] [CommRing O] [Algebra O C]
    (hinj : Function.Injective (algebraMap O C))
    (hsurj : ∀ x : C, ‖x‖ ≤ 1 → ∃ y : O, algebraMap O C y = x) {a b : O}
    (h : ‖algebraMap O C b‖ ≤ ‖algebraMap O C a‖) : a ∣ b := by
  by_cases ha : algebraMap O C a = 0
  · have hb : algebraMap O C b = 0 := by
      rw [ha, norm_zero] at h
      exact norm_le_zero_iff.mp h
    have hb0 : b = 0 := hinj (by rw [hb, map_zero])
    rw [hb0]
    exact dvd_zero a
  · obtain ⟨y, hy⟩ := hsurj (algebraMap O C b / algebraMap O C a) (by
      rw [norm_div]
      exact (div_le_one (norm_pos_iff.mpr ha)).mpr h)
    refine ⟨y, hinj ?_⟩
    rw [map_mul, hy]
    field_simp

theorem main : ∀ (C O : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CommRing O] [Algebra O C], IsUnitBall O C → ∃ (_ : IsDomain O), ValuationRing O ∧ Ring.DimensionLEOne O ∧ IsFractionRing O C := by
  intro C O _ _ _ _ hO
  obtain ⟨hinj, hball⟩ := hO
  have hsurj : ∀ x : C, ‖x‖ ≤ 1 → ∃ y : O, algebraMap O C y = x := fun x hx => (hball x).mpr hx
  have hle : ∀ y : O, ‖algebraMap O C y‖ ≤ 1 := fun y => (hball _).mp ⟨y, rfl⟩
  have hdom : IsDomain O := hinj.isDomain (algebraMap O C)

  have hunit : ∀ y : O, ‖algebraMap O C y‖ = 1 → IsUnit y := fun y hy =>
    isUnit_of_dvd_one (dvd_of_norm_le hinj hsurj (by rw [map_one, norm_one, hy]))
  refine ⟨hdom, { cond' := fun a b => ?_ }, ⟨fun {P} hP0 hP => ?_⟩, ?_⟩
  · rcases le_total ‖algebraMap O C b‖ ‖algebraMap O C a‖ with h | h
    · obtain ⟨c, hc⟩ := dvd_of_norm_le hinj hsurj h
      exact ⟨c, Or.inl hc.symm⟩
    · obtain ⟨c, hc⟩ := dvd_of_norm_le hinj hsurj h
      exact ⟨c, Or.inr hc.symm⟩
  ·
    obtain ⟨p, hpP, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
    have hp' : algebraMap O C p ≠ 0 := fun h0 => hp0 (hinj (by rw [h0, map_zero]))
    have key : ∀ m : O, m ∉ P → IsUnit m := by
      intro m hm
      apply hunit
      refine le_antisymm (hle m) (not_lt.mp fun hlt => hm ?_)
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hp') hlt
      obtain ⟨c, hc⟩ := dvd_of_norm_le hinj hsurj (a := p) (b := m ^ n)
        (by rw [map_pow, norm_pow]; exact hn.le)
      refine hP.mem_of_pow_mem n ?_
      rw [hc]
      exact P.mul_mem_right c hpP
    obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P hP.ne_top
    have hMP : M ≤ P := fun m hm => by
      by_contra hmP
      exact hM.ne_top (Ideal.eq_top_of_isUnit_mem M hm (key m hmP))
    rwa [le_antisymm hPM hMP]
  · refine (isLocalization_iff (nonZeroDivisors O) C).mpr ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact IsUnit.mk0 _ fun h0 => nonZeroDivisors.ne_zero hy (hinj (by rw [h0, map_zero]))
    · intro z
      by_cases hz : ‖z‖ ≤ 1
      · obtain ⟨y, hy⟩ := hsurj z hz
        exact ⟨⟨y, 1⟩, by simp [hy]⟩
      · rw [not_le] at hz
        have hz0 : z ≠ 0 := by
          rintro rfl
          rw [norm_zero] at hz
          linarith
        obtain ⟨y, hy⟩ := hsurj z⁻¹ (by rw [norm_inv]; exact inv_le_one_of_one_le₀ hz.le)
        have hy0 : y ∈ nonZeroDivisors O := mem_nonZeroDivisors_of_ne_zero (by
          rintro rfl
          rw [map_zero] at hy
          exact inv_ne_zero hz0 hy.symm)
        exact ⟨⟨1, ⟨y, hy0⟩⟩, by simp [hy, hz0]⟩
    · intro x y hxy
      exact ⟨1, by rw [hinj hxy]⟩

end GlobalTheory.UnitBallVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormPsiPullLocalRingsOfIntegers
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormPsiPullLocalRingsOfIntegers
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.PsiNormPull

theorem valF_eq_valR' {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valF x U f = valR x U f := by
  rfl

theorem toStk_map_valR {A F : Type} [CommRing A] [Field F] (ψ : A →+* F) {X : Scheme.{0}} (x : Sp A ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (z : Sp F) (a : Γ(X, U)ˣ) :
    toStk z (ψ (valR x U a.val)) = (gm (spMap ψ ≫ x) z U a).val := by
  obtain ⟨h', e⟩ := CrdCalc.valR_spMap ψ x U h
  rw [← e, ← valF_eq_valR']
  exact toStk_valF _ U z (h' trivial) a

theorem norm_eq_one_of_isUnit {A F : Type} [CommRing A] [NormedField F] (ψ : A →+* F) (hψ : ∀ a, ‖ψ a‖ ≤ 1)
    {a : A} (ha : IsUnit a) : ‖ψ a‖ = 1 := by
  obtain ⟨u, rfl⟩ := ha
  have e : ‖ψ u.val‖ * ‖ψ (u⁻¹).val‖ = 1 := by rw [← norm_mul, ← map_mul, u.mul_inv, map_one, norm_one]
  refine le_antisymm (hψ _) ?_
  calc (1 : ℝ) = ‖ψ u.val‖ * ‖ψ (u⁻¹).val‖ := e.symm
    _ ≤ ‖ψ u.val‖ * 1 := mul_le_mul_of_nonneg_left (hψ _) (norm_nonneg _)
    _ = _ := _root_.mul_one _

theorem norm_psi_pull : ∀ (p : ℕ) [Fact p.Prime] (V V' : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'] [Algebra (FractionRing V) (PadicAlgCl p)] [Algebra (FractionRing V') (PadicAlgCl p)] (φ : V →+* V'), (∀ v : V, algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V _ v) = algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ (φ v))) → (∀ v : V', ‖algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ v)‖ ≤ 1) → ∀ (D : DegPre V) (D' : DegPre V') (hD : IsPullDeg φ D D') (χ : D'.X) (j : D.P.L.ι) (j' : D'.P.L.ι), ⊤ ≤ (D.c (hD.xe χ)).left ⁻¹ᵁ D.P.L.U j → ⊤ ≤ (D'.c χ).left ⁻¹ᵁ D'.P.L.U j' → ‖algebraMap (FractionRing V') (PadicAlgCl p) (valF (𝟙 (Sp (FractionRing V'))) _ ((D'.psi χ).s fun _ => j').val)‖ = ‖algebraMap (FractionRing V) (PadicAlgCl p) (valF (𝟙 (Sp (FractionRing V))) _ ((D.psi (hD.xe χ)).s fun _ => j).val)‖ := by
  intro p _ V V' _ _ _ _ _ _ _ _ φ hφ hn D D' hD χ j j' hj hj'
  let F := PadicAlgCl p
  let ψ' : V' →+* F := (algebraMap (FractionRing V') F).comp (algebraMap V' (FractionRing V'))
  have hsq : jFK (R := V') F ≫ jK V' ≫ spMap φ = jFK (R := V) F ≫ jK V := by
    refine ((congrArg (jFK (R := V') F ≫ ·) (spMap_comp φ _).symm).trans (spMap_comp _ _).symm).trans
      ((congrArg spMap ?_).trans (spMap_comp _ _))
    exact RingHom.ext fun v => (hφ v).symm
  have z : Sp F := (default : PrimeSpectrum F)
  let Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)
  have hΦ : ⊤ ≤ ((D'.c χ).left ≫ Φ) ⁻¹ᵁ D.P.L.U j := by
    rw [show (D'.c χ).left ≫ Φ = _ from hD.c_pr χ]
    exact fun y _ => hj (Set.mem_univ ((specOf φ) y))
  let U := (D.P.L.pull Φ).U (fun _ => j) ⊓ D'.P.L.U j'
  have hU : ⊤ ≤ (D'.c χ).left ⁻¹ᵁ U := fun y _ => ⟨mem_pull.2 (hΦ (Set.mem_univ y)), hj' (Set.mem_univ y)⟩
  have m' : ∀ y, D'.xK χ y ∈ D'.P.L.U j' := fun y => hj' (Set.mem_univ (jK V' y))
  have m : ∀ y, D.xK (hD.xe χ) y ∈ D.P.L.U j := fun y => hj (Set.mem_univ (jK V y))
  have e := pmaps_psi hD F hsq χ _ (𝟙 _) z (fun _ => j) (fun _ => j')
    (fun _ => hΦ (Set.mem_univ (jK V' (jFK (R := V') F z)))) (fun _ => m' _)
  have g₁ := gm_pullGen D.P.L (fun _ : PUnit => D.xK (hD.xe χ)) (fun _ => -1) (D.psi (hD.xe χ)) (jFK (R := V) F)
    (𝟙 _ ≫ 𝟙 _) z (fun _ => j) (Set.mem_iInter.2 fun _ => m _)
  have g₂ := gm_pullGen D'.P.L (fun _ : PUnit => D'.xK χ) (fun _ => -1) (D'.psi χ) (jFK (R := V') F)
    (𝟙 _) z (fun _ => j') (Set.mem_iInter.2 fun _ => m' _)
  rw [Fintype.prod_unique] at e
  replace e := g₁.symm.trans (e.trans (congrArg₂ (· * ·) (zpow_neg_one _) g₂))
  rw [eq_inv_mul_iff_mul_eq] at e
  simp only [Category.id_comp] at e
  have a := toStk_map_valR (algebraMap (FractionRing V) F) (𝟙 _)
    (LB.wchart D.P.L (fun _ : PUnit => D.xK (hD.xe χ)) fun _ => j) (fun y _ => Set.mem_iInter.2 fun _ => m y) z
    ((D.psi (hD.xe χ)).s fun _ => j)
  have a' := toStk_map_valR (algebraMap (FractionRing V') F) (𝟙 _)
    (LB.wchart D'.P.L (fun _ : PUnit => D'.xK χ) fun _ => j') (fun y _ => Set.mem_iInter.2 fun _ => m' y) z
    ((D'.psi χ).s fun _ => j')
  rw [Category.comp_id, ← valF_eq_valR'] at a a'
  have b := toStk_map_valR ψ' (D'.c χ).left U hU z (hD.w.s (fun _ => j, j'))
  have hpt : spMap ψ' ≫ (D'.c χ).left = jFK (R := V') F ≫ D'.xK χ :=
    (congrArg (· ≫ (D'.c χ).left) (spMap_comp _ _)).trans (Category.assoc _ _ _)
  have b' : toStk z (ψ' (valR (D'.c χ).left U (hD.w.s (fun _ => j, j')).val)) =
      (gw hD.w (jFK (R := V') F ≫ D'.xK χ) z j j').val := by
    rw [← hpt]; exact b
  have hu : IsUnit (valR (D'.c χ).left U (hD.w.s (fun _ => j, j')).val) := by
    exact (congrArg IsUnit (CrdCalc.valR_eq (R := V') (D'.c χ).left U hU _)).mpr ((Units.isUnit _).map _)
  have key := (toStk z).injective (a'.trans ((congrArg Units.val e).symm.trans
    ((Units.val_mul _ _).trans ((congrArg₂ (· * ·) b' a).symm.trans (map_mul _ _ _).symm))))
  refine (congrArg norm key).trans ?_
  rw [norm_mul, norm_eq_one_of_isUnit ψ' hn hu, _root_.one_mul]
  rfl

end GlobalTheory.ZH.PsiNormPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormPsiPullLocalRingsOfIntegersStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_psi_pull_localRingsOfIntegers : ∀ (p : ℕ) [Fact p.Prime] (V V' : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'] [Algebra (FractionRing V) (PadicAlgCl p)] [Algebra (FractionRing V') (PadicAlgCl p)] (φ : V →+* V'), (∀ v : V, algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V _ v) = algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ (φ v))) → (∀ v : V', ‖algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ v)‖ ≤ 1) → ∀ (D : DegPre V) (D' : DegPre V') (hD : IsPullDeg φ D D') (χ : D'.X) (j : D.P.L.ι) (j' : D'.P.L.ι), ⊤ ≤ (D.c (hD.xe χ)).left ⁻¹ᵁ D.P.L.U j → ⊤ ≤ (D'.c χ).left ⁻¹ᵁ D'.P.L.U j' → ‖algebraMap (FractionRing V') (PadicAlgCl p) (valF (𝟙 (Sp (FractionRing V'))) _ ((D'.psi χ).s fun _ => j').val)‖ = ‖algebraMap (FractionRing V) (PadicAlgCl p) (valF (𝟙 (Sp (FractionRing V))) _ ((D.psi (hD.xe χ)).s fun _ => j).val)‖ := by
  first | exact @GlobalTheory.ZH.PsiNormPull.norm_psi_pull | exact GlobalTheory.ZH.PsiNormPull.norm_psi_pull | (intros; apply GlobalTheory.ZH.PsiNormPull.norm_psi_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteSchemeLatticeTorsionHomPrimitiveRoot
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteSchemeLatticeTorsionHomPrimitiveRoot
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TorsRootParam


open Polynomial in
abbrev CycRing (n : ℕ) : Type := AdjoinRoot (cyclotomic n ℤ)

open Polynomial in
theorem root_pow (n : ℕ) : AdjoinRoot.root (cyclotomic n ℤ) ^ n = 1 := by
  have h := (AdjoinRoot.mk_eq_zero (f := cyclotomic n ℤ)).mpr (cyclotomic.dvd_X_pow_sub_one n ℤ)
  rw [map_sub, map_pow, AdjoinRoot.mk_X, map_one] at h
  exact sub_eq_zero.mp h


open Polynomial in
def cycUnit {n : ℕ} (hn : 0 < n) : (CycRing n)ˣ :=
  Units.ofPowEqOne (AdjoinRoot.root (cyclotomic n ℤ)) n (root_pow n) hn.ne'

open Polynomial in
theorem cycUnit_val {n : ℕ} (hn : 0 < n) : (cycUnit hn : CycRing n) = AdjoinRoot.root (cyclotomic n ℤ) := rfl

theorem cycUnit_pow {n : ℕ} (hn : 0 < n) : cycUnit hn ^ n = 1 := by
  ext
  rw [Units.val_pow_eq_pow_val, cycUnit_val, root_pow, Units.val_one]

open Polynomial in
theorem isPrimitiveRoot_map {n : ℕ} (hn : 0 < n) {K : Type} [Field K] (hK : (n : K) ≠ 0) (β : CycRing n →+* K) :
    IsPrimitiveRoot (Units.map β.toMonoidHom (cycUnit hn)) n := by
  have : NeZero (n : K) := ⟨hK⟩
  have hr : (cyclotomic n K).IsRoot (β (AdjoinRoot.root (cyclotomic n ℤ))) := by
    have h := congrArg β (AdjoinRoot.eval₂_root (cyclotomic n ℤ))
    rw [Polynomial.hom_eval₂, map_zero, RingHom.ext_int (β.comp (AdjoinRoot.of _)) (Int.castRingHom K),
      ← Polynomial.eval_map, Polynomial.map_cyclotomic_int] at h
    exact h
  rw [← IsPrimitiveRoot.coe_units_iff]
  have hv : ((Units.map β.toMonoidHom (cycUnit hn) : Kˣ) : K) = β (AdjoinRoot.root (cyclotomic n ℤ)) := by
    simp [cycUnit_val]
  rw [hv]
  exact (Polynomial.isRoot_cyclotomic_iff).mp hr

open Polynomial in
theorem exists_map_eq {n : ℕ} (hn : 0 < n) {K : Type} [Field K] {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) :
    ∃ β : CycRing n →+* K, Units.map β.toMonoidHom (cycUnit hn) = ζ := by
  have h : (cyclotomic n ℤ).eval₂ (Int.castRingHom K) (ζ : K) = 0 := by
    rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic_int]
    exact (IsPrimitiveRoot.coe_units_iff.mpr hζ).isRoot_cyclotomic hn
  refine ⟨AdjoinRoot.lift (Int.castRingHom K) (ζ : K) h, Units.ext ?_⟩
  simp [cycUnit_val]

open Polynomial in
theorem isFinite_cyc (n : ℕ) : IsFinite (spMap (algebraMap ℤ (CycRing n))) := by
  have hf : Module.Finite ℤ (CycRing n) := (AdjoinRoot.powerBasis' (cyclotomic.monic n ℤ)).finite
  dsimp only [spMap]
  rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom]
  exact RingHom.finite_algebraMap.mpr hf

theorem isUnit_natCast_of_hom {X Y : Scheme.{0}} (f : X ⟶ Y) {n : ℕ} (h : IsUnit (n : Γ(Y, ⊤))) :
    IsUnit (n : Γ(X, ⊤)) := by
  have h' := h.map f.appTop.hom
  rwa [map_natCast] at h'

theorem natCast_ne_zero_of_isUnit {K : Type} [Field K] {n : ℕ} (h : IsUnit (n : Γ(Sp K, ⊤))) : (n : K) ≠ 0 := by
  have h' := h.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
  rw [map_natCast] at h'
  exact h'.ne_zero

theorem isUnit_natCast_basicOpen (S : Scheme.{0}) (n : ℕ) :
    IsUnit (n : Γ(S.basicOpen (n : Γ(S, ⊤)), ⊤)) := by
  have h : IsUnit (n : Γ(S, S.basicOpen (n : Γ(S, ⊤)))) := by
    have h0 := S.toRingedSpace.isUnit_res_basicOpen (n : Γ(S, ⊤))
    rwa [map_natCast] at h0
  have e : (n : Γ(S.basicOpen (n : Γ(S, ⊤)), ⊤)) =
      (S.basicOpen (n : Γ(S, ⊤))).topIso.inv.hom (n : Γ(S, S.basicOpen (n : Γ(S, ⊤)))) :=
    (map_natCast _ n).symm
  rw [e]
  exact h.map _

theorem range_subset_basicOpen {S : Scheme.{0}} {K : Type} [Field K] (x : Sp K ⟶ S) {n : ℕ} (hK : (n : K) ≠ 0) :
    Set.range x ⊆ Set.range (S.basicOpen (n : Γ(S, ⊤))).ι := by
  rintro _ ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι]
  have hK' : IsUnit (n : Γ(Sp K, ⊤)) := by
    have h1 := (Ne.isUnit hK).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    rwa [map_natCast] at h1
  have hu : IsUnit (x.app ⊤ (n : Γ(S, ⊤))) := by
    rw [map_natCast]
    have h1 := hK'.map ((Sp K).presheaf.map (homOfLE (le_top : x ⁻¹ᵁ ⊤ ≤ ⊤)).op).hom
    rwa [map_natCast] at h1
  have h := Scheme.preimage_basicOpen x (n : Γ(S, ⊤))
  rw [(Sp K).basicOpen_of_isUnit hu] at h
  show y ∈ x ⁻¹ᵁ S.basicOpen (n : Γ(S, ⊤))
  rw [h]
  trivial

theorem unitOn_inj {k : Type} [CommRing k] : Function.Injective (unitOn (R := k)) := by
  intro a b h
  apply Units.ext
  have h1 := congrArg (fun u : Γ(Sp k, ⊤)ˣ => (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom (u : Γ(Sp k, ⊤))) h
  simpa [unitOn] using h1

private theorem exists_lift_of_range_subset_closure_image_finite {W U S : Scheme.{0}} (q : W ⟶ U) [IsFinite q] (f : U ⟶ S) [IsOpenImmersion f]
    {C : Set W} (hC : IsClosed C) {K : Type} [Field K] [IsAlgClosed K] (x : Sp K ⟶ U)
    (hx : Set.range (x ≫ f) ⊆ closure ((q ≫ f) '' C)) : ∃ w : Sp K ⟶ W, w ≫ q = x ∧ Set.range w ⊆ C := by
  let pt : Sp K := IsLocalRing.closedPoint K
  obtain ⟨c, hcC, hc⟩ : ∃ c ∈ C, q c = x pt := by
    have h1 : (x ≫ f) pt ∈ closure ((q ≫ f) '' C) := hx ⟨pt, rfl⟩
    have e : (q ≫ f) '' C = f '' (q '' C) := by
      ext y
      simp
    rw [e] at h1
    have h2 : x pt ∈ closure (q '' C) := by
      rw [f.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image]
      simpa [Scheme.Hom.comp_apply] using h1
    rw [(q.isClosedMap C hC).closure_eq] at h2
    exact h2
  obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback c pt hc
  have := QuasiCompact.compactSpace_of_compactSpace (pullback.snd q x)
  have hS : IsClosed ((pullback.fst q x) ⁻¹' C) := hC.preimage (pullback.fst q x).continuous
  obtain ⟨z', hz'C, hz'⟩ := hS.exists_closed_singleton ⟨z, by simpa [Set.mem_preimage, hz1] using hcC⟩
  refine ⟨pointOfClosedPoint (pullback.snd q x) z' hz' ≫ pullback.fst q x, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]
  · rintro _ ⟨a, rfl⟩
    simpa [Scheme.Hom.comp_apply] using hz'C

private theorem lift_lemma' {S : Scheme.{0}} {K : Type} [Field K] (x : Sp K ⟶ S) {n : ℕ} (hK : (n : K) ≠ 0) :
    ∃ xU : Sp K ⟶ (S.basicOpen (n : Γ(S, ⊤)) : Scheme.{0}), xU ≫ (S.basicOpen (n : Γ(S, ⊤))).ι = x :=
  ⟨_, IsOpenImmersion.lift_fac _ x (range_subset_basicOpen x hK)⟩

set_option maxHeartbeats 1000000 in
private theorem main_lemma_3 : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La], IsAbelianScheme G → 0 < n → ∃ (Z : Over S) (et : La → (Z ⟶ G)) (c : Γ(Z.left, ⊤)ˣ), IsUnit (n : Γ(Z.left, ⊤)) ∧ (∀ a a', et (a + a') = et a * et a') ∧ (∀ a, et a ^ n = 1) ∧ c ^ n = 1 ∧ (∀ (K : Type) [Field K] (h : Sp K ⟶ Z.left) (ζ : Kˣ), Units.map h.appTop.hom.toMonoidHom c = unitOn ζ → IsPrimitiveRoot ζ n) ∧ (∀ (K : Type) [Field K] (x : Sp K ⟶ S) (et' : La → (Over.mk x ⟶ G)) (ζ : Kˣ), (n : K) ≠ 0 → (∀ a a', et' (a + a') = et' a * et' a') → (∀ a, et' a ^ n = 1) → IsPrimitiveRoot ζ n → ∃ h : Over.mk x ⟶ Z, (∀ a, h ≫ et a = et' a) ∧ Units.map h.left.appTop.hom.toMonoidHom c = unitOn ζ) ∧ ∀ (C : Set Z.left), IsClosed C → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), (n : K) ≠ 0 → Set.range x ⊆ closure (Z.hom '' C) → ∃ h : Over.mk x ⟶ Z, Set.range h.left ⊆ C := by
  intro S G _ _ n La _ _ _ hG hn
  have hU : IsUnit (n : Γ(S.basicOpen (n : Γ(S, ⊤)), ⊤)) := isUnit_natCast_basicOpen S n
  have hGU : IsAbelianScheme ((Over.pullback (S.basicOpen (n : Γ(S, ⊤))).ι).obj G) :=
    Out.TLinPf.isAb_pullback _ G hG
  have hP := isGrpPullback_pullback G (S.basicOpen (n : Γ(S, ⊤))).ι
  obtain ⟨Z₀, et₀, hfin, -, hadd₀, hpow₀, huniv₀⟩ :=
    GlobalTheory.exists_finiteEtale_latticeTorsionHom _ ((Over.pullback (S.basicOpen (n : Γ(S, ⊤))).ι).obj G) n La hGU hU
  have hcyc := isFinite_cyc n
  have hp1 : IsFinite (pullback.fst (specZIsTerminal.from Z₀.left) (spMap (algebraMap ℤ (CycRing n)))) :=
    by infer_instance
  let ZU : Over (S.basicOpen (n : Γ(S, ⊤)) : Scheme.{0}) :=
    Over.mk (pullback.fst (specZIsTerminal.from Z₀.left) (spMap (algebraMap ℤ (CycRing n))) ≫ Z₀.hom)
  let r : ZU ⟶ Z₀ := Over.homMk (pullback.fst _ _)
  have hWu : IsUnit (n : Γ(ZU.left, ⊤)) := isUnit_natCast_of_hom ZU.hom hU
  refine ⟨Over.mk (ZU.hom ≫ (S.basicOpen (n : Γ(S, ⊤))).ι), fun a => GlobalTheory.ObjPull.pushEquiv hP ZU (r ≫ et₀ a),
    Units.map (GlobalTheory.LevCover.fnOn (pullback.snd (specZIsTerminal.from Z₀.left)
      (spMap (algebraMap ℤ (CycRing n))))).toMonoidHom (cycUnit hn), hWu, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a a'
    dsimp only
    rw [hadd₀, comp_mul, map_mul]
  · intro a
    dsimp only
    rw [← map_pow, ← comp_pow, hpow₀]
    simp
  · rw [← map_pow, cycUnit_pow, map_one]
  · intro K _ h ζ hζ
    obtain ⟨β, hβ⟩ := GlobalTheory.LevCover.exists_spMap (h ≫ pullback.snd _ _)
    rw [GlobalTheory.LevCover.map_fnOn _ h β hβ] at hζ
    rw [← unitOn_inj hζ]
    exact isPrimitiveRoot_map hn (natCast_ne_zero_of_isUnit (isUnit_natCast_of_hom h hWu)) β
  · intro K _ x et' ζ hK hadd hpow hζ
    obtain ⟨xU, hxU⟩ := lift_lemma' (S := S) (K := K) (n := n) x hK
    let e : Over.mk ((Over.mk xU).hom ≫ (S.basicOpen (n : Γ(S, ⊤))).ι) ⟶ Over.mk x :=
      Over.homMk (𝟙 _) (by simpa using hxU.symm)
    obtain ⟨h₀, hh₀, -⟩ := huniv₀ (Over.mk xU) (fun a => (GlobalTheory.ObjPull.pushEquiv hP _).symm (e ≫ et' a))
      (fun a a' => by rw [hadd, comp_mul, map_mul])
      (fun a => by rw [← map_pow, ← comp_pow, hpow]; simp)
    obtain ⟨β, hβ⟩ := exists_map_eq hn hζ
    let hW : Sp K ⟶ ZU.left := pullback.lift h₀.left (spMap β) (specZIsTerminal.hom_ext _ _)
    have hW1 : hW ≫ pullback.fst _ _ = h₀.left := pullback.lift_fst _ _ _
    have hW2 : hW ≫ pullback.snd _ _ = spMap β := pullback.lift_snd _ _ _
    refine ⟨Over.homMk hW ?_, ?_, ?_⟩
    · show hW ≫ (pullback.fst _ _ ≫ Z₀.hom) ≫ _ = x
      rw [← Category.assoc, ← Category.assoc, hW1, Over.w h₀]
      exact hxU
    · intro a
      apply Over.OverMorphism.ext
      have h1 := GlobalTheory.ObjPull.pushEquiv_symm_left hP _ (e ≫ et' a)
      rw [← hh₀ a] at h1
      have h2 : (e ≫ et' a).left = (et' a).left := by simp [e]
      show hW ≫ (GlobalTheory.ObjPull.pushEquiv hP ZU (r ≫ et₀ a)).left = (et' a).left
      rw [GlobalTheory.ObjPull.pushEquiv_left, ← h2, ← h1, Over.comp_left, Over.comp_left, ← hW1]
      simp only [Category.assoc]
      rfl
    · show Units.map hW.appTop.hom.toMonoidHom _ = _
      rw [GlobalTheory.LevCover.map_fnOn _ hW β hW2, hβ]
  · intro C hC K _ _ x hK hcl
    obtain ⟨xU, hxU⟩ := lift_lemma' (S := S) (K := K) (n := n) x hK
    have : IsFinite Z₀.hom := hfin
    have : IsFinite ZU.hom := by
      show IsFinite (pullback.fst (specZIsTerminal.from Z₀.left) (spMap (algebraMap ℤ (CycRing n))) ≫ Z₀.hom)
      infer_instance
    obtain ⟨w, hw, hwC⟩ := exists_lift_of_range_subset_closure_image_finite ZU.hom (S.basicOpen (n : Γ(S, ⊤))).ι hC xU
      (by rw [hxU]; exact hcl)
    refine ⟨Over.homMk w ?_, hwC⟩
    show w ≫ ZU.hom ≫ _ = x
    rw [← Category.assoc, hw, hxU]

end GlobalTheory.TorsRootParam

namespace GlobalTheory


open TorsRootParam in
theorem exists_latticeTorsionHom_primitiveRoot_param : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La], IsAbelianScheme G → 0 < n → ∃ (Z : Over S) (et : La → (Z ⟶ G)) (c : Γ(Z.left, ⊤)ˣ), IsUnit (n : Γ(Z.left, ⊤)) ∧ (∀ a a', et (a + a') = et a * et a') ∧ (∀ a, et a ^ n = 1) ∧ c ^ n = 1 ∧ (∀ (K : Type) [Field K] (h : Sp K ⟶ Z.left) (ζ : Kˣ), Units.map h.appTop.hom.toMonoidHom c = unitOn ζ → IsPrimitiveRoot ζ n) ∧ (∀ (K : Type) [Field K] (x : Sp K ⟶ S) (et' : La → (Over.mk x ⟶ G)) (ζ : Kˣ), (n : K) ≠ 0 → (∀ a a', et' (a + a') = et' a * et' a') → (∀ a, et' a ^ n = 1) → IsPrimitiveRoot ζ n → ∃ h : Over.mk x ⟶ Z, (∀ a, h ≫ et a = et' a) ∧ Units.map h.left.appTop.hom.toMonoidHom c = unitOn ζ) ∧ ∀ (C : Set Z.left), IsClosed C → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), (n : K) ≠ 0 → Set.range x ⊆ closure (Z.hom '' C) → ∃ h : Over.mk x ⟶ Z, Set.range h.left ⊆ C := by
  exact main_lemma_3

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteSchemeLatticeTorsionHomPrimitiveRootStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_scheme_latticeTorsionHom_primitiveRoot : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La], IsAbelianScheme G → 0 < n → ∃ (Z : Over S) (et : La → (Z ⟶ G)) (c : Γ(Z.left, ⊤)ˣ), IsUnit (n : Γ(Z.left, ⊤)) ∧ (∀ a a', et (a + a') = et a * et a') ∧ (∀ a, et a ^ n = 1) ∧ c ^ n = 1 ∧ (∀ (K : Type) [Field K] (h : Sp K ⟶ Z.left) (ζ : Kˣ), Units.map h.appTop.hom.toMonoidHom c = unitOn ζ → IsPrimitiveRoot ζ n) ∧ (∀ (K : Type) [Field K] (x : Sp K ⟶ S) (et' : La → (Over.mk x ⟶ G)) (ζ : Kˣ), (n : K) ≠ 0 → (∀ a a', et' (a + a') = et' a * et' a') → (∀ a, et' a ^ n = 1) → IsPrimitiveRoot ζ n → ∃ h : Over.mk x ⟶ Z, (∀ a, h ≫ et a = et' a) ∧ Units.map h.left.appTop.hom.toMonoidHom c = unitOn ζ) ∧ ∀ (C : Set Z.left), IsClosed C → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), (n : K) ≠ 0 → Set.range x ⊆ closure (Z.hom '' C) → ∃ h : Over.mk x ⟶ Z, Set.range h.left ⊆ C := by
  first | exact @GlobalTheory.exists_latticeTorsionHom_primitiveRoot_param | exact GlobalTheory.exists_latticeTorsionHom_primitiveRoot_param | (intros; apply GlobalTheory.exists_latticeTorsionHom_primitiveRoot_param <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueTorsionPointFrobeniusLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueTorsionPointFrobeniusLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TorsionTheta

theorem ptMap_comp_ptMap {O : Type} [CommRing O] {A B C : Type} [CommRing A] [Algebra O A]
    [CommRing B] [Algebra O B] [CommRing C] [Algebra O C] (φ : A →ₐ[O] B) (ψ : B →ₐ[O] C) :
    ptMap ψ ≫ ptMap φ = ptMap (ψ.comp φ) := by
  unfold ptMap
  ext1
  simp only [Over.comp_left, Over.homMk_left]
  rw [← Spec.map_comp]
  rfl

theorem tmul_one_ne_zero {O : Type} [CommRing O] [IsLocalRing O] {H : Type} [CommRing H]
    [Algebra O H] [Module.Finite O H] [Module.Free O H] (l : H)
    (hl : l ∉ (IsLocalRing.maximalIdeal O).map (algebraMap O H))
    (K : Type) [Field K] [Algebra O K] : l ⊗ₜ[O] (1 : K) ≠ 0 := by
  classical
  intro h0
  let b := Module.Free.chooseBasis O H
  have hex : ∃ i, IsUnit (b.repr l i) := by
    by_contra hne
    push Not at hne
    apply hl
    rw [← b.sum_repr l]
    refine Ideal.sum_mem _ (fun i _ => ?_)
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal _).2 (hne i)))
  obtain ⟨i, hi⟩ := hex
  have h1 := congrArg (fun x => TensorProduct.lid O K (TensorProduct.map (b.coord i) LinearMap.id x)) h0
  simp only [TensorProduct.map_tmul, TensorProduct.lid_tmul, LinearMap.id_apply, map_zero,
    Module.Basis.coord_apply] at h1
  rw [Algebra.smul_def, _root_.mul_one] at h1
  exact (hi.map (algebraMap O K)).ne_zero h1

private lemma ptMap_comp_comp {O : Type} [CommRing O] {A B C : Type} [CommRing A] [Algebra O A]
    [CommRing B] [Algebra O B] [CommRing C] [Algebra O C] {X : Over (Sp O)} (φ : A →ₐ[O] B)
    (ψ : B →ₐ[O] C) (f : specO O A ⟶ X) : ptMap (ψ.comp φ) ≫ f = ptMap ψ ≫ ptMap φ ≫ f := by
  rw [← ptMap_comp_ptMap, Category.assoc]

theorem exists_theta : ∀ (O : Type) [CommRing O] [IsLocalRing O] (G : Over (Sp O)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (H : Type) [CommRing H] [Algebra O H] [Module.Finite O H] [Module.Free O H] (y : specO O H ⟶ G), y ^ n = 1 → (∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ G), z ^ n = 1 → ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z) → ∀ (ε : H →ₐ[O] O) (l : H) (c : O), ptMap ε ≫ y = 1 → (∀ h, ε h = 0 → h * l = 0) → ε l = c → l ∉ (IsLocalRing.maximalIdeal O).map (algebraMap O H) → ∃ Θ : H ⊗[O] H, (∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ) ∧ Algebra.TensorProduct.lmul' O Θ = algebraMap O H c ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra O K], (∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O K a = 0) → ∀ ga : H →ₐ[O] K, Algebra.TensorProduct.map (AlgHom.id O H) ga Θ ≠ 0 := by
  intro O _ _ G _ _ n H _ _ _ _ y hy hU ε l c hε hann hεl hlm
  have tors : ∀ (S : Type) [CommRing S] [Algebra O S] (f : specO O S ⟶ specO O H), (f ≫ y) ^ n = 1 := by
    intro S _ _ f
    rw [← comp_pow, hy, comp_one]
  have uniq : ∀ (S : Type) [CommRing S] [Algebra O S] (φ₁ φ₂ : H →ₐ[O] S),
      ptMap φ₁ ≫ y = ptMap φ₂ ≫ y → φ₁ = φ₂ := by
    intro S _ _ φ₁ φ₂ h
    obtain ⟨φ, -, hφ⟩ := hU S (ptMap φ₂ ≫ y) (tors S _)
    exact (hφ φ₁ h).trans (hφ φ₂ rfl).symm
  let iL : H →ₐ[O] H ⊗[O] H := Algebra.TensorProduct.includeLeft
  let iR : H →ₐ[O] H ⊗[O] H := Algebra.TensorProduct.includeRight
  obtain ⟨d, hd, -⟩ := hU (H ⊗[O] H) (ptMap iL ≫ y * (ptMap iR ≫ y)⁻¹)
    (by rw [mul_pow, inv_pow, tors, tors, inv_one, _root_.mul_one])
  obtain ⟨m, hm, -⟩ := hU (H ⊗[O] H) (ptMap iL ≫ y * ptMap iR ≫ y)
    (by rw [mul_pow, tors, tors, _root_.mul_one])
  let eH : H →ₐ[O] H := (Algebra.ofId O H).comp ε
  have heH : ptMap eH ≫ y = 1 := by
    rw [ptMap_comp_comp, hε, comp_one]

  have hmd : (Algebra.TensorProduct.lmul' O : H ⊗[O] H →ₐ[O] H).comp d = eH := by
    apply uniq
    rw [ptMap_comp_comp, hd, comp_mul, GrpObj.comp_inv, ← ptMap_comp_comp, ← ptMap_comp_comp, heH]
    have h1 : (Algebra.TensorProduct.lmul' O : H ⊗[O] H →ₐ[O] H).comp iL = AlgHom.id O H := by
      ext x; simp [iL]
    have h2 : (Algebra.TensorProduct.lmul' O : H ⊗[O] H →ₐ[O] H).comp iR = AlgHom.id O H := by
      ext x; simp [iR]
    rw [h1, h2, mul_inv_cancel]
  refine ⟨d l, ?_, ?_, ?_⟩
  ·
    have hl' : ∀ a : H, a * l = algebraMap O H (ε a) * l := by
      intro a
      have := hann (a - algebraMap O H (ε a)) (by simp)
      rwa [sub_mul, sub_eq_zero] at this
    let e2 : H ⊗[O] H →ₐ[O] H := Algebra.TensorProduct.lift eH (AlgHom.id O H) (fun _ _ => Commute.all _ _)
    have hkey : ∀ x : H ⊗[O] H, x * (l ⊗ₜ[O] (1 : H)) = (l ⊗ₜ[O] (1 : H)) * ((1 : H) ⊗ₜ[O] e2 x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        simp only [e2, eH, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one,
          _root_.one_mul, hl' a, AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.id_apply]
        rw [← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.smul_tmul]
      | add x x' hx hx' => rw [add_mul, hx, hx', map_add (f := _), TensorProduct.tmul_add, mul_add]
    let ψ : H ⊗[O] H →ₐ[O] H ⊗[O] H := Algebra.TensorProduct.lift d iR (fun _ _ => Commute.all _ _)
    have hψL : ψ.comp iL = d := by ext x; simp [ψ, iL]
    have hψR : ψ.comp iR = iR := by ext x; simp [ψ, iR]
    have he2L : e2.comp iL = eH := by ext x; simp [e2, iL]
    have he2R : e2.comp iR = AlgHom.id O H := by ext x; simp [e2, iR]
    have he2m : e2.comp m = AlgHom.id O H := by
      apply uniq
      rw [ptMap_comp_comp, hm, comp_mul, ← ptMap_comp_comp, ← ptMap_comp_comp, he2L, he2R, heH, _root_.one_mul]
    have hψm : ψ.comp m = iL := by
      apply uniq
      rw [ptMap_comp_comp, hm, comp_mul, ← ptMap_comp_comp, ← ptMap_comp_comp, hψL, hψR, hd,
        inv_mul_cancel_right]
    intro h
    have a1 : h ⊗ₜ[O] (1 : H) = ψ (m h) := by
      rw [← AlgHom.comp_apply, hψm]; rfl
    have a2 : d l = ψ (l ⊗ₜ[O] (1 : H)) := by simp [ψ]
    have a3 : (1 : H) ⊗ₜ[O] h = ψ ((1 : H) ⊗ₜ[O] h) := by simp [ψ, iR]
    have a4 : e2 (m h) = h := by rw [← AlgHom.comp_apply, he2m]; rfl
    rw [a1, a2, ← map_mul, hkey, a4, map_mul, ← a3, ← a2, _root_.mul_comm]
  · have := DFunLike.congr_fun hmd l
    rw [AlgHom.comp_apply] at this
    rw [this]
    simp [eH, hεl]
  · intro K _ _ _ _ ga
    let jL : H →ₐ[O] H ⊗[O] K := Algebra.TensorProduct.includeLeft
    let jR : K →ₐ[O] H ⊗[O] K := Algebra.TensorProduct.includeRight
    let κ : H ⊗[O] H →ₐ[O] H ⊗[O] K := Algebra.TensorProduct.map (AlgHom.id O H) ga
    let Sg : H →ₐ[O] H ⊗[O] K := κ.comp m
    let MainNotions : H ⊗[O] K →ₐ[O] H ⊗[O] K := Algebra.TensorProduct.lift Sg jR (fun _ _ => Commute.all _ _)
    have hκL : κ.comp iL = jL := by ext x; simp [κ, iL, jL]
    have hκR : κ.comp iR = jR.comp ga := by ext x; simp [κ, iR, jR]
    have hSL : (MainNotions.comp κ).comp iL = Sg := by ext x; simp [MainNotions, κ, iL]
    have hSR : (MainNotions.comp κ).comp iR = jR.comp ga := by ext x; simp [MainNotions, κ, iR, jR]
    have hSg : ptMap Sg ≫ y = ptMap jL ≫ y * ptMap (jR.comp ga) ≫ y := by
      rw [ptMap_comp_comp, hm, comp_mul, ← ptMap_comp_comp, ← ptMap_comp_comp, hκL, hκR]
    have hback : (MainNotions.comp κ).comp d = jL := by
      apply uniq
      rw [ptMap_comp_comp, hd, comp_mul, GrpObj.comp_inv, ← ptMap_comp_comp, ← ptMap_comp_comp, hSL, hSR, hSg,
        mul_inv_cancel_right]
    intro h0
    apply tmul_one_ne_zero l hlm K
    have := DFunLike.congr_fun hback l
    simp only [AlgHom.comp_apply] at this
    change MainNotions (κ (d l)) = l ⊗ₜ[O] (1 : K) at this
    rw [← this]
    change MainNotions (Algebra.TensorProduct.map (AlgHom.id O H) ga (d l)) = 0
    rw [h0, map_zero]

end GlobalTheory.TorsionTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueTorsionPointFrobeniusLocalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_diagonal_element_lmul_eq_nonzero_geometric_points : ∀ (O : Type) [CommRing O] [IsLocalRing O] (G : Over (Sp O)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (H : Type) [CommRing H] [Algebra O H] [Module.Finite O H] [Module.Free O H] (y : specO O H ⟶ G), y ^ n = 1 → (∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ G), z ^ n = 1 → ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z) → ∀ (ε : H →ₐ[O] O) (l : H) (c : O), ptMap ε ≫ y = 1 → (∀ h, ε h = 0 → h * l = 0) → ε l = c → l ∉ (IsLocalRing.maximalIdeal O).map (algebraMap O H) → ∃ Θ : H ⊗[O] H, (∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ) ∧ Algebra.TensorProduct.lmul' O Θ = algebraMap O H c ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra O K], (∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O K a = 0) → ∀ ga : H →ₐ[O] K, Algebra.TensorProduct.map (AlgHom.id O H) ga Θ ≠ 0 := by
  first | exact @GlobalTheory.TorsionTheta.exists_theta | exact GlobalTheory.TorsionTheta.exists_theta | (intros; apply GlobalTheory.TorsionTheta.exists_theta <;> assumption)
end
end
