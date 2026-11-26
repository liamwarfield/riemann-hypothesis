module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechDifferentialOneInclusion
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TerminalRes
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FRiCalc
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

lemma rc_pull_comp {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {C'' : Type u''} [Category.{v''} C''] {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w} R}
    {F'' : C'' ⥤ ModuleCat.{w} R} (m : Mor F F' (RingHom.id R)) (m' : Mor F' F'' (RingHom.id R)) (n : ℕ) :
    (m.comp m' : Mor F F'' (RingHom.id R)).pull n = (m'.pull n).comp (m.pull n) :=
  LinearMap.ext fun x => (CrystallineSemistableComparison.P.pull_comp m m' n x).1

lemma rc_restrict_comp {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {C'' : Type u''} [Category.{v''} C''] (F : C ⥤ ModuleCat.{w} R) (G : C' ⥤ C) (G' : C'' ⥤ C') (n : ℕ) :
    (Mor.restrict F (G' ⋙ G)).pull n = ((Mor.restrict (G ⋙ F) G').pull n).comp ((Mor.restrict F G).pull n) :=
  rc_pull_comp (Mor.restrict F G) (Mor.restrict (G ⋙ F) G') n

lemma rc_iso_upTo {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {F F₁ : C ⥤ ModuleCat.{w} R}
    (e : F ≅ F₁) (n : ℕ) : UpTo (1 : R) ((Mor.ofNatTrans e.hom).pull n) := by
  have h := CrystallineSemistableComparison.P.coef_upTo e.hom (1 : R) (fun T => by
    refine ((CrystallineSemistableComparison.P.upTo_alg (e.hom.app T).hom LinearMap.id 1 1).2.2.2.2).2 ?_
    exact (e.app T).toLinearEquiv.bijective) n
  rwa [one_pow] at h

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.ri_calc : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C''] (F : C ⥤ ModuleCat.{w} R) (G : C' ⥤ C) (G' : C'' ⥤ C') (s s' : R) (n : ℕ), (RI s n F G → RI s' n (G ⋙ F) G' → RI (s * s') n F (G' ⋙ G)) ∧ (RI s n F G → RI s' n F (G' ⋙ G) → RI (s * s') n (G ⋙ F) G') ∧ (RI s n (G ⋙ F) G' → RI s' n F (G' ⋙ G) → RI (s * s') n F G) ∧ (RI s n F G → RI (s * s') n F G) ∧ (∀ G₁ : C' ⥤ C, (G ≅ G₁) → RI s n F G → RI s n F G₁) ∧ (G.IsEquivalence → RI 1 n F G) ∧ (∀ F₁ : C ⥤ ModuleCat.{w} R, (F ≅ F₁) → RI s n F G → RI s n F₁ G) := by
  intro R _ C _ C' _ C'' _ F G G' s s' n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h1 h2 j hj
    rw [RI, IsoLe] at *
    rw [rc_restrict_comp]
    exact (CrystallineSemistableComparison.P.upTo_alg _ _ s s').1 (h1 j hj) (h2 j hj)
  · intro h1 h2 j hj
    have := h2 j hj
    rw [rc_restrict_comp] at this
    exact (CrystallineSemistableComparison.P.upTo_alg _ _ s s').2.1 (h1 j hj) this
  · intro h1 h2 j hj
    have := h2 j hj
    rw [rc_restrict_comp] at this
    exact (CrystallineSemistableComparison.P.upTo_alg _ _ s s').2.2.1 (h1 j hj) this
  · intro h1 j hj
    exact (CrystallineSemistableComparison.P.upTo_alg ((Mor.restrict F G).pull j) LinearMap.id s s').2.2.2.1 (h1 j hj)
  · intro G₁ e h1 j hj
    have hp : (Mor.restrict F G₁).pull j =
        ((Mor.ofNatTrans (Functor.whiskerRight e.hom F)).pull j).comp ((Mor.restrict F G).pull j) := by
      rw [← rc_pull_comp]
      refine LinearMap.ext fun x => CrystallineSemistableComparison.P.prism (Mor.restrict F G₁)
        ((Mor.restrict F G).comp (Mor.ofNatTrans (Functor.whiskerRight e.hom F))) e.inv ?_ j x
      intro T x
      change (F.map (e.hom.app T)).hom ((F.map (e.inv.app T)).hom x) = x
      rw [← ModuleCat.comp_apply, ← F.map_comp, e.inv_hom_id_app, F.map_id]
      rfl
    rw [hp, ← mul_one s]
    exact (CrystallineSemistableComparison.P.upTo_alg _ _ s 1).1 (h1 j hj) (rc_iso_upTo (Functor.isoWhiskerRight e F) j)
  · intro hG j hj
    exact ((CrystallineSemistableComparison.P.upTo_alg ((Mor.restrict F G).pull j) LinearMap.id 1 1).2.2.2.2).2
      (CrystallineSemistableComparison.P.adj F G G.asEquivalence.inverse G.asEquivalence.toAdjunction j)
  · intro F₁ e h1 j hj
    have hp : (Mor.restrict F₁ G).pull j =
        ((Mor.ofNatTrans (Functor.whiskerLeft G e.hom)).pull j).comp
          (((Mor.restrict F G).pull j).comp ((Mor.ofNatTrans e.inv).pull j)) := by
      rw [← rc_pull_comp, ← rc_pull_comp]
      refine LinearMap.ext fun x => CrystallineSemistableComparison.P.prism (Mor.restrict F₁ G)
        ((Mor.ofNatTrans e.inv).comp ((Mor.restrict F G).comp (Mor.ofNatTrans (Functor.whiskerLeft G e.hom))))
        (𝟙 G) ?_ j x
      intro T x
      change (e.hom.app (G.obj T)).hom ((e.inv.app (G.obj T)).hom ((F₁.map (𝟙 (G.obj T))).hom x)) = x
      rw [F₁.map_id, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply, e.inv_hom_id_app]
      rfl
    rw [hp, ← one_mul s, ← mul_one (1 * s)]
    exact (CrystallineSemistableComparison.P.upTo_alg _ _ (1 * s) 1).1
      ((CrystallineSemistableComparison.P.upTo_alg _ _ 1 s).1 (rc_iso_upTo e.symm j) (h1 j hj))
      (rc_iso_upTo (Functor.isoWhiskerLeft G e) j)
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FResLe
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

theorem resLe_cls_zero {R : Type} [CommRing R] (K : Cx.{w} R) (n : ℕ) (a : K.X n) (ha : K.d n a = 0)
    (h : a ∈ K.B n) : K.cls a ha = 0 := ((CrystallineSemistableComparison.P.cls_surj K n).2.1 a ha).2 h

theorem resLe_cls_smul {R : Type} [CommRing R] (K : Cx.{w} R) (n : ℕ) (r : R) (a : K.X n) (ha : K.d n a = 0)
    (hb : K.d n (r • a) = 0) : K.cls (r • a) hb = r • K.cls a ha := (CrystallineSemistableComparison.P.cls_surj K n).2.2.2.2 r a ha hb

theorem eq_zero_of_mem_boundaries_zero {R : Type} [CommRing R] (K : Cx.{w} R) (a : K.X 0) (h : a ∈ K.B 0) : a = 0 :=
  (Submodule.mem_bot R).1 h

theorem resLe_succ {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R))
    (n : ℕ) (hK : ExactUpTo (1 : R) (K.d n) (K.d (n + 1))) (s : R) :
    UpTo s (φ.mapH (n + 1)) ↔ ExactUpTo s (L.d n) (L.d (n + 1)) := by
  have hz : ∀ x : K.H (n + 1), x = 0 := by
    intro x
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K (n + 1)).1 x
    obtain ⟨b, hb⟩ := hK a ha
    exact resLe_cls_zero K (n + 1) a ha ⟨b, by rw [hb, one_smul]⟩
  constructor
  · rintro ⟨-, hs⟩ y hy
    obtain ⟨x, hx⟩ := hs (L.cls y hy)
    rw [hz x, map_zero] at hx
    have hy' : L.d (n + 1) (s • y) = 0 := by rw [map_smul, hy, smul_zero]
    rw [← resLe_cls_smul L (n + 1) s y hy hy'] at hx
    have : s • y ∈ L.B (n + 1) := ((CrystallineSemistableComparison.P.cls_surj L (n + 1)).2.1 _ hy').1 hx.symm
    obtain ⟨c, hc⟩ := this
    exact ⟨c, hc⟩
  · intro h
    refine ⟨fun x _ => by rw [hz x, smul_zero], fun y => ⟨0, ?_⟩⟩
    obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj L (n + 1)).1 y
    have hb' : L.d (n + 1) (s • b) = 0 := by rw [map_smul, hb, smul_zero]
    obtain ⟨c, hc⟩ := h b hb
    rw [map_zero, ← resLe_cls_smul L (n + 1) s b hb hb']
    exact (resLe_cls_zero L (n + 1) _ hb' ⟨c, hc⟩).symm

theorem resLe_zero {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R))
    {M : Type u''} [AddCommGroup M] [Module R M] (ε : M →ₗ[R] K.X 0) (hK : K.ResUpTo 1 ε) (s : R) :
    UpTo s (φ.mapH 0) ↔ InjUpTo s (φ.f 0 ∘ₗ ε) ∧ ExactUpTo s (φ.f 0 ∘ₗ ε) (L.d 0) := by
  obtain ⟨hd, hi, he, -⟩ := hK
  have hLd : ∀ x, L.d 0 (φ.f 0 (ε x)) = 0 := fun x => by rw [φ.comm, hd, map_zero]
  constructor
  · rintro ⟨hI, hS⟩
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · have h1 : φ.mapH 0 (K.cls (ε x) (hd x)) = 0 := by
        rw [CrystallineSemistableComparison.P.mapH_cls φ 0 _ _ (hLd x)]
        exact resLe_cls_zero L 0 _ _ (by rw [show φ.f 0 (ε x) = 0 from hx]; exact Submodule.zero_mem _)
      have h2 := hI _ h1
      have hs' : K.d 0 (s • ε x) = 0 := by rw [map_smul, hd, smul_zero]
      rw [← resLe_cls_smul K 0 s _ _ hs'] at h2
      have h3 : s • ε x = 0 := eq_zero_of_mem_boundaries_zero _ _ (((CrystallineSemistableComparison.P.cls_surj K 0).2.1 _ hs').1 h2)
      rw [← map_smul] at h3
      have := hi _ h3
      rwa [one_smul] at this
    · obtain ⟨x, hx⟩ := hS (L.cls y hy)
      obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K 0).1 x
      obtain ⟨m, hm⟩ := he a ha
      rw [one_smul] at hm
      refine ⟨m, ?_⟩
      have hy' : L.d 0 (s • y) = 0 := by rw [map_smul, hy, smul_zero]
      have hfa : L.d 0 (φ.f 0 a) = 0 := by rw [φ.comm, ha, map_zero]
      rw [CrystallineSemistableComparison.P.mapH_cls φ 0 a ha hfa, ← resLe_cls_smul L 0 s y hy hy'] at hx
      have := ((CrystallineSemistableComparison.P.cls_surj L 0).2.2.1 _ _ hfa hy').1 hx
      change φ.f 0 (ε m) = s • y
      rw [hm]
      exact sub_eq_zero.1 (eq_zero_of_mem_boundaries_zero _ _ this)
  · rintro ⟨hI, hE⟩
    refine ⟨fun x hx => ?_, fun y => ?_⟩
    · obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K 0).1 x
      have hfa : L.d 0 (φ.f 0 a) = 0 := by rw [φ.comm, ha, map_zero]
      rw [CrystallineSemistableComparison.P.mapH_cls φ 0 a ha hfa] at hx
      have h0 : φ.f 0 a = 0 := eq_zero_of_mem_boundaries_zero _ _ (((CrystallineSemistableComparison.P.cls_surj L 0).2.1 _ hfa).1 hx)
      obtain ⟨m, hm⟩ := he a ha
      rw [one_smul] at hm
      have h1 : s • m = 0 := hI m (by change φ.f 0 (ε m) = 0; rw [hm, h0])
      have hs' : K.d 0 (s • a) = 0 := by rw [map_smul, ha, smul_zero]
      rw [← resLe_cls_smul K 0 s a ha hs']
      exact resLe_cls_zero K 0 _ hs' (by rw [← hm, ← map_smul, h1, map_zero]; exact Submodule.zero_mem _)
    · obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj L 0).1 y
      obtain ⟨m, hm⟩ := hE b hb
      refine ⟨K.cls (ε m) (hd m), ?_⟩
      have hb' : L.d 0 (s • b) = 0 := by rw [map_smul, hb, smul_zero]
      rw [CrystallineSemistableComparison.P.mapH_cls φ 0 _ _ (hLd m), ← resLe_cls_smul L 0 s b hb hb']
      exact ((CrystallineSemistableComparison.P.cls_surj L 0).2.2.1 _ _ _ hb').2 (by
        rw [show φ.f 0 (ε m) = s • b from hm, sub_self]; exact Submodule.zero_mem _)

theorem resLe_cx {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R))
    {M : Type u''} [AddCommGroup M] [Module R M] (ε : M →ₗ[R] K.X 0) (hK : K.ResUpTo 1 ε) (s : R) :
    L.ResUpTo s (φ.f 0 ∘ₗ ε) ↔ ∀ n, UpTo s (φ.mapH n) := by
  have hd : ∀ x, L.d 0 ((φ.f 0 ∘ₗ ε) x) = 0 := fun x => by
    change L.d 0 (φ.f 0 (ε x)) = 0
    rw [φ.comm, hK.1, map_zero]
  constructor
  · rintro ⟨-, hi, he, hn⟩ n
    cases n with
    | zero => exact (resLe_zero φ ε hK s).2 ⟨hi, he⟩
    | succ n => exact (resLe_succ φ n (hK.2.2.2 n) s).2 (hn n)
  · intro h
    obtain ⟨hi, he⟩ := (resLe_zero φ ε hK s).1 (h 0)
    exact ⟨hd, hi, he, fun n => (resLe_succ φ n (hK.2.2.2 n) s).1 (h (n + 1))⟩

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.res_le : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] (F : C ⥤ ModuleCat.{w} R) (F' : C' ⥤ ModuleCat.{w'} R) (m : Mor F F' (RingHom.id R)) (T₀ : C) (h : Limits.IsInitial T₀) (s : R), ((cx F').ResUpTo s (aug F' fun T => (m.τ T) ∘ₗ (F.map (h.to _)).hom) ↔ ∀ n, UpTo s (m.pull n)) := by
  intro R _ C _ C' _ F F' m T₀ h s
  have e : (aug F' fun T => (m.τ T) ∘ₗ (F.map (h.to _)).hom) = m.hom.f 0 ∘ₗ aug F fun T => (F.map (h.to T)).hom := by
    apply LinearMap.ext; intro x; funext c; rfl
  rw [e]
  exact CrystallineSemistableComparison.B.resLe_cx m.hom _ (CrystallineSemistableComparison.P.initial F T₀ h) s
end
