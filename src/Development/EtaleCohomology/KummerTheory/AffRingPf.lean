module

public import Development.EtaleCohomology.KummerTheory.BockCut

@[expose] public section

section -- merged from Development.EtaleCohomology.KummerTheory.AffRingPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.KummerTheory.AffRingPf

variable {X : Scheme.{0}} [IsAffine X] {R : CommRingCat.{0}} (p : X ⟶ Spec R)

def phi : R ⟶ Γ(X, ⊤) := Spec.preimage (X.isoSpec.inv ≫ p)

def Tf : Under R ⥤ CommRingCat.{0} := Under.pushout (phi p) ⋙ Under.forget _

theorem isPb (A : Under R) :
    IsPullback (Spec.map (pushout.inr A.hom (phi p)) ≫ X.isoSpec.inv) (Spec.map (pushout.inl A.hom (phi p)))
      p (Spec.map A.hom) := by
  have h := (isPullback_SpecMap_pushout A.hom (phi p)).flip
  refine IsPullback.of_iso h (Iso.refl _) X.isoSpec.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp [phi]
  · simp

def eIso (A : Under R) : Spec (pushout A.hom (phi p)) ≅ pullback p (Spec.map A.hom) := (isPb p A).isoPullback

theorem eIso_fst (A : Under R) : (eIso p A).hom ≫ pullback.fst _ _ =
    Spec.map (pushout.inr A.hom (phi p)) ≫ X.isoSpec.inv :=
  (isPb p A).isoPullback_hom_fst

theorem eIso_snd (A : Under R) : (eIso p A).hom ≫ pullback.snd _ _ =
    Spec.map (pushout.inl A.hom (phi p)) :=
  (isPb p A).isoPullback_hom_snd

def tmap {A B : Under R} (h : A ⟶ B) : pushout A.hom (phi p) ⟶ pushout B.hom (phi p) :=
  pushout.desc (h.right ≫ pushout.inl B.hom (phi p)) (pushout.inr B.hom (phi p))
    (by rw [← Category.assoc, Under.w h, pushout.condition])

theorem nat {A B : Under R} (h : A ⟶ B) :
    (eIso p B).hom ≫ bcMap p A.hom B.hom h.right (Under.w h) = Spec.map (tmap p h) ≫ (eIso p A).hom := by
  have e1 : pushout.inr A.hom (phi p) ≫ tmap p h = pushout.inr B.hom (phi p) := pushout.inr_desc _ _ _
  have e2 : pushout.inl A.hom (phi p) ≫ tmap p h = h.right ≫ pushout.inl B.hom (phi p) := pushout.inl_desc _ _ _
  apply pullback.hom_ext
  · simp only [bcMap, pullback.map, Category.assoc, pullback.lift_fst, Category.comp_id, eIso_fst]
    rw [← e1, Spec.map_comp, Category.assoc]
  · simp only [bcMap, pullback.map, Category.assoc, pullback.lift_snd, eIso_snd]
    rw [← Category.assoc, eIso_snd, ← Spec.map_comp, ← e2, Spec.map_comp]

theorem AffRing_of : LateralTheory.KummerTheory.ContCut.AffRing := by
  intro X _ R p
  refine ⟨Tf p, ⟨NatIso.ofComponents (fun A => (eIso p A).op) ?_⟩, fun A => ⟨A.hom ≫ pushout.inl A.hom (phi p)⟩, ?_⟩
  · intro A B h
    exact Quiver.Hom.unop_inj (nat p h)
  · intro J _ _ D c hc
    have : IsConnected J := IsFiltered.isConnected J
    have hc' : IsColimit c := isColimitOfReflects (Under.forget R) hc
    let _ : PreservesColimitsOfSize.{0, 0} (Under.pushout (phi p)) :=
      (Under.mapPushoutAdj (phi p)).leftAdjoint_preservesColimits
    have : PreservesColimit D (Tf p) :=
      inferInstanceAs (PreservesColimit D (Under.pushout (phi p) ⋙ Under.forget _))
    exact ⟨isColimitOfPreserves (Tf p) hc'⟩

end LateralTheory.KummerTheory.AffRingPf
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.RedExPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.RedExPf
open LateralTheory.KummerTheory.BockCut

theorem nsmul_congr {q : ℕ} {i : ℤ} {U : Scheme.{0}} (y : Sec (tw q i) U) {n m : ℕ}
    (h : (n : ZMod q) = (m : ZMod q)) : n • y = m • y := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) n y, ← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) m y]
  congr 1
  exact ULift.ext (by simpa using h)

theorem RedEx_of (hZ : ZHom) (hT : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated) (hP : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities) : RedEx := by
  intro Q q _ h i
  have hq : NeZero q := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne Q) h⟩
  choose ρ hρ using fun (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) => (hP Q Γ(U, ⊤)).2.2.2.2.2 q h ζ
  let M : Shv (ZMod Q) := (restr (ZMod.castHom h (ZMod q))).obj (tw q i)
  let e : ∀ U : Scheme.{0}, Prim Q Γ(U, ⊤) → Sec M U := fun U ζ => (twGen i (ρ U ζ) : Sec (tw q i) U)
  have he1 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom) := by
    intro V U g ζ
    have hx : ρ V (ζ.map g.appTop.hom) = (ρ U ζ).map g.appTop.hom := by
      apply Subtype.ext
      rw [hρ]
      show (g.appTop.hom ζ.1) ^ (Q / q) = g.appTop.hom ((ρ U ζ).1)
      rw [hρ, map_pow]
    show Sec.res (F := tw q i) g (twGen i (ρ U ζ)) = twGen i (ρ V (ζ.map g.appTop.hom))
    rw [hx, (hT q i).2.2.2.1]
  have he2 : ∀ (U : Scheme.{0}) (ζ ξ : Prim Q Γ(U, ⊤)) (a : (ZMod Q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod Q).val →
      e U ξ = ((a ^ i : (ZMod Q)ˣ) : ZMod Q).val • e U ζ := by
    intro U ζ ξ a hξa
    let b : (ZMod q)ˣ := ZMod.unitsMap h a
    have hb : ∀ x : ZMod Q, ((ZMod.castHom h (ZMod q) x : ZMod q)) = (x.val : ZMod q) := fun x =>
      ZMod.cast_eq_val x
    have hpow : (ρ U ξ).1 = (ρ U ζ).1 ^ (b : ZMod q).val := by
      have h1 : (ρ U ζ).1 ^ q = 1 := (hP q Γ(U, ⊤)).1 (ρ U ζ)
      have hbv : (b : ZMod q).val = (a : ZMod Q).val % q := by
        show (ZMod.castHom h (ZMod q) (a : ZMod Q)).val = _
        rw [hb, ZMod.val_natCast]
      rw [hρ, hρ, hξa, hbv, ← pow_mul, mul_comm, pow_mul]
      conv_lhs => rw [← Nat.div_add_mod (a : ZMod Q).val q]
      rw [hρ] at h1
      rw [pow_add, pow_mul, h1, one_pow, one_mul]
    show twGen i (ρ U ξ) = _ • (twGen i (ρ U ζ) : Sec (tw q i) U)
    rw [(hT q i).2.2.2.2.1 U (ρ U ζ) (ρ U ξ) b hpow]
    apply nsmul_congr
    rw [ZMod.natCast_zmod_val]
    have : ((b ^ i : (ZMod q)ˣ) : ZMod q) = ZMod.castHom h (ZMod q) ((a ^ i : (ZMod Q)ˣ) : ZMod Q) := by
      rw [show b ^ i = ZMod.unitsMap h (a ^ i) from (map_zpow _ _ _).symm]
      rfl
    rw [this, hb]
  obtain ⟨φ, hφ, -⟩ := (hT Q i).2.2.2.2.2 M e he1 he2
  obtain ⟨π, hπ⟩ := hZ (TZ Q i) (TZ q i)
    (fun U => AddMonoidHom.mk' (fun a => (Sec.map φ (show Sec (tw Q i) U from a) : Sec (tw q i) U))
      (fun a b => map_add (φ.hom.app (op U)).hom a b))
    (fun V U g a => by
      have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (φ.hom.naturality g.op)) a
      exact this.symm)
  refine ⟨π, fun U ζ ξ hξ => ?_⟩
  rw [hπ]
  have hx : ξ = ρ U ζ := Subtype.ext (by rw [hξ, hρ])
  subst hx
  exact hφ U ζ

end LateralTheory.KummerTheory.RedExPf
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.RedEpiPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.RedEpiPf
open LateralTheory.KummerTheory.BockCut

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (y : Sec F U) : Sec.res (k ≫ g) y = Sec.res k (Sec.res g y) := by
  simp [Sec.res]

theorem sec_TZ_eq_zero {q : ℕ} (hq : q = 1) (i : ℤ) {V : Scheme.{0}} (x : Sec (TZ q i) V) : x = 0 := by
  subst hq
  have : Subsingleton (Sec (tw 1 i) V) := Module.subsingleton (ULift.{1} (ZMod 1)) _
  exact Subsingleton.elim (α := Sec (tw 1 i) V) x 0

theorem RedEpi_of (h_tw : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated) (h_pb : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities)
    (h_pl : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally) (h_me : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria)
    (h_lb : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure) : LateralTheory.KummerTheory.BockCut.RedEpi := by
  intro l _ c a hac i π hπ
  obtain ⟨hall, hmono, -, -, htrans, -, -⟩ := h_lb
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ a) := ⟨pow_ne_zero _ hl0⟩
  have : NeZero (l ^ c) := ⟨pow_ne_zero _ hl0⟩
  refine ((h_me ℤ π).2.2.1).2 ?_
  intro U y
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · apply hall
    intro V g
    exact ⟨0, (sec_TZ_eq_zero (pow_zero l) i _).trans (sec_TZ_eq_zero (pow_zero l) i _).symm⟩
  · suffices key : ∀ y' : Sec (tw (l ^ a) i) U, Loc U fun V g =>
        ∃ x : Sec (TZ (l ^ c) i) V, Sec.map π x = (Sec.res (F := tw (l ^ a) i) g y' : Sec (tw (l ^ a) i) V) from key y
    clear y
    intro y
    apply htrans
    refine hmono _ _ _ ((h_tw (l ^ a) i).1 U y) ?_
    intro V g hd
    rcases hd with h0 | ⟨ξ, d, hξ⟩
    · apply hall
      intro W k
      refine ⟨0, ?_⟩
      have e1 : Sec.res (F := tw (l ^ a) i) (k ≫ g) y = 0 := by
        rw [res_comp, h0]
        exact map_zero ((tw (l ^ a) i).obj.map k.op).hom
      have e2 : Sec.map π (0 : Sec (TZ (l ^ c) i) W) = 0 := map_zero (π.hom.app (op W)).hom
      exact e2.trans e1.symm
    · have hla : IsUnit ((l : Γ(V, ⊤)) ^ a) := by simpa using ξ.2.1
      have hl : IsUnit (l : Γ(V, ⊤)) := (isUnit_pow_iff ha.ne').1 hla
      have hlc : IsUnit ((l ^ c : ℕ) : Γ(V, ⊤)) := by simpa using hl.pow c
      apply htrans
      refine hmono _ _ _ ((h_pl (l ^ c) V).1 hlc) ?_
      rintro W k ⟨ζ⟩
      obtain ⟨ζ', hζ'⟩ := (h_pb (l ^ c) Γ(W, ⊤)).2.2.2.2.2 (l ^ a) (pow_dvd_pow l hac) ζ
      refine hmono _ _ _ ((h_tw (l ^ a) i).2.1 W ζ' (Sec.res (F := tw (l ^ a) i) k (Sec.res (F := tw (l ^ a) i) g y))) ?_
      rintro W' k' ⟨e, he⟩
      beta_reduce
      refine ⟨e • genZ i (ζ.map k'.appTop.hom), ?_⟩
      have hr : (ζ'.map k'.appTop.hom).1 = (ζ.map k'.appTop.hom).1 ^ (l ^ c / l ^ a) := by
        show k'.appTop.hom ζ'.1 = (k'.appTop.hom ζ.1) ^ _
        rw [hζ', map_pow]
      have e3 : Sec.res (F := tw (l ^ a) i) ((k' ≫ k) ≫ g) y = e • twGen i (ζ'.map k'.appTop.hom) := by
        rw [res_comp, res_comp, he]
      have e4 : Sec.map π (e • genZ i (ζ.map k'.appTop.hom)) = e • genZ i (ζ'.map k'.appTop.hom) :=
        (map_nsmul (π.hom.app (op W')).hom e _).trans (congrArg (fun z => e • z) (hπ W' _ _ hr))
      exact e4.trans e3.symm

end LateralTheory.KummerTheory.RedEpiPf
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.PlacePfVal
noncomputable section
open GlobalTheory.EtC Polynomial

namespace LateralTheory.KummerTheory.ValAICPf

variable {K : Type} [Field K] [IsAlgClosed K] (T : ValuationSubring K)

theorem mem_of_root (p : T[X]) (hp : p.Monic) (r : K) (hr : (p.map (algebraMap T K)).eval r = 0) : r ∈ T := by
  have hi : IsIntegral T r := ⟨p, hp, by rwa [eval_map] at hr⟩
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := T) (K := K)).mp hi
  rw [← hy]; exact y.2

theorem aic : AIC T := by
  intro p hp hd
  have hd' : (p.map (algebraMap T K)).degree ≠ 0 := by
    rw [degree_map_eq_of_injective (IsFractionRing.injective T K)]
    intro h; rw [degree_eq_natDegree hp.ne_zero] at h; norm_cast at h; omega
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root _ hd'
  have hrT := mem_of_root T p hp r hr
  refine ⟨⟨r, hrT⟩, ?_⟩
  apply IsFractionRing.injective T K
  rw [map_zero, ← eval₂_hom, ← eval_map]
  exact hr

theorem prod_lt (s : Multiset K) (hs : ∀ r ∈ s, T.valuation r ≤ 1) (h : T.valuation s.prod < 1) :
    ∃ r ∈ s, T.valuation r < 1 := by
  by_contra hc
  push_neg at hc
  have : T.valuation s.prod = 1 := by
    rw [map_multiset_prod]
    apply Multiset.prod_eq_one
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
    exact le_antisymm (hs r hr) (hc r hr)
  rw [this] at h; exact lt_irrefl _ h

theorem hens : HenselianLocalRing T where
  is_henselian := by
    intro f hf a₀ h₁ _
    set q := f.map (algebraMap T K)
    have he : (algebraMap T K) (f.eval a₀) = (q.roots.map (fun r => (a₀ : K) - r)).prod := by
      rw [← eval₂_hom, ← eval_map]
      exact (IsAlgClosed.splits q).eval_eq_prod_roots_of_monic (hf.map _) _
    have hmem : ∀ r ∈ q.roots, r ∈ T := fun r hr =>
      mem_of_root T f hf r ((mem_roots (hf.map _).ne_zero).mp hr)
    have hlt : T.valuation (q.roots.map (fun r => (a₀ : K) - r)).prod < 1 := by
      rw [← he]; exact (T.valuation_lt_one_iff _).mp h₁
    obtain ⟨x, hx, hxv⟩ := prod_lt T _ (by
      intro x hx
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
      exact (T.valuation_le_one_iff _).mpr (T.sub_mem a₀.2 (hmem r hr))) hlt
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
    refine ⟨⟨r, hmem r hr⟩, ?_, ?_⟩
    · have h0 := (mem_roots (hf.map _).ne_zero).mp hr
      apply IsFractionRing.injective T K
      rw [map_zero, ← eval₂_hom, ← eval_map]
      exact h0
    · rw [T.valuation_lt_one_iff]
      have hc : (((⟨r, hmem r hr⟩ : T) - a₀ : T) : K) = -((a₀ : K) - r) := by push_cast; ring
      rw [hc, Valuation.map_neg]
      exact hxv

end LateralTheory.KummerTheory.ValAICPf

theorem LateralTheory.KummerTheory.ValAIC_of : LateralTheory.KummerTheory.ValAIC := fun K _ _ T => ⟨LateralTheory.KummerTheory.ValAICPf.aic T, LateralTheory.KummerTheory.ValAICPf.hens T⟩

theorem LateralTheory.KummerTheory.Place_of_ex (h : LateralTheory.KummerTheory.PlaceEx) : LateralTheory.KummerTheory.Place :=
  LateralTheory.KummerTheory.Place_of h LateralTheory.KummerTheory.ValAIC_of
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.MVnatPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.MVnatPf

open LateralTheory.KummerTheory.ContCut

theorem res_res {R : Type} [CommRing R] {F : Shv R} {A B C : Scheme.{0}} (g₁ : A ⟶ B) (g₂ : B ⟶ C) (x : Sec F C) :
    Sec.res g₁ (Sec.res g₂ x) = Sec.res (g₁ ≫ g₂) x := by
  show _ = (F.obj.map (g₁ ≫ g₂).op).hom x
  rw [op_comp, Functor.map_comp]
  rfl

theorem map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {A B : Scheme.{0}} (g : A ⟶ B) (x : Sec F B) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  show ((F.obj.map g.op) ≫ φ.hom.app (op A)).hom x = (φ.hom.app (op B) ≫ G.obj.map g.op).hom x
  rw [φ.hom.naturality]

theorem conn_pull (hD : Dict) {R : Type} [CommRing R] (F : Shv R) {W U V X W' U' V' X' : Scheme.{0}}
    (a : W ⟶ U) (f : U ⟶ X) (g : V ⟶ X) (a' : W' ⟶ U') (f' : U' ⟶ X') (g' : V' ⟶ X')
    (hw : W' ⟶ W) (hu : U' ⟶ U) (hv : V' ⟶ V) (hx : X' ⟶ X)
    (ea : a' ≫ hu = hw ≫ a) (ef : f' ≫ hx = hu ≫ f) (eg : g' ≫ hx = hv ≫ g) (n : ℤ) w x
    (h : Conn F a f g n w x) :
    Conn F a' f' g' n (pull R (sch.map hw) F n w) (pull R (sch.map hx) F (n + 1) x) := by
  obtain ⟨s, z, hs, hz, e1, e2⟩ := h
  refine ⟨Sec.res hu s, Sec.res hx z, ?_, ?_, ?_, ?_⟩
  · have := (hD R (res R F) W n).2.2.2.2 hw w _ hs
    rw [res_res, ea, ← res_res]
    exact this
  · exact (hD R (res R F) X (n + 1)).2.2.2.2 hx x _ hz
  · rw [res_res, ef, ← res_res, e1, map_res]
  · rw [res_res, eg, ← res_res, e2]
    exact map_zero _

theorem unop_nat {K : Type 1} [Category.{0} K] {A B : K ⥤ Scheme.{0}ᵒᵖ} (φ : A ⟶ B) {k k' : K} (h : k ⟶ k') :
    (φ.app k').unop ≫ (A.map h).unop = (B.map h).unop ≫ (φ.app k).unop := by
  have := congrArg Quiver.Hom.unop (φ.naturality h)
  rw [unop_comp, unop_comp] at this
  exact this

theorem MVnat_of (hD : Dict) (hΔ : Delta) (hE : Exact) : MVnat := by
  intro R _ F K _ X U V W f g a b hM
  have dk : ∀ (n : ℤ) (k : K), ∃ δ : H R (sch.obj (W.obj k).unop) F n →+ H R (sch.obj (X.obj k).unop) F (n + 1),
      ∀ w x, Conn F (a.app k).unop (f.app k).unop (g.app k).unop n w x ↔ δ w = x :=
    fun n k => hΔ R F _ _ _ _ (hM k) n
  choose δ hδ using dk
  refine ⟨{
    f := fun n => Functor.whiskerRight f (Hf F n)
    g := fun n => Functor.whiskerRight g (Hf F n)
    a := fun n => Functor.whiskerRight a (Hf F n)
    b := fun n => Functor.whiskerRight b (Hf F n)
    δ := fun n =>
      { app := fun k => AddCommGrpCat.ofHom (δ n k)
        naturality := fun k k' h => by
          apply AddCommGrpCat.hom_ext
          ext w
          show δ n k' (pull R (sch.map (W.map h).unop) F n w) = pull R (sch.map (X.map h).unop) F (n + 1) (δ n k w)
          exact (hδ n k' _ _).1 (conn_pull hD F _ _ _ _ _ _ _ _ _ _ (unop_nat a h) (unop_nat f h) (unop_nat g h) n _ _
            ((hδ n k _ _).2 rfl)) }
    comm := fun n => by
      ext k : 2
      simp only [NatTrans.comp_app, Functor.whiskerRight_app]
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      apply Quiver.Hom.unop_inj
      rw [unop_comp, unop_comp]
      exact (hM k).2.2.1.w
    exUV := fun n k u v h => (hE R F _ _ _ _ (hM k) n).1 u v h
    exX := fun n k x h1 h2 => by
      obtain ⟨w, hw⟩ := (hE R F _ _ _ _ (hM k) n).2.1 x h1 h2
      exact ⟨w, (hδ n k w x).1 hw⟩
    exW := fun n k w => (hδ n k w 0).symm.trans ((hE R F _ _ _ _ (hM k) n).2.2 w) }⟩

end LateralTheory.KummerTheory.MVnatPf

end
end

section -- merged from Development.EtaleCohomology.KummerTheory.SemiUniqPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.SemiUniqPf

theorem cpush_homotopy {R : Type} [CommRing R] (K : Cx R) {I J : Cx R} {f g : I ⟶ J} (ho : Homotopy f g) (n : ℤ)
    (x : CohomologyClass K I n) : cpush K f n x = cpush K g n x := by
  obtain ⟨a, rfl⟩ := x.mk_surjective
  rw [cpost_mk, cpost_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨a.1.comp (Cochain.ofHomotopy ho) (by omega), ?_⟩
  rw [δ_comp _ _ _ (n + 1) 0 n (by omega) (by omega) (by omega), δ_ofHomotopy, Cocycle.δ_eq_zero]
  ext p q hpq
  simp [zcomp, Cochain.comp_sub]

theorem secMap_comp {R : Type} [CommRing R] {F G M : Shv R} (f : F ⟶ G) (g : G ⟶ M) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (f ≫ g) a = Sec.map g (Sec.map f a) := rfl

theorem factor (hZ : LateralTheory.KummerTheory.BockCut.ZHom) (hME : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria) {S : Type} [CommRing S]
    {I : Cx S} {T J : Cx ℤ} (σ : SemiMap I T) (hσ : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (σ.app U s))
    (κ : SemiMap I J) : ∃ u : T ⟶ J, ∀ (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U),
      κ.app U s a = Sec.map (u.f s) (σ.app U s a) := by
  let e : ∀ (U : Scheme.{0}) (s : ℤ), Sec (I.X s) U ≃+ Sec (T.X s) U :=
    fun U s => AddEquiv.ofBijective (σ.app U s) (hσ U s)
  have he : ∀ U s a, e U s a = σ.app U s a := fun _ _ _ => rfl
  have hu : ∀ s, ∃ φ : T.X s ⟶ J.X s, ∀ (U : Scheme.{0}) (b : Sec (T.X s) U),
      Sec.map φ b = κ.app U s ((e U s).symm b) := by
    intro s
    refine hZ _ _ (fun U => (κ.app U s).comp (e U s).symm.toAddMonoidHom) ?_
    intro V U g b
    obtain ⟨a, rfl⟩ := (e U s).surjective b
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply]
    rw [κ.nat]
    congr 1
    apply (e V s).injective
    rw [AddEquiv.apply_symm_apply, he, he, σ.nat]
  choose φ hφ using hu
  refine ⟨{ f := φ, comm' := ?_ }, ?_⟩
  · intro s t _
    refine (hME ℤ (φ s ≫ J.d s t)).2.2.2 (T.d s t ≫ φ t) ?_
    intro U b
    obtain ⟨a, rfl⟩ := (e U s).surjective b
    rw [secMap_comp, secMap_comp, hφ, AddEquiv.symm_apply_apply, κ.comm, he, σ.comm, hφ, ← he,
      AddEquiv.symm_apply_apply]
  · intro U s a
    show κ.app U s a = Sec.map (φ s) (σ.app U s a)
    rw [hφ, ← he, AddEquiv.symm_apply_apply]

theorem SemiUniq_of (hRR : LateralTheory.KummerTheory.BockCut.RestrRes) (hZ : LateralTheory.KummerTheory.BockCut.ZHom)
    (hOC : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapCompCompatible) (hEH : LateralTheory.EtaleFoundations.EtaleKInjectiveHomExtendsAlongQuasiIso)
    (hRB : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) (hME : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria) :
    LateralTheory.KummerTheory.BockCut.SemiUniq := by
  intro S _ F G ρ ρ' hρ E n x
  obtain ⟨T, σ, ε, hε, hσ, hσε⟩ := hRR ℤ S (Int.castRingHom S) F
  obtain ⟨u, hu⟩ := factor hZ hME σ hσ ρ
  obtain ⟨u', hu'⟩ := factor hZ hME σ hσ ρ'
  obtain ⟨hK, -, hGE, -⟩ := hRB ℤ G
  have heq : ε ≫ u = ε ≫ u' := by
    apply HomologicalComplex.from_single_hom_ext
    refine (hME ℤ _).2.2.2 _ ?_
    intro U b
    let ι := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((restr (Int.castRingHom S)).obj F)
    have hb : b = Sec.map (sglι _) (Sec.map ι.hom b) := by
      rw [← secMap_comp]; exact (congrArg (fun f => Sec.map f b) ι.hom_inv_id).symm
    have h1 := hσε U (Sec.map ι.hom b)
    dsimp only at h1
    rw [hb]
    change Sec.map (u.f 0) (Sec.map (ε.f 0) (Sec.map (sglι _) (Sec.map ι.hom b))) =
      Sec.map (u'.f 0) (Sec.map (ε.f 0) (Sec.map (sglι _) (Sec.map ι.hom b)))
    rw [h1, ← hu, ← hu']
    exact hρ U _
  obtain ⟨ho⟩ := (hEH ℤ _ T (res ℤ G) ε).2 u u' heq
  rw [(hOC S ℤ σ ρ u hu).1 E n x, (hOC S ℤ σ ρ' u' hu').1 E n x]
  exact cpush_homotopy _ ho n _

end LateralTheory.KummerTheory.SemiUniqPf
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.TwSESPf
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.TwSESPf
open LateralTheory.KummerTheory.BockCut

theorem smap_add {R : Type} [CommRing R] {F G : Shv R} (f g : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f + g) x = Sec.map f x + Sec.map g x := by
  show ((f+g).hom.app (op U)).hom x = (f.hom.app (op U)).hom x + (g.hom.app (op U)).hom x
  simp

theorem smap_zero {R : Type} [CommRing R] {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (0 : F ⟶ G) x = 0 := by
  show ((0 : F ⟶ G).hom.app (op U)).hom x = 0
  simp

theorem smap_nsmul {R : Type} [CommRing R] {F G : Shv R} (f : F ⟶ G) (n : ℕ) {U : Scheme.{0}}
    (x : Sec F U) : Sec.map (n • f) x = n • Sec.map f x := by
  induction n with
  | zero => simp [smap_zero]
  | succ n ih => rw [succ_nsmul, smap_add, ih, succ_nsmul]

theorem smap_comp {R : Type} [CommRing R] {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) {U : Scheme.{0}}
    (x : Sec F U) : Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem smap_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (𝟙 F) x = x := rfl

theorem sres_zero {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) :
    Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem smap_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  show (φ.hom.app (op V)).hom ((F.obj.map g.op).hom x) = (G.obj.map g.op).hom ((φ.hom.app (op U)).hom x)
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

theorem tz_kill (q : ℕ) (i : ℤ) {U : Scheme.{0}} (y : Sec (TZ q i) U) : q • y = 0 := by
  change q • (show ((tw q i).obj.obj (op U) : ModuleCat (ULift (ZMod q))) from y) = 0
  rw [← Nat.cast_smul_eq_nsmul (ULift (ZMod q))]
  have : ((q : ℕ) : ULift (ZMod q)) = 0 := by ext; simp
  rw [this, zero_smul]

theorem TwSES_of (hEpi : RedEpi) (hKer : RedKer) (hME : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria)
    (hEx : LateralTheory.EtaleFoundations.EtaleSheafShortComplexExactIffLocallyLifts) (hL : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure) : TwSES := by
  intro l _ b a i π₁ π₂ h₁ h₂
  have : NeZero (l ^ (b + a)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : Epi π₁ := hEpi l (b + a) a (by omega) i π₁ h₁
  have : Epi π₂ := hEpi l (b + a) b (by omega) i π₂ h₂
  have hm1 : l ^ (b + a) = l ^ b * l ^ a := pow_add _ _ _
  have hm2 : l ^ (b + a) = l ^ a * l ^ b := by rw [pow_add, mul_comm]
  have hk : kernel.ι π₁ ≫ (l ^ b • 𝟙 _) = 0 := by
    refine ((hME ℤ (kernel.ι π₁ ≫ (l ^ b • 𝟙 _))).2.2.2 0 fun U x => ?_)
    rw [smap_zero, smap_comp, smap_nsmul, smap_id]
    exact ((hKer _ _ _ hm1 i π₁ h₁ U _).1).1 (by rw [← smap_comp, kernel.condition, smap_zero])
  let ι := Abelian.epiDesc π₁ (l ^ b • 𝟙 _) hk
  have hι : π₁ ≫ ι = l ^ b • 𝟙 _ := Abelian.comp_epiDesc _ _ _
  have hιs : ∀ {U : Scheme.{0}} (y : Sec (TZ (l ^ (b + a)) i) U), Sec.map ι (Sec.map π₁ y) = l ^ b • y := by
    intro U y; rw [← smap_comp, hι, smap_nsmul, smap_id]
  have w : ι ≫ π₂ = 0 := by
    rw [← cancel_epi π₁, ← Category.assoc, hι, comp_zero]
    refine ((hME ℤ _).2.2.2 0 fun U y => ?_)
    rw [smap_zero, smap_comp, smap_nsmul, smap_id]
    refine ((hKer _ _ _ hm2 i π₂ h₂ U _).1).2 ?_
    rw [smul_smul, ← hm2]; exact tz_kill _ _ _
  refine ⟨ι, hι, w, ?_⟩
  have : Mono ι := by
    refine (hME ℤ ι).2.1.2 fun U x hx => ?_
    refine hL.2.1 _ _ _ ((hME ℤ π₁).2.2.1.1 ‹_› U x) fun V g ⟨y, hy⟩ => ?_
    rw [← hy]
    refine ((hKer _ _ _ hm1 i π₁ h₁ V y).1).2 ?_
    rw [← hιs, hy, smap_res, hx, sres_zero]
  refine ShortComplex.ShortExact.mk' ?_ ‹Mono ι› ‹Epi π₂›
  refine (hEx ℤ _).2 fun U y hy => ?_
  refine hL.2.1 _ _ _ ((hKer _ _ _ hm2 i π₂ h₂ U y).2 hy) fun V g ⟨x, hx⟩ => ⟨Sec.map π₁ x, ?_⟩
  show Sec.map ι (Sec.map π₁ x) = _
  rw [hιs, hx]

end LateralTheory.KummerTheory.TwSESPf
end

section -- merged from Development.EtaleCohomology.KummerTheory.ISupFinSuccEq
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.KummerTheory.IndPf

open LateralTheory.KummerTheory.ContCut

theorem isMV_opens {Y : Scheme.{0}} (U V : Y.Opens) (h : U ⊔ V = ⊤) :
    IsMV (Y.homOfLE inf_le_left) (Y.homOfLE inf_le_right) U.ι V.ι := by
  refine ⟨inferInstance, inferInstance, isPullback_opens_inf U V, fun x => ?_⟩
  rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
  have hx : x ∈ (U ⊔ V) := by rw [h]; trivial
  exact hx

theorem inf_affine {Y : Scheme.{0}} {R : CommRingCat.{0}} (q : Y ⟶ Spec R) [IsSeparated q]
    {V₁ V₂ : Y.Opens} (h1 : IsAffineOpen V₁) (h2 : IsAffineOpen V₂) : IsAffineOpen (V₁ ⊓ V₂) :=
  (isAffineHom_diagonal_iff (f := q)).mp inferInstance ⊤ (isAffineOpen_top _) V₁ (by simp) V₂ (by simp) h1 h2

theorem iSup_fin_succ_eq {Y : Scheme.{0}} {n : ℕ} (V : Fin (n + 1) → Y.Opens) :
    (⨆ i, V i) = (⨆ i : Fin n, V i.castSucc) ⊔ V (Fin.last n) := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact le_sup_right
    · exact le_sup_of_le_left (le_iSup (fun j : Fin n => V j.castSucc) j)
  · exact sup_le (iSup_le fun j => le_iSup V j.castSucc) (le_iSup V _)

theorem main (R : CommRingCat.{0}) (P : ∀ X : Scheme.{0}, (X ⟶ Spec R) → Prop)
    (hA : ∀ (X : Scheme.{0}) [IsAffine X] (p : X ⟶ Spec R), P X p)
    (hM : ∀ {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X) (p : X ⟶ Spec R), IsMV a b f g →
      P U (f ≫ p) → P V (g ≫ p) → P W (a ≫ f ≫ p) → P X p) :
    ∀ (n : ℕ) (Y : Scheme.{0}) (q : Y ⟶ Spec R) [IsSeparated q] (V : Fin n → Y.Opens),
      (∀ i, IsAffineOpen (V i)) → (⨆ i, V i) = ⊤ → P Y q := by
  intro n
  induction n with
  | zero =>
    intro Y q _ V _ hV
    have : IsEmpty Y := by
      refine ⟨fun x => ?_⟩
      have hx : x ∈ (⊤ : Y.Opens) := trivial
      rw [← hV] at hx
      obtain ⟨i, _⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact i.elim0
    have : IsAffine Y := inferInstance
    exact hA Y q
  | succ n ih =>
    intro Y q _ V hA' hV
    set U : Y.Opens := ⨆ i : Fin n, V i.castSucc with hUdef
    set V' : Y.Opens := V (Fin.last n)
    have hUV : U ⊔ V' = ⊤ := by rw [← hV, iSup_fin_succ_eq]
    refine hM _ _ U.ι V'.ι q (isMV_opens U V' hUV) ?_ ?_ ?_
    ·
      refine ih U (U.ι ≫ q) (fun i => U.ι ⁻¹ᵁ V i.castSucc) (fun i => ?_) ?_
      · exact (hA' _).preimage_of_isOpenImmersion U.ι
          (by rw [Scheme.Opens.opensRange_ι]; exact le_iSup (fun j : Fin n => V j.castSucc) i)
      · rw [← Scheme.Hom.preimage_iSup, Scheme.Opens.ι_preimage_self]
    · have : IsAffine V' := hA' (Fin.last n)
      exact hA _ _
    ·
      rw [← Category.assoc, Scheme.homOfLE_ι]
      refine ih _ ((U ⊓ V').ι ≫ q) (fun i => (U ⊓ V').ι ⁻¹ᵁ (V i.castSucc ⊓ V')) (fun i => ?_) ?_
      · exact (inf_affine q (hA' _) (hA' _)).preimage_of_isOpenImmersion _
          (by rw [Scheme.Opens.opensRange_ι]
              exact inf_le_inf_right _ (le_iSup (fun j : Fin n => V j.castSucc) i))
      · rw [← Scheme.Hom.preimage_iSup, ← iSup_inf_eq, Scheme.Opens.ι_preimage_self]

theorem Ind_of : LateralTheory.KummerTheory.ContCut.Ind := by
  intro R P hA hM X p _ _
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨s, hs, hU⟩ := (isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens (X := X)
    (U := Set.univ)).mp ⟨isCompact_univ, isOpen_univ⟩
  have : Finite s := hs
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin s
  refine main R P hA hM n X p (fun i => ((e.symm i : s) : X.affineOpens)) (fun i => (e.symm i : s).1.2) ?_
  ext x
  simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  have hx : x ∈ (Set.univ : Set X) := trivial
  rw [hU] at hx
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp hx
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨e ⟨a, ha⟩, ?_⟩
  simpa using hxa

end LateralTheory.KummerTheory.IndPf
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.DictExistPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.DE
variable {R : Type} [CommRing R] {I : Cx R} {X : Scheme.{0}} {n : ℤ}

def eta (a : Sec (I.X n) X) : (freeP R).obj (yoneda.obj X) ⟶ (I.X n).obj where
  app U := ModuleCat.freeDesc (↾fun y : ULift.{1} (U.unop ⟶ X) => ((I.X n).obj.map y.down.op).hom a)
  naturality := by
    intro U V g
    apply ModuleCat.free_hom_ext
    intro y
    erw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.free_map_apply]
    erw [ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    erw [← ModuleCat.comp_apply, ← Functor.map_comp]
    rfl

theorem eta_app (a : Sec (I.X n) X) (U : Scheme.{0}) (x : U ⟶ X) :
    ((eta a).app (op U)).hom (ModuleCat.freeMk (ULift.up x)) = Sec.res x a := by
  erw [eta, ModuleCat.freeDesc_apply]
  rfl

def phi (a : Sec (I.X n) X) : (free R).obj (yoneda.obj X) ⟶ I.X n :=
  ⟨sheafifyLift Scheme.etaleTopology (eta a) (I.X n).property⟩

theorem phi_gen (a : Sec (I.X n) X) (U : Scheme.{0}) (x : U ⟶ X) :
    Sec.map (phi a) (freeGen R (yoneda.obj X) U x) = Sec.res x a := by
  have key := congrArg (fun t => (t.app (op U)).hom (ModuleCat.freeMk (ULift.up x)))
    (toSheafify_sheafifyLift Scheme.etaleTopology (eta a) (I.X n).property)
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at key
  exact key.trans (eta_app a U x)

def coch (a : Sec (I.X n) X) : Cochain ((chains R).obj (sch.obj X)) I n :=
  Cochain.single (p := -((0 : ℕ) : ℤ)) (q := n) ((chainsXIso R (sch.obj X) 0).hom ≫ phi a) n

theorem coch_zero (a : Sec (I.X n) X) (h : -((0 : ℕ) : ℤ) + n = n) (U : Scheme.{0}) (x : U ⟶ X) :
    ev (R := R) (coch a) 0 n h U x = Sec.res x a := by
  change Sec.map ((chainsXIso R _ 0).inv ≫ (coch a).v _ _ h) (freeGen R ((sch.obj X).obj (op (SimplexCategory.mk 0))) U x) = _
  rw [coch, Cochain.single_v]
  erw [Iso.inv_hom_id_assoc]
  exact phi_gen a U x

theorem coch_succ (a : Sec (I.X n) X) (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx (sch.obj X) (p + 1) U) : ev (R := R) (coch a) (p + 1) s h U x = 0 := by
  rw [AW.ev_eq, coch, Cochain.single_v_eq_zero _ _ _ _ _ (by omega), comp_zero]
  rfl

theorem ev_zero_cochain {E : Spc} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := R) (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by
  simp [ev]

theorem coch_delta (a : Sec (I.X n) X) (ha : Sec.map (I.d n (n + 1)) a = 0) : δ n (n + 1) (coch a) = 0 := by
  apply AW.ev_ext
  intro p s h U x
  rw [ev_zero_cochain]
  rcases p with _ | p
  · obtain rfl : s = n + 1 := by omega
    rw [AW.ev_delta_zero rfl (coch a) n (n + 1) (by simp) h U x, coch_zero a (by simp) U x]
    have e := AW.sec_map_res (I.d n (n + 1)) (show U ⟶ X from x) a
    rw [ha] at e
    exact e.symm.trans (LinearMap.map_zero _)
  · rw [AW.ev_delta_succ rfl (coch a) p (-((p + 1 : ℕ) : ℤ) + n) s rfl h U x, coch_succ]
    rw [show Sec.map (I.d (-((p + 1 : ℕ) : ℤ) + n) s) (0 : Sec (I.X (-((p + 1 : ℕ) : ℤ) + n)) U) = 0 from LinearMap.map_zero _, zero_add]
    rcases p with _ | p
    · have hs : n = s := by omega
      subst hs
      rw [Fin.sum_univ_two]
      have e : ∀ i : Fin 2, ev (R := R) (coch a) 0 n (by omega) U (x.face i) =
          Sec.res (show U ⟶ X from x) a := fun i => coch_zero a _ U _
      rw [e 0, e 1]
      simp
    · simp only [coch_succ, smul_zero, Finset.sum_const_zero]

theorem dictExist : DictExist := by
  intro R _ I X n a ha
  refine ⟨⟨coch a, (Cocycle.mem_iff n (n + 1) rfl _).2 (coch_delta a ha)⟩, ?_, ?_⟩
  · exact (coch_zero a (by simp) X (𝟙 X)).trans (by rw [Sec.res, op_id, CategoryTheory.Functor.map_id]; rfl)
  · intro p s h U y
    exact coch_succ a p s h U y

end LateralTheory.KummerTheory.DE

namespace LateralTheory.KummerTheory

theorem DictExist_of : DictExist := DE.dictExist
end LateralTheory.KummerTheory
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.DerDictPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.DerDictPf

def hc {C : Type*} [Category C] [Preadditive C] {X Y X' Y' : C} (i : X ≅ X') (j : Y ≅ Y') :
    (X ⟶ Y) ≃+ (X' ⟶ Y') :=
  { i.homCongr j with map_add' := fun f g => by simp [Iso.homCongr_apply] }

lemma zcomp_ofHom {C : Type*} [Category C] [Preadditive C] {K L M : CochainComplex C ℤ} {n : ℤ}
    (c : Cocycle K L n) (g : L ⟶ M) : zcomp c (Cocycle.ofHom g) (add_zero n) = c.postcomp g := by
  ext p q hpq
  simp [zcomp, Cocycle.postcomp]

section
variable (R : Type) [CommRing R] [HasDerivedCategory (Shv R)]

def isoL (hres : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) (F : Shv R) : DerivedCategory.Q.obj (res R F) ≅ (DerivedCategory.singleFunctor (Shv R) 0).obj F :=
  haveI : IsIso (DerivedCategory.Q.map (resAug F)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := resAug F)).2 (hres R F).2.2.2.1
  (asIso (DerivedCategory.Q.map (resAug F))).symm ≪≫ (DerivedCategory.singleFunctorIsoCompQ (Shv R) 0).symm.app F

lemma isoL_nat (hres : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) {F G : Shv R} (φ : F ⟶ G) :
    DerivedCategory.Q.map (resMap R φ) ≫ (isoL R hres G).hom =
      (isoL R hres F).hom ≫ (DerivedCategory.singleFunctor (Shv R) 0).map φ := by
  haveI : IsIso (DerivedCategory.Q.map (resAug F)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := resAug F)).2 (hres R F).2.2.2.1
  haveI : IsIso (DerivedCategory.Q.map (resAug G)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := resAug G)).2 (hres R G).2.2.2.1
  have h1 := congrArg DerivedCategory.Q.map (((hres R F).2.2.2.2.2.2.2 G φ).1)
  simp only [Functor.map_comp] at h1
  have h2 := (DerivedCategory.singleFunctorIsoCompQ (Shv R) 0).inv.naturality φ
  simp only [isoL, Iso.trans_hom, Iso.symm_hom, asIso_inv, Iso.app_hom]
  rw [Category.assoc, IsIso.eq_inv_comp, ← Category.assoc, h1, Category.assoc, IsIso.hom_inv_id_assoc]
  exact h2

def jIso (hres : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) (F : Shv R) (n : ℤ) :
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient (Shv R) _).obj ((res R F)⟦n⟧)) ≅
      ((DerivedCategory.singleFunctor (Shv R) 0).obj F)⟦n⟧ :=
  (DerivedCategory.quotientCompQhIso (Shv R)).app _ ≪≫ (DerivedCategory.Q.commShiftIso n).app (res R F) ≪≫
    (CategoryTheory.shiftFunctor _ n).mapIso (isoL R hres F)

lemma jIso_nat (hres : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) {F G : Shv R} (φ : F ⟶ G) (n : ℤ) :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient (Shv R) _).map ((resMap R φ)⟦n⟧')) ≫ (jIso R hres G n).hom =
      (jIso R hres F n).hom ≫ ((DerivedCategory.singleFunctor (Shv R) 0).map φ)⟦n⟧' := by
  have h1 := (DerivedCategory.quotientCompQhIso (Shv R)).hom.naturality ((resMap R φ)⟦n⟧')
  have h2 := (DerivedCategory.Q.commShiftIso n).hom.naturality (resMap R φ)
  have h3 := congrArg (fun f => f⟦n⟧') (isoL_nat R hres φ)
  simp only [Functor.map_comp] at h3
  simp only [jIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  simp only [Functor.comp_map] at h1 h2
  rw [← Category.assoc, h1, Category.assoc, ← Category.assoc (DerivedCategory.Q.map _), h2, Category.assoc, h3,
    Category.assoc]
  simp only [Category.assoc]

def dict (hres : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) (K : Cx R) (F : Shv R) (n : ℤ) :
    HK R K F n ≃+ (DerivedCategory.Q.obj K ⟶ ((DerivedCategory.singleFunctor (Shv R) 0).obj F)⟦n⟧) :=
  haveI := (hres R F).1
  (CohomologyClass.homAddEquiv).trans <|
    (AddEquiv.ofBijective (DerivedCategory.Qh.mapAddHom)
      (CochainComplex.IsKInjective.Qh_map_bijective _ ((res R F)⟦n⟧))).trans <|
    hc ((DerivedCategory.quotientCompQhIso (Shv R)).app K) (jIso R hres F n)

lemma dict_mk (hres : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) (K : Cx R) (F : Shv R) (n : ℤ) (c : Cocycle K (res R F) n) :
    dict R hres K F n (CohomologyClass.mk c) =
      (DerivedCategory.quotientCompQhIso (Shv R)).inv.app K ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient (Shv R) _).map (Cocycle.equivHomShift.symm c)) ≫
          (jIso R hres F n).hom := by
  simp [dict, hc, Iso.homCongr_apply, CohomologyClass.toHom_mk]; rfl

end

theorem DerDict_of (hres : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) : LateralTheory.KummerTheory.BockCut.DerDict := by
  intro R _ K
  letI := HasDerivedCategory.standard (Shv R)
  refine ⟨dict R hres K, ?_⟩
  intro F G φ n x
  obtain ⟨c, rfl⟩ := x.mk_surjective
  have hp : HK.post R K φ n (CohomologyClass.mk c) = CohomologyClass.mk (c.postcomp (resMap R φ)) := by
    rw [← zcomp_ofHom]; rfl
  rw [hp, dict_mk, dict_mk, Cocycle.equivHomShift_symm_postcomp, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  exact congrArg (fun t => (DerivedCategory.quotientCompQhIso (Shv R)).inv.app K ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient (Shv R) _).map (Cocycle.equivHomShift.symm c)) ≫ t)
    (jIso_nat R hres φ n)

end LateralTheory.KummerTheory.DerDictPf
end
end
