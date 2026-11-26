module

public import Development.EtaleCohomology.KummerTheory.BockCut

@[expose] public section

section -- merged from Development.EtaleCohomology.KummerTheory.FivePf
noncomputable section
open CategoryTheory Limits

namespace LateralTheory.KummerTheory.FivePf
open LateralTheory.KummerTheory.ContCut

variable {K : Type 1} [Category.{0} K]

theorem mapc (G : K ⥤ AddCommGrpCat.{1}) {a b d : K} (f : a ⟶ b) (g : b ⟶ d) (x : G.obj a) :
    (G.map g).hom ((G.map f).hom x) = (G.map (f ≫ g)).hom x := by
  rw [G.map_comp]; rfl

theorem natap {F G : K ⥤ AddCommGrpCat.{1}} (α : F ⟶ G) {k k' : K} (h : k ⟶ k') (x : F.obj k) :
    (α.app k').hom ((F.map h).hom x) = (G.map h).hom ((α.app k).hom x) := by
  have := congrArg (fun φ => φ.hom x) (α.naturality h)
  exact this

theorem commap {X U V W : ℤ → K ⥤ AddCommGrpCat.{1}} (S : MVSeq X U V W) (n : ℤ) (k : K) (x : (X n).obj k) :
    ((S.a n).app k).hom (((S.f n).app k).hom x) = ((S.b n).app k).hom (((S.g n).app k).hom x) := by
  have := congrArg (fun φ => (φ.app k).hom x) (S.comm n)
  exact this

variable {J : Type} [SmallCategory J] {D : J ⥤ K}

theorem natι {F G : K ⥤ AddCommGrpCat.{1}} (α : F ⟶ G) (c : Cocone D) (j : J) (x : F.obj (D.obj j)) :
    (α.app c.pt).hom ((F.map (c.ι.app j)).hom x) = (G.map (c.ι.app j)).hom ((α.app (D.obj j)).hom x) :=
  natap α (c.ι.app j) x

theorem push (G : K ⥤ AddCommGrpCat.{1}) (c : Cocone D) {j k : J} (f : j ⟶ k) (y : G.obj (D.obj j)) :
    (G.map (c.ι.app k)).hom ((G.map (D.map f)).hom y) = (G.map (c.ι.app j)).hom y := by
  rw [mapc, c.w]

theorem five_succ [IsFiltered J] (X U V W : ℤ → K ⥤ AddCommGrpCat.{1}) (S : MVSeq X U V W) (c : Cocone D)
    (hU : ∀ n, Lim (U n) c) (hV : ∀ n, Lim (V n) c) (hW : ∀ n, Lim (W n) c) (m : ℤ) : Lim (X (m + 1)) c := by
  constructor
  · intro x
    obtain ⟨j1, u, hu⟩ := (hU (m + 1)).1 (((S.f (m + 1)).app c.pt).hom x)
    obtain ⟨j2, v, hv⟩ := (hV (m + 1)).1 (((S.g (m + 1)).app c.pt).hom x)
    obtain ⟨k, g1, g2, -⟩ := IsFilteredOrEmpty.cocone_objs j1 j2
    have e0 : ((W (m + 1)).map (c.ι.app k)).hom
        (((S.a (m + 1)).app (D.obj k)).hom (((U (m + 1)).map (D.map g1)).hom u) -
          ((S.b (m + 1)).app (D.obj k)).hom (((V (m + 1)).map (D.map g2)).hom v)) = 0 := by
      rw [map_sub, ← natι (S.a (m + 1)), ← natι (S.b (m + 1)), push, push, hu, hv, commap, sub_self]
    obtain ⟨k2, f2, h2⟩ := (hW (m + 1)).2 k _ e0
    rw [map_sub, ← natap (S.a (m + 1)), ← natap (S.b (m + 1)), sub_eq_zero] at h2
    obtain ⟨x', hx1, hx2⟩ := S.exUV (m + 1) (D.obj k2) _ _ h2
    obtain ⟨xi, hxi⟩ : ∃ xi : (X (m + 1)).obj c.pt, xi = ((X (m + 1)).map (c.ι.app k2)).hom x' := ⟨_, rfl⟩
    have hfd : ((S.f (m + 1)).app c.pt).hom (x - xi) = 0 := by
      rw [map_sub, hxi, natι (S.f (m + 1)), hx1, push, push, hu, sub_self]
    have hgd : ((S.g (m + 1)).app c.pt).hom (x - xi) = 0 := by
      rw [map_sub, hxi, natι (S.g (m + 1)), hx2, push, push, hv, sub_self]
    obtain ⟨w, hw⟩ := S.exX m c.pt _ hfd hgd
    obtain ⟨j3, w0, hw0⟩ := (hW m).1 w
    obtain ⟨k4, g3, g4, -⟩ := IsFilteredOrEmpty.cocone_objs k2 j3
    refine ⟨k4, ((X (m + 1)).map (D.map g3)).hom x' + ((X (m + 1)).map (D.map g4)).hom (((S.δ m).app (D.obj j3)).hom w0), ?_⟩
    rw [map_add (f := _), push, push, ← natι (S.δ m), hw0, hw, ← hxi]
    exact add_sub_cancel _ _
  · intro j y hy
    have hfy : ((U (m + 1)).map (c.ι.app j)).hom (((S.f (m + 1)).app (D.obj j)).hom y) = 0 := by
      rw [← natι (S.f (m + 1)), hy, map_zero]
    obtain ⟨k1, f1, h1⟩ := (hU (m + 1)).2 j _ hfy
    have hgy : ((V (m + 1)).map (c.ι.app k1)).hom
        (((V (m + 1)).map (D.map f1)).hom (((S.g (m + 1)).app (D.obj j)).hom y)) = 0 := by
      rw [push, ← natι (S.g (m + 1)), hy, map_zero]
    obtain ⟨k2, f2, h2⟩ := (hV (m + 1)).2 k1 _ hgy
    have hf1 : ((S.f (m + 1)).app (D.obj k2)).hom (((X (m + 1)).map (D.map (f1 ≫ f2))).hom y) = 0 := by
      rw [natap, D.map_comp, ← mapc, h1, map_zero]
    have hg1 : ((S.g (m + 1)).app (D.obj k2)).hom (((X (m + 1)).map (D.map (f1 ≫ f2))).hom y) = 0 := by
      rw [natap, D.map_comp, ← mapc, h2]
    obtain ⟨w, hw⟩ := S.exX m (D.obj k2) _ hf1 hg1
    have hdw : ((S.δ m).app c.pt).hom (((W m).map (c.ι.app k2)).hom w) = 0 := by
      rw [natι (S.δ m), hw, push, hy]
    obtain ⟨u, v, huv⟩ := (S.exW m c.pt _).1 hdw
    obtain ⟨j1, u0, hu0⟩ := (hU m).1 u
    obtain ⟨j2, v0, hv0⟩ := (hV m).1 v
    obtain ⟨k3, g1, g2, -⟩ := IsFilteredOrEmpty.cocone_objs j1 j2
    obtain ⟨k4, g3, g4, -⟩ := IsFilteredOrEmpty.cocone_objs k2 k3
    have he : ((W m).map (c.ι.app k4)).hom (((W m).map (D.map g3)).hom w -
        (((S.a m).app (D.obj k4)).hom (((U m).map (D.map (g1 ≫ g4))).hom u0) -
          ((S.b m).app (D.obj k4)).hom (((V m).map (D.map (g2 ≫ g4))).hom v0))) = 0 := by
      rw [map_sub, map_sub, push, ← natι (S.a m), ← natι (S.b m), push, push, hu0, hv0, huv, sub_self]
    obtain ⟨k5, g5, h5⟩ := (hW m).2 k4 _ he
    rw [map_sub, sub_eq_zero, mapc, map_sub, ← natap (S.a m), ← natap (S.b m)] at h5
    refine ⟨k5, (f1 ≫ f2) ≫ g3 ≫ g5, ?_⟩
    rw [D.map_comp, ← mapc, ← hw, ← natap (S.δ m), D.map_comp, h5]
    exact (S.exW m _ _).2 ⟨_, _, rfl⟩

theorem Five_of : LateralTheory.KummerTheory.ContCut.Five := by
  intro J _ _ K _ X U V W ⟨S⟩ D c hU hV hW n
  have := five_succ X U V W S c hU hV hW (n - 1)
  rwa [sub_add_cancel] at this

end LateralTheory.KummerTheory.FivePf
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.RedPostPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.RedPostPf
open LateralTheory.KummerTheory.BockCut

variable {S R T : Type} [CommRing S] [CommRing R] [CommRing T]

theorem sec_nat {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) := by
  have h := φ.hom.naturality g.op
  exact (congrArg (fun f => f.hom a) h).symm

theorem sec_comp {F G M : Shv R} (φ : F ⟶ G) (ψ : G ⟶ M) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (φ ≫ ψ) a = Sec.map ψ (Sec.map φ a) := rfl

def scomp {I : Cx S} {J : Cx R} {K : Cx T} (ρ : SemiMap I J) (σ : SemiMap J K) : SemiMap I K where
  app U s := (σ.app U s).comp (ρ.app U s)
  nat g s a := by simp only [AddMonoidHom.comp_apply]; rw [σ.nat, ρ.nat]
  comm U s t a := by simp only [AddMonoidHom.comp_apply]; rw [σ.comm, ρ.comm]

def spost {I : Cx S} {J J' : Cx R} (ρ : SemiMap I J) (u : J ⟶ J') : SemiMap I J' where
  app U s := ((u.f s).hom.app (op U)).hom.toAddMonoidHom.comp (ρ.app U s)
  nat g s a := by
    change Sec.res g (Sec.map (u.f s) (ρ.app _ s a)) = Sec.map (u.f s) (ρ.app _ s (Sec.res g a))
    rw [sec_nat, ρ.nat]
  comm U s t a := by
    change Sec.map (J'.d s t) (Sec.map (u.f s) (ρ.app U s a)) = Sec.map (u.f t) (ρ.app U t (Sec.map (I.d s t) a))
    rw [← ρ.comm, ← sec_comp, ← sec_comp, u.comm]

theorem scomp_op (hS : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses) {I : Cx S} {J : Cx R} {K : Cx T} (ρ : SemiMap I J)
    (σ : SemiMap J K) (E : Spc) (n : ℤ) (x : CohomologyClass ((chains S).obj E) I n) :
    (scomp ρ σ).op.app E n x = σ.op.app E n (ρ.op.app E n x) := by
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨β, hβ⟩ := (hS S R ρ).1 E n α
  obtain ⟨γ, hγ⟩ := (hS R T σ).1 E n β
  rw [(hS S R ρ).2 E n α β hβ, (hS R T σ).2 E n β γ hγ, (hS S T (scomp ρ σ)).2 E n α γ ?_]
  intro p s h U y
  rw [hγ, hβ]
  rfl

end LateralTheory.KummerTheory.RedPostPf

namespace LateralTheory.KummerTheory.RedPostPf
open LateralTheory.KummerTheory.BockCut

variable {S R : Type} [CommRing S] [CommRing R]

def up {F : Shv S} (φ : R →+* S) {U : Scheme.{0}} (a : Sec ((restr φ).obj F) U) : Sec F U := a

theorem up_add {F : Shv S} (φ : R →+* S) {U : Scheme.{0}} (a b : Sec ((restr φ).obj F) U) :
    up φ (a + b) = up φ a + up φ b := rfl

theorem up_res {F : Shv S} (φ : R →+* S) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec ((restr φ).obj F) U) :
    Sec.res g (up φ a) = up φ (Sec.res g a) := rfl

theorem sec_add {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add _ _ _

theorem RedPost_of (hU : SemiUniq) (hE : TwExt) (hZ : ZHom) (hS : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses)
    (hC : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapCompCompatible) (hR : LateralTheory.EtaleFoundations.EtaleRootsOfUnityReductionMapGenerator) (hX : LateralTheory.EtaleFoundations.EtaleRestrictScalarsResolutionCompatible)
    (hP : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities) (hB : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) : RedPost := by
  intro Q q _ hq i π hπ E n x
  have : NeZero q := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne Q) hq⟩
  let ρ := scomp (redMap Q q i) (restrMap (Int.castRingHom (ZMod q)) (tw q i))
  let r0 := restrMap (Int.castRingHom (ZMod Q)) (tw Q i)
  let ρ' := spost r0 (resMap ℤ π)
  have h1 : restrH (Int.castRingHom (ZMod q)) E (tw q i) n (red Q q E n i x) = ρ.op.app E n x :=
    (scomp_op hS _ _ E n x).symm
  have h2 : HK.post ℤ ((chains ℤ).obj E) π n (restrH (Int.castRingHom (ZMod Q)) E (tw Q i) n x) = ρ'.op.app E n x :=
    ((hC (ZMod Q) ℤ r0 ρ' (resMap ℤ π) (fun _ _ _ => rfl)).1 E n x).symm
  rw [h1, h2]
  obtain ⟨φ1, hφ1⟩ := hZ (TZ Q i) ((res ℤ (TZ q i)).X 0)
    (fun U => AddMonoidHom.mk' (fun a : Sec (TZ Q i) U => ρ.app U 0 (Sec.map (resι _ (tw Q i)) (up _ a)))
      (fun a b => by rw [up_add, sec_add, map_add (f := _)]))
    (fun V U g a => by
      change Sec.res g (ρ.app U 0 (Sec.map (resι _ (tw Q i)) (up _ a))) = ρ.app V 0 (Sec.map (resι _ (tw Q i)) (up _ (Sec.res g a)))
      rw [ρ.nat, sec_nat, up_res])
  obtain ⟨φ2, hφ2⟩ := hZ (TZ Q i) ((res ℤ (TZ q i)).X 0)
    (fun U => AddMonoidHom.mk' (fun a : Sec (TZ Q i) U => ρ'.app U 0 (Sec.map (resι _ (tw Q i)) (up _ a)))
      (fun a b => by rw [up_add, sec_add, map_add (f := _)]))
    (fun V U g a => by
      change Sec.res g (ρ'.app U 0 (Sec.map (resι _ (tw Q i)) (up _ a))) = ρ'.app V 0 (Sec.map (resι _ (tw Q i)) (up _ (Sec.res g a)))
      rw [ρ'.nat, sec_nat, up_res])
  have heq : φ1 = φ2 := by
    refine hE Q i _ φ1 φ2 fun U ζ => ?_
    obtain ⟨ξ, hξ⟩ := (hP Q Γ(U, ⊤)).2.2.2.2.2 q hq ζ
    rw [hφ1, hφ2]
    change (restrMap (Int.castRingHom (ZMod q)) (tw q i)).app U 0 ((redMap Q q i).app U 0 (resGen i ζ)) =
      Sec.map ((resMap ℤ π).f 0) (r0.app U 0 (Sec.map (resι _ (tw Q i)) (twGen i ζ)))
    rw [hR Q q hq i U ζ ξ hξ, hX ℤ (ZMod Q) _ (tw Q i) U (twGen i ζ)]
    change (restrMap (Int.castRingHom (ZMod q)) (tw q i)).app U 0 (Sec.map (resι _ (tw q i)) (twGen i ξ)) = _
    rw [hX ℤ (ZMod q) _ (tw q i) U (twGen i ξ), ← sec_comp, ((hB ℤ (TZ Q i)).2.2.2.2.2.2.2 (TZ q i) π).2, sec_comp]
    exact congrArg (Sec.map (resι ℤ (TZ q i))) (hπ U ζ ξ hξ).symm
  refine hU (ZMod Q) (tw Q i) (TZ q i) ρ ρ' (fun U a => ?_) E n x
  have e1 := hφ1 U a
  have e2 := hφ2 U a
  rw [heq] at e1
  exact e1.symm.trans e2

end LateralTheory.KummerTheory.RedPostPf
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.RedKerPf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.RedKerPf

open LateralTheory.KummerTheory.BockCut

theorem sepLoc {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (y z : Sec F U)
    (h : Loc U fun V g => Sec.res g y = Sec.res g z) : y = z := by
  obtain ⟨S, hS, hh⟩ := h
  have h1 := (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget _ F.obj (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.property)
  exact (h1 S hS).isSeparatedFor.ext (fun {V} {g} hg => hh V g hg)

theorem locZero {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (hL : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure)
    (y : Sec F U) (h : Loc U fun V g => Sec.res g y = 0) : y = 0 := by
  refine sepLoc y 0 (hL.2.1 U _ _ h fun V g hg => ?_)
  rw [hg]; exact (map_zero _).symm

theorem secEmpty {R : Type} [CommRing R] {F : Shv R} {V : Scheme.{0}} [IsEmpty V]
    (hL : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure) (y : Sec F V) : y = 0 :=
  sepLoc y 0 (hL.2.2.2.2.2.2 V _)

theorem resMap {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (congrArg (fun f => (ModuleCat.Hom.hom f) x) (φ.hom.naturality g.op)).symm

theorem resNsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (x : Sec F U) :
    Sec.res g (n • x) = n • Sec.res g x := map_nsmul _ _ _

theorem mapNsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (n : ℕ) (x : Sec F U) :
    Sec.map φ (n • x) = n • Sec.map φ x := map_nsmul _ _ _

theorem killTw {q : ℕ} {i : ℤ} {U : Scheme.{0}} (x : Sec (tw q i) U) : q • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by ext; simp
  rw [this, zero_smul]

theorem kill {q : ℕ} {i : ℤ} {U : Scheme.{0}} (x : Sec (TZ q i) U) : q • x = 0 := killTw (i := i) x

theorem mapGen (hT : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated) (hP : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities)
    (Q e q : ℕ) [NeZero Q] [NeZero q] (hQ : Q = e * q) (i : ℤ) (π : TZ Q i ⟶ TZ q i) (hπ : IsRed Q q i π)
    (V : Scheme.{0}) [Nonempty V] (ζ : Prim Q Γ(V, ⊤)) (c : ℕ) :
    Sec.map π (c • genZ i ζ) = 0 ↔ q ∣ c := by
  obtain ⟨ξ, hξ⟩ := (hP Q Γ(V, ⊤)).2.2.2.2.2 q ⟨e, by rw [hQ, mul_comm]⟩ ζ
  rw [mapNsmul, hπ V ζ ξ hξ]
  constructor
  · intro h; exact (hT q i).2.2.1 V ξ c h
  · rintro ⟨k, rfl⟩
    rw [mul_comm, mul_smul, kill, smul_zero]

theorem eGen (hT : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated)
    (Q e q : ℕ) [NeZero Q] (hQ : Q = e * q) (i : ℤ)
    (V : Scheme.{0}) [Nonempty V] (ζ : Prim Q Γ(V, ⊤)) (c : ℕ) :
    e • (c • genZ i ζ) = 0 ↔ q ∣ c := by
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · exact absurd (by rw [hQ, h, zero_mul]) (NeZero.ne Q)
    · exact h
  rw [← mul_smul]
  constructor
  · intro h
    have := (hT Q i).2.2.1 V ζ (e * c) h
    rw [hQ] at this
    exact (Nat.mul_dvd_mul_iff_left he).1 this
  · rintro ⟨k, rfl⟩
    have : e * (q * k) = Q * k := by rw [hQ]; ring
    rw [this, mul_comm, mul_smul, kill, smul_zero]

theorem RedKer_of (hT : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated) (hP : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities)
    (hL : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure) : RedKer := by
  intro Q e q _ hQ i π hπ U y
  haveI : NeZero q := ⟨by rintro rfl; exact NeZero.ne Q (by rw [hQ, mul_zero])⟩
  have L := (hT Q i).1 U y

  have key : Sec.map π y = 0 → Loc U fun V g => Sec.res g y = 0 ∨ (Nonempty V ∧ ∃ (ζ : Prim Q Γ(V, ⊤)) (c : ℕ),
      q ∣ c ∧ Sec.res (F := TZ Q i) g y = c • genZ i ζ) ∨ IsEmpty V := by
    intro h0
    refine hL.2.1 U _ _ L fun V g hg => ?_
    rcases hg with hg | ⟨ζ, c, hc⟩
    · exact Or.inl hg
    rcases isEmpty_or_nonempty V with hV | hV
    · exact Or.inr (Or.inr hV)
    refine Or.inr (Or.inl ⟨hV, ζ, c, ?_, hc⟩)
    have h1 : Sec.map π (Sec.res (F := TZ Q i) g y) = 0 := by rw [← resMap, h0]; exact map_zero _
    have hc' : Sec.res (F := TZ Q i) g y = c • genZ i ζ := hc
    rw [hc'] at h1
    exact (mapGen hT hP Q e q hQ i π hπ V ζ c).1 h1
  refine ⟨⟨fun h0 => ?_, fun h0 => ?_⟩, fun h0 => ?_⟩
  · refine locZero hL _ (hL.2.1 U _ _ (key h0) fun V g hg => ?_)
    rw [resNsmul]
    rcases hg with hg | ⟨hV, ζ, c, hc, hg⟩ | hV
    · rw [hg]; exact smul_zero _
    · rw [hg]; exact (eGen hT Q e q hQ i V ζ c).2 hc
    · exact secEmpty hL _
  · refine locZero hL _ (hL.2.1 U _ _ L fun V g hg => ?_)
    rw [resMap]
    rcases hg with hg | ⟨ζ, c, hc⟩
    · have hg' : Sec.res (F := TZ Q i) g y = 0 := hg
      rw [hg']; exact map_zero _
    rcases isEmpty_or_nonempty V with hV | hV
    · exact secEmpty hL _
    have hc' : Sec.res (F := TZ Q i) g y = c • genZ i ζ := hc
    have h1 : e • Sec.res (F := TZ Q i) g y = 0 := by rw [← resNsmul, h0]; exact map_zero _
    rw [hc'] at h1 ⊢
    exact (mapGen hT hP Q e q hQ i π hπ V ζ c).2 ((eGen hT Q e q hQ i V ζ c).1 h1)
  · refine hL.2.1 U _ _ (key h0) fun V g hg => ?_
    rcases hg with hg | ⟨hV, ζ, c, ⟨k, rfl⟩, hg⟩ | hV
    · exact ⟨0, by rw [hg]; exact smul_zero _⟩
    · exact ⟨k • genZ i ζ, by rw [hg, ← mul_smul]⟩
    · exact ⟨0, by rw [smul_zero]; exact (secEmpty hL _).symm⟩

end LateralTheory.KummerTheory.RedKerPf
end

section -- merged from Development.EtaleCohomology.KummerTheory.DeltaPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.DeltaPf
open LateralTheory.KummerTheory LateralTheory.KummerTheory.ContCut

variable {R : Type} [CommRing R]

theorem sec_res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (a : V ⟶ U) (x : Sec F U) :
    Sec.res a (Sec.map φ x) = Sec.map φ (Sec.res a x) :=
  (congrArg (fun h => h.hom x) (φ.hom.naturality a.op)).symm

theorem sec_map_comp {F G K : Shv R} (φ : F ⟶ G) (ψ : G ⟶ K) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem sec_map_zero {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := rfl

theorem res_add {F : Shv R} {V U : Scheme.{0}} (a : V ⟶ U) (x y : Sec F U) :
    Sec.res a (x + y) = Sec.res a x + Sec.res a y := map_add _ _ _
theorem res_sub {F : Shv R} {V U : Scheme.{0}} (a : V ⟶ U) (x y : Sec F U) :
    Sec.res a (x - y) = Sec.res a x - Sec.res a y := map_sub _ _ _
theorem res_neg {F : Shv R} {V U : Scheme.{0}} (a : V ⟶ U) (x : Sec F U) :
    Sec.res a (-x) = -Sec.res a x := map_neg _ _
theorem res_zero {F : Shv R} {V U : Scheme.{0}} (a : V ⟶ U) : Sec.res a (0 : Sec F U) = 0 := map_zero _
theorem smap_add {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y := map_add _ _ _
theorem smap_sub {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x - y) = Sec.map φ x - Sec.map φ y := map_sub _ _ _
theorem smap_neg {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map φ (-x) = -Sec.map φ x := map_neg _ _
theorem smap_zero {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 := map_zero _

theorem dd (I : Cx R) (i j k : ℤ) {U : Scheme.{0}} (x : Sec (I.X i) U) :
    Sec.map (I.d j k) (Sec.map (I.d i j) x) = 0 := by
  rw [← sec_map_comp, I.d_comp_d, sec_map_zero]

instance injRes (F : Shv R) (n : ℤ) : Injective ((res R F).X n) :=
  inferInstanceAs (Injective ((injectiveResolution F).cochainComplex.X n))

theorem mono_a {W U V X : Scheme.{0}} {a : W ⟶ U} {b : W ⟶ V} {f : U ⟶ X} {g : V ⟶ X}
    (h : IsMV a b f g) : Mono a := by
  obtain ⟨_, hg, hp, _⟩ := h
  haveI := hg
  refine ⟨fun x y e => hp.hom_ext e ?_⟩
  rw [← cancel_mono g, Category.assoc, Category.assoc, ← hp.w, reassoc_of% e]

variable {F : Shv R} {W U V X : Scheme.{0}} {a : W ⟶ U} {b : W ⟶ V} {f : U ⟶ X} {g : V ⟶ X} {n : ℤ}

theorem conn_total (hD : Dict) (hG : Glue) (hF : Flasque) (h : IsMV a b f g)
    (w : H R (sch.obj W) F n) : ∃ x, Conn F a f g n w x := by
  haveI := mono_a h
  obtain ⟨c, hc⟩ := (hD R (res R F) W n).2.1 w
  obtain ⟨s, rfl⟩ := hF R ((res R F).X n) a c
  have hcl := ((hD R (res R F) W n).2.2.1 w _ hc).1
  obtain ⟨-, hglue⟩ := hG R ((res R F).X (n + 1)) a b f g h
  obtain ⟨z, hz1, hz2⟩ := hglue (Sec.map ((res R F).d n (n + 1)) s) 0
    (by rw [sec_res_map, hcl, res_zero])
  have hzc : Sec.map ((res R F).d (n + 1) (n + 1 + 1)) z = 0 := by
    apply (hG R ((res R F).X (n + 1 + 1)) a b f g h).1
    · rw [sec_res_map, hz1, dd]
    · rw [sec_res_map, hz2, smap_zero]
  obtain ⟨x, hx⟩ := (hD R (res R F) X (n + 1)).1 z hzc
  exact ⟨x, s, z, hc, hx, hz1, hz2⟩

theorem conn_add (hD : Dict) {w w' x x'} (h1 : Conn F a f g n w x) (h2 : Conn F a f g n w' x') :
    Conn F a f g n (w + w') (x + x') := by
  obtain ⟨s, z, hs, hz, e1, e2⟩ := h1
  obtain ⟨s', z', hs', hz', e1', e2'⟩ := h2
  refine ⟨s + s', z + z', ?_, ((hD R _ X (n + 1)).2.2.2.1 _ _ _ _ hz hz').1, ?_, ?_⟩
  · rw [res_add]; exact ((hD R _ W n).2.2.2.1 _ _ _ _ hs hs').1
  · rw [res_add, smap_add, e1, e1']
  · rw [res_add, e2, e2', add_zero]

theorem conn_neg (hD : Dict) {w x} (h1 : Conn F a f g n w x) : Conn F a f g n (-w) (-x) := by
  obtain ⟨s, z, hs, hz, e1, e2⟩ := h1
  refine ⟨-s, -z, ?_, ((hD R _ X (n + 1)).2.2.2.1 _ _ _ _ hz hz).2, ?_, ?_⟩
  · rw [res_neg]; exact ((hD R _ W n).2.2.2.1 _ _ _ _ hs hs).2
  · rw [res_neg, smap_neg, e1]
  · rw [res_neg, e2, neg_zero]

theorem conn_zero (hD : Dict) (hG : Glue) (hF : Flasque) (h : IsMV a b f g) {x}
    (hx : Conn F a f g n 0 x) : x = 0 := by
  haveI := mono_a h
  obtain ⟨s, z, hs, hz, e1, e2⟩ := hx
  obtain ⟨c, hc⟩ := ((hD R (res R F) W n).2.2.1 0 _ hs).2.mp rfl
  obtain ⟨s', rfl⟩ := hF R ((res R F).X (n - 1)) a c
  beta_reduce at hc
  obtain ⟨-, hglue⟩ := hG R ((res R F).X n) a b f g h
  obtain ⟨t, ht1, ht2⟩ := hglue (s - Sec.map ((res R F).d (n - 1) n) s') 0
    (by rw [res_sub, sec_res_map, hc, sub_self, res_zero])
  have hzt : Sec.map ((res R F).d n (n + 1)) t = z := by
    refine sub_eq_zero.1 ((hG R ((res R F).X (n + 1)) a b f g h).1 _ ?_ ?_)
    · rw [res_sub, sec_res_map, ht1, e1, smap_sub, dd, sub_zero, sub_self]
    · rw [res_sub, sec_res_map, ht2, e2, smap_zero, sub_self]
  refine ((hD R (res R F) X (n + 1)).2.2.1 x z hz).2.mpr
    ⟨Sec.map ((res R F).XIsoOfEq (by ring : n = n + 1 - 1)).hom t, ?_⟩
  rw [← sec_map_comp, HomologicalComplex.XIsoOfEq_hom_comp_d, hzt]

theorem conn_unique (hD : Dict) (hG : Glue) (hF : Flasque) (h : IsMV a b f g) {w x x'}
    (h1 : Conn F a f g n w x) (h2 : Conn F a f g n w x') : x = x' := by
  have h3 := conn_add hD h1 (conn_neg hD h2)
  rw [add_neg_cancel] at h3
  have := conn_zero hD hG hF h h3
  rwa [← sub_eq_add_neg, sub_eq_zero] at this

end LateralTheory.KummerTheory.DeltaPf

namespace LateralTheory.KummerTheory.ContCut
open LateralTheory.KummerTheory.DeltaPf

theorem Delta_of (hD : Dict) (hG : Glue) (hF : Flasque) : Delta := by
  intro R _ F W U V X a b f g h n
  have tot := fun w => conn_total (F := F) (n := n) hD hG hF h w
  refine ⟨AddMonoidHom.mk' (fun w => Classical.choose (tot w)) (fun w w' =>
    conn_unique hD hG hF h (Classical.choose_spec (tot (w + w')))
      (conn_add hD (Classical.choose_spec (tot w)) (Classical.choose_spec (tot w')))), fun w x => ⟨fun hx =>
    conn_unique hD hG hF h (Classical.choose_spec (tot w)) hx, fun e => e ▸ Classical.choose_spec (tot w)⟩⟩

end LateralTheory.KummerTheory.ContCut
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.PrimTorsPf
noncomputable section
open Polynomial IsLocalRing GlobalTheory.EtC

namespace LateralTheory.KummerTheory.PrimitiveRootTorsion

theorem aeval_cyc {S : Type} [CommRing S] (q : ℕ) (x : S) :
    aeval x (cyclotomic q ℤ) = eval x (cyclotomic q S) := by
  rw [aeval_def, eval₂_eq_eval_map, algebraMap_int_eq, map_cyclotomic_int]

theorem prim_pow {q : ℕ} {B : Type} [CommRing B] (ζ : Prim q B) : ζ.1 ^ q = 1 := by
  obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (aeval ζ.1) hg
  rw [map_mul, ζ.2.2, zero_mul] at h
  simpa [sub_eq_zero] using h

theorem pow_mod_q {q : ℕ} {B : Type} [CommRing B] {x : B} (h : x ^ q = 1) (n : ℕ) : x ^ n = x ^ (n % q) := by
  conv_lhs => rw [← Nat.div_add_mod n q, pow_add, pow_mul, h, one_pow, one_mul]

variable {q : ℕ} [NeZero q] {B : Type} [CommRing B] [IsLocalRing B]

theorem neZero_res (hq : IsUnit (q : B)) : NeZero (q : ResidueField B) :=
  ⟨by simpa using (hq.map (residue B)).ne_zero⟩

theorem uniq (hq : IsUnit (q : B)) {u v : B} (hu : u ^ q = 1) (hv : v ^ q = 1)
    (h : residue B u = residue B v) : u = v := by
  have hq' := neZero_res hq
  have hS : IsUnit (∑ i ∈ Finset.range q, u ^ i * v ^ (q - 1 - i)) := by
    apply isUnit_of_map_unit (residue B)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_mul, map_pow, h]
    rw [geom_sum₂_self]
    have hv' : residue B v ^ q = 1 := by rw [← map_pow, hv, map_one]
    have hu1 : IsUnit (residue B v) := IsUnit.of_pow_eq_one hv' (NeZero.ne q)
    exact (isUnit_iff_ne_zero.2 (NeZero.ne _)).mul (hu1.pow _)
  have e := geom_sum₂_mul u v q
  rw [hu, hv, sub_self] at e
  exact sub_eq_zero.1 ((hS.mul_right_eq_zero).1 e)

theorem prim_res (hq : IsUnit (q : B)) (ζ : Prim q B) : IsPrimitiveRoot (residue B ζ.1) q := by
  have := neZero_res hq
  rw [← isRoot_cyclotomic_iff, IsRoot, ← aeval_cyc]
  have e := Polynomial.aeval_algHom_apply (residue B).toIntAlgHom ζ.1 (cyclotomic q ℤ)
  rw [ζ.2.2, map_zero] at e
  exact e

theorem exists_idx (hq : IsUnit (q : B)) (ζ ξ : Prim q B) :
    ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val := by
  have hζ := prim_res hq ζ
  have hξ := prim_res hq ξ
  obtain ⟨i, hi, he⟩ := hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one
  have hc : i.Coprime q := (hζ.pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (he ▸ hξ)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  have hval : ((ZMod.unitOfCoprime i hc : (ZMod q)ˣ) : ZMod q).val = i := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  rw [hval]
  refine uniq hq (prim_pow ξ) (by rw [← pow_mul, mul_comm, pow_mul, prim_pow ζ, one_pow]) ?_
  rw [map_pow, he]

theorem idx_unique (hq : IsUnit (q : B)) (ζ : Prim q B) {a b : (ZMod q)ˣ}
    (h : ζ.1 ^ (a : ZMod q).val = ζ.1 ^ (b : ZMod q).val) : a = b := by
  have h' := congrArg (residue B) h
  rw [map_pow, map_pow] at h'
  exact Units.ext (ZMod.val_injective q ((prim_res hq ζ).pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h'))

theorem idx_mul {ζ0 ζ ξ : Prim q B} {a b : (ZMod q)ˣ} (hb : ζ.1 = ζ0.1 ^ (b : ZMod q).val)
    (ha : ξ.1 = ζ.1 ^ (a : ZMod q).val) : ξ.1 = ζ0.1 ^ ((a * b : (ZMod q)ˣ) : ZMod q).val := by
  rw [Units.val_mul, ZMod.val_mul, ← pow_mod_q (prim_pow ζ0), ha, hb, ← pow_mul, mul_comm]

end LateralTheory.KummerTheory.PrimitiveRootTorsion

namespace LateralTheory.KummerTheory.PrimitiveRootTorsion

theorem exists_prim {q : ℕ} [NeZero q] {B : Type} [CommRing B] [HenselianLocalRing B]
    [IsSepClosed (ResidueField B)] (hq : IsUnit (q : B)) : Nonempty (Prim q B) := by
  have := neZero_res hq
  obtain ⟨μ, hμ⟩ := IsSepClosed.exists_root (cyclotomic q (ResidueField B))
    (degree_cyclotomic_pos q _ (Nat.pos_of_ne_zero (NeZero.ne q))).ne' (separable_cyclotomic q _)
  obtain ⟨a0, rfl⟩ := residue_surjective μ
  have hev : residue B (eval a0 (cyclotomic q B)) = eval (residue B a0) (cyclotomic q (ResidueField B)) := by
    rw [← Polynomial.eval₂_hom, ← Polynomial.eval_map, map_cyclotomic]
  have hder : residue B (eval a0 (derivative (cyclotomic q B))) =
      eval (residue B a0) (derivative (cyclotomic q (ResidueField B))) := by
    rw [← Polynomial.eval₂_hom, ← Polynomial.eval_map, ← Polynomial.derivative_map, map_cyclotomic]
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (cyclotomic q B) (cyclotomic.monic q B) a0
    (by rw [← residue_eq_zero_iff, hev]; exact hμ)
    (by
      apply isUnit_of_map_unit (residue B)
      rw [hder, isUnit_iff_ne_zero]
      have h := (separable_cyclotomic q (ResidueField B)).aeval_derivative_ne_zero
        (x := residue B a0) (by rw [Polynomial.coe_aeval_eq_eval]; exact hμ)
      rwa [Polynomial.coe_aeval_eq_eval] at h)
  exact ⟨⟨a, hq, by rw [aeval_cyc]; exact ha⟩⟩

end LateralTheory.KummerTheory.PrimitiveRootTorsion

namespace LateralTheory.KummerTheory
open LateralTheory.KummerTheory.PrimitiveRootTorsion

theorem PrimTors_of : PrimTors := by
  intro q _ B _ hSH hq
  obtain ⟨_, _⟩ := hSH
  refine ⟨exists_prim hq, fun i ζ => ?_⟩
  classical
  have hex : ∀ ξ : Prim q B, ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val := fun ξ => exists_idx hq ζ ξ
  let ind : Prim q B → (ZMod q)ˣ := fun ξ => (hex ξ).choose
  have hind : ∀ ξ, ξ.1 = ζ.1 ^ (ind ξ : ZMod q).val := fun ξ => (hex ξ).choose_spec
  let v : Prim q B → ULift.{1} (ZMod q) := fun ξ => ULift.up (((ind ξ) ^ i : (ZMod q)ˣ) : ZMod q)
  let φ := Finsupp.linearCombination (ULift.{1} (ZMod q)) v
  have hker : twRel q i B ≤ LinearMap.ker φ := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨ζ', ξ, a, h, rfl⟩
    have hi : ind ξ = a * ind ζ' := idx_unique hq ζ (by rw [← hind ξ]; exact idx_mul (hind ζ') h)
    change φ _ = 0
    rw [map_sub, Finsupp.linearCombination_single, Finsupp.linearCombination_single, sub_eq_zero]
    apply ULift.ext
    simp [v, hi, mul_zpow]
  let ψ := (twRel q i B).liftQ φ hker
  constructor
  · intro t t' h
    have h2 := congrArg ψ h
    simp only [LinearMap.map_smul, ψ, Submodule.liftQ_apply, φ, Finsupp.linearCombination_single,
      one_smul] at h2
    have h3 := congrArg ULift.down h2
    change t * (((ind ζ) ^ i : (ZMod q)ˣ) : ZMod q) = t' * (((ind ζ) ^ i : (ZMod q)ˣ) : ZMod q) at h3
    exact (Units.mul_left_inj _).1 h3
  · intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    induction x using Finsupp.induction_linear with
    | zero => exact ⟨0, by simp⟩
    | add f g hf hg =>
      obtain ⟨a, ha⟩ := hf
      obtain ⟨b, hb⟩ := hg
      refine ⟨a + b, ?_⟩
      simp only at ha hb ⊢
      rw [Submodule.Quotient.mk_add, ← ha, ← hb, ← add_smul]
      rfl
    | single ξ c =>
      have hmem : Finsupp.single ξ 1 - Finsupp.single ζ (ULift.up (((ind ξ) ^ i : (ZMod q)ˣ) : ZMod q)) ∈
          twRel q i B := Submodule.subset_span ⟨ζ, ξ, ind ξ, hind ξ, rfl⟩
      have he : (Submodule.Quotient.mk (Finsupp.single ξ 1) : _ ⧸ twRel q i B) =
          Submodule.Quotient.mk (Finsupp.single ζ (ULift.up (((ind ξ) ^ i : (ZMod q)ˣ) : ZMod q))) :=
        (Submodule.Quotient.eq _).2 hmem
      refine ⟨(c * ULift.up (((ind ξ) ^ i : (ZMod q)ˣ) : ZMod q)).down, ?_⟩
      have hs : Finsupp.single ζ (ULift.up (((ind ξ) ^ i : (ZMod q)ˣ) : ZMod q)) =
          (ULift.up (((ind ξ) ^ i : (ZMod q)ˣ) : ZMod q)) • Finsupp.single ζ (1 : ULift.{1} (ZMod q)) := by
        rw [Finsupp.smul_single_one]
      simp only [ULift.up_down]
      rw [← Finsupp.smul_single_one ξ c, Submodule.Quotient.mk_smul, he, hs, Submodule.Quotient.mk_smul, smul_smul]

end LateralTheory.KummerTheory
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.ExactPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.ExactPf

open LateralTheory.KummerTheory LateralTheory.KummerTheory.ContCut

variable {R : Type} [CommRing R]

theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  change (F.obj.map g.op ≫ φ.hom.app (op V)).hom x = (φ.hom.app (op U) ≫ G.obj.map g.op).hom x
  rw [φ.hom.naturality]

theorem res_res {F : Shv R} {W V U : Scheme.{0}} (a : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res a (Sec.res g x) = Sec.res (a ≫ g) x := by
  change _ = (F.obj.map (a ≫ g).op).hom x
  rw [op_comp, Functor.map_comp]
  rfl

theorem dd (I : Cx R) (i j k : ℤ) {U : Scheme.{0}} (s : Sec (I.X i) U) :
    Sec.map (I.d j k) (Sec.map (I.d i j) s) = 0 := by
  change (Sec.map (I.d i j ≫ I.d j k) s) = 0
  rw [I.d_comp_d]
  rfl

theorem mneg {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) : Sec.map φ (-x) = -Sec.map φ x :=
  map_neg _ _

theorem mzero {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 := map_zero _

theorem rneg {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) : Sec.res g (-x) = -Sec.res g x :=
  map_neg _ _

theorem msub {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x - y) = Sec.map φ x - Sec.map φ y := map_sub _ _ _

theorem rsub {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) : Sec.res g (x - y) = Sec.res g x - Sec.res g y :=
  map_sub _ _ _

theorem rzero {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem inj (F : Shv R) (m : ℤ) : Injective ((res R F).X m) := by
  unfold res; infer_instance

theorem tr (I : Cx R) {X : Scheme.{0}} (m k j : ℤ) (h : m = k) (a : Sec (I.X j) X) :
    (∃ b : Sec (I.X m) X, Sec.map (I.d m j) b = a) → ∃ b : Sec (I.X k) X, Sec.map (I.d k j) b = a := by
  subst h; exact id

theorem cls_eq (hD : Dict) (F : Shv R) {Y : Scheme.{0}} (m : ℤ) {x y : H R (sch.obj Y) F m}
    {s t : Sec ((res R F).X m) Y} (hx : IsCls x s) (hy : IsCls y t)
    (h : ∃ b : Sec ((res R F).X (m - 1)) Y, Sec.map ((res R F).d (m - 1) m) b = s - t) : x = y := by
  obtain ⟨-, -, D3, D4, -⟩ := hD R (res R F) Y m
  have h3 := (D4 x (-y) s (-t) hx (D4 y y t t hy hy).2).1
  rw [← sub_eq_add_neg, ← sub_eq_add_neg] at h3
  exact sub_eq_zero.mp ((D3 _ _ h3).2.mpr h)

theorem Exact_of (hD : Dict) (hG : Glue) (hF : Flasque) : Exact := by
  intro R _ F W U V X a b f g hmv n
  have hpb := hmv.2.2.1
  haveI : IsOpenImmersion g := hmv.2.1
  haveI : Mono a := hpb.mono_fst_of_mono
  have hw : a ≫ f = b ≫ g := hpb.w
  refine ⟨?_, ?_, ?_⟩
  · intro u v huv
    obtain ⟨u0, hu0⟩ := (hD R (res R F) U n).2.1 u
    obtain ⟨v0, hv0⟩ := (hD R (res R F) V n).2.1 v
    have hau : IsCls (pull R (sch.map a) F n u) (Sec.res a u0) := (hD R (res R F) U n).2.2.2.2 a u u0 hu0
    have hbv : IsCls (pull R (sch.map b) F n v) (Sec.res b v0) := (hD R (res R F) V n).2.2.2.2 b v v0 hv0
    rw [huv] at hau
    have hu0c := ((hD R (res R F) U n).2.2.1 u u0 hu0).1
    have hv0c := ((hD R (res R F) V n).2.2.1 v v0 hv0).1
    obtain ⟨r, hr⟩ : ∃ r : Sec ((res R F).X (n - 1)) W,
        Sec.map ((res R F).d (n - 1) n) r = Sec.res a u0 - Sec.res b v0 := by
      have h3 := ((hD R (res R F) W n).2.2.2.1 _ _ _ _ hau ((hD R (res R F) W n).2.2.2.1 _ _ _ _ hbv hbv).2).1
      rw [add_neg_cancel, ← sub_eq_add_neg] at h3
      exact ((hD R (res R F) W n).2.2.1 _ _ h3).2.mp rfl
    haveI := inj F (n - 1)
    obtain ⟨r', hr'⟩ := hF R ((res R F).X (n - 1)) a r
    change Sec.res a r' = r at hr'
    have hu1 : Sec.res a (u0 - Sec.map ((res R F).d (n - 1) n) r') = Sec.res b v0 := by
      rw [rsub]
      rw [← map_res, hr', hr]
      abel
    obtain ⟨z, hzf, hzg⟩ := (hG R ((res R F).X n) a b f g hmv).2 _ v0 hu1
    have hdz : Sec.map ((res R F).d n (n + 1)) z = 0 := by
      apply (hG R ((res R F).X (n + 1)) a b f g hmv).1
      · rw [← map_res, hzf, msub, hu0c, dd, sub_zero]
      · rw [← map_res, hzg, hv0c]
    obtain ⟨x, hx⟩ := (hD R (res R F) X n).1 z hdz
    refine ⟨x, ?_, ?_⟩
    · have hfx : IsCls (pull R (sch.map f) F n x) (Sec.res f z) := (hD R (res R F) X n).2.2.2.2 f x z hx
      rw [hzf] at hfx
      refine cls_eq hD F n hfx hu0 ⟨-r', ?_⟩
      rw [mneg]
      abel
    · have hgx : IsCls (pull R (sch.map g) F n x) (Sec.res g z) := (hD R (res R F) X n).2.2.2.2 g x z hx
      rw [hzg] at hgx
      exact cls_eq hD F n hgx hv0 ⟨0, by rw [mzero, sub_self]⟩
  · intro x hfx hgx
    obtain ⟨z0, hz0⟩ := (hD R (res R F) X (n + 1)).2.1 x
    have hz0c := ((hD R (res R F) X (n + 1)).2.2.1 x z0 hz0).1
    have hgz : IsCls (pull R (sch.map g) F (n + 1) x) (Sec.res g z0) :=
      (hD R (res R F) X (n + 1)).2.2.2.2 g x z0 hz0
    rw [hgx] at hgz
    obtain ⟨t, ht⟩ := tr (res R F) (n + 1 - 1) n (n + 1) (by ring) _
      (((hD R (res R F) V (n + 1)).2.2.1 _ _ hgz).2.mp rfl)
    haveI := inj F n
    obtain ⟨t', ht'⟩ := hF R ((res R F).X n) g t
    change Sec.res g t' = t at ht'
    have hzg : Sec.res g (z0 - Sec.map ((res R F).d n (n + 1)) t') = 0 := by
      rw [rsub, ← map_res, ht', ht, sub_self]
    obtain ⟨x', hx'⟩ := (hD R (res R F) X (n + 1)).1 (z0 - Sec.map ((res R F).d n (n + 1)) t')
      (by rw [msub, hz0c, dd, sub_zero])
    have hxx : x' = x := cls_eq hD F (n + 1) hx' hz0
      (tr (res R F) n (n + 1 - 1) (n + 1) (by ring) _ ⟨-t', by rw [mneg]; abel⟩)
    rw [hxx] at hx'
    have hfz : IsCls (pull R (sch.map f) F (n + 1) x) (Sec.res f (z0 - Sec.map ((res R F).d n (n + 1)) t')) :=
      (hD R (res R F) X (n + 1)).2.2.2.2 f x _ hx'
    rw [hfx] at hfz
    obtain ⟨s, hs⟩ := tr (res R F) (n + 1 - 1) n (n + 1) (by ring) _
      (((hD R (res R F) U (n + 1)).2.2.1 _ _ hfz).2.mp rfl)
    have hsc : Sec.map ((res R F).d n (n + 1)) (Sec.res a s) = 0 := by
      rw [map_res, hs, res_res, hw, ← res_res, hzg, rzero]
    obtain ⟨w, hw'⟩ := (hD R (res R F) W n).1 _ hsc
    exact ⟨w, s, _, hw', hx', hs.symm, hzg⟩
  · intro w
    constructor
    · rintro ⟨s, z, hws, hz0, hfz, hgz⟩
      obtain ⟨t, ht⟩ := tr (res R F) (n + 1 - 1) n (n + 1) (by ring) _
        (((hD R (res R F) X (n + 1)).2.2.1 _ _ hz0).2.mp rfl)
      have hu : Sec.map ((res R F).d n (n + 1)) (s - Sec.res f t) = 0 := by
        rw [msub, map_res, ht, hfz, sub_self]
      have hv : Sec.map ((res R F).d n (n + 1)) (-Sec.res g t) = 0 := by
        rw [mneg, map_res, ht, hgz, neg_zero]
      obtain ⟨u, hu'⟩ := (hD R (res R F) U n).1 _ hu
      obtain ⟨v, hv'⟩ := (hD R (res R F) V n).1 _ hv
      refine ⟨u, v, ?_⟩
      have h1 : IsCls (pull R (sch.map a) F n u) (Sec.res a (s - Sec.res f t)) :=
        (hD R (res R F) U n).2.2.2.2 a u _ hu'
      have h2 : IsCls (pull R (sch.map b) F n v) (Sec.res b (-Sec.res g t)) :=
        (hD R (res R F) V n).2.2.2.2 b v _ hv'
      have h3 := ((hD R (res R F) W n).2.2.2.1 _ _ _ _ h1 ((hD R (res R F) W n).2.2.2.1 _ _ _ _ h2 h2).2).1
      have hA : Sec.res a (s - Sec.res f t) + -Sec.res b (-Sec.res g t) = Sec.res a s := by
        rw [rsub, rneg, res_res, res_res, hw]
        abel
      rw [hA, ← sub_eq_add_neg] at h3
      exact cls_eq hD F n hws h3 ⟨0, by rw [mzero, sub_self]⟩
    · rintro ⟨u, v, rfl⟩
      obtain ⟨u0, hu0⟩ := (hD R (res R F) U n).2.1 u
      obtain ⟨v0, hv0⟩ := (hD R (res R F) V n).2.1 v
      have hu0c := ((hD R (res R F) U n).2.2.1 u u0 hu0).1
      have hv0c := ((hD R (res R F) V n).2.2.1 v v0 hv0).1
      haveI := inj F n
      obtain ⟨s', hs'⟩ := hF R ((res R F).X n) a (Sec.res b v0)
      change Sec.res a s' = Sec.res b v0 at hs'
      obtain ⟨t, htf, htg⟩ := (hG R ((res R F).X n) a b f g hmv).2 s' v0 hs'
      refine ⟨u0 - s', -Sec.map ((res R F).d n (n + 1)) t, ?_, ?_, ?_, ?_⟩
      · have h1 : IsCls (pull R (sch.map a) F n u) (Sec.res a u0) := (hD R (res R F) U n).2.2.2.2 a u u0 hu0
        have h2 : IsCls (pull R (sch.map b) F n v) (Sec.res b v0) := (hD R (res R F) V n).2.2.2.2 b v v0 hv0
        have h3 := ((hD R (res R F) W n).2.2.2.1 _ _ _ _ h1 ((hD R (res R F) W n).2.2.2.1 _ _ _ _ h2 h2).2).1
        rw [← sub_eq_add_neg, ← sub_eq_add_neg, ← hs', ← rsub] at h3
        exact h3
      · obtain ⟨y, hy⟩ := (hD R (res R F) X (n + 1)).1 (-Sec.map ((res R F).d n (n + 1)) t)
          (by rw [mneg, dd, neg_zero])
        have hy0 : y = 0 := ((hD R (res R F) X (n + 1)).2.2.1 _ _ hy).2.mpr
          (tr (res R F) n (n + 1 - 1) (n + 1) (by ring) _ ⟨-t, mneg _ _⟩)
        rw [hy0] at hy
        exact hy
      · rw [rneg, ← map_res, htf, msub, hu0c, zero_sub]
      · rw [rneg, ← map_res, htg, hv0c, neg_zero]

end LateralTheory.KummerTheory.ExactPf
end
end
