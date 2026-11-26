module

public import Development.EtaleCohomology.EtaleSheaves.HensCut
public import Development.EtaleCohomology.WeilConjectures.FermatCount
public import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertib

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.ColimHensPf
noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.ColimHensPf

variable {B : Type} [CommRing B] {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{0}}
  (β : (Functor.const J).obj (CommRingCat.of B) ⟶ D) {c : Cocone D}

lemma beta_nat {j j' : J} (f : j ⟶ j') (b : B) : (D.map f).hom ((β.app j).hom b) = (β.app j').hom b := by
  have h := congrArg (fun g => g.hom b) (β.naturality f)
  simpa using h.symm

lemma iota_nat (c : Cocone D) {j j' : J} (f : j ⟶ j') (x : D.obj j) :
    (c.ι.app j').hom ((D.map f).hom x) = (c.ι.app j).hom x := by
  have h := congrArg (fun g => g.hom x) (c.w f)
  simpa using h

lemma mapI (I : Ideal B) {j j' : J} (f : j ⟶ j') {x : D.obj j} (hx : x ∈ I.map (β.app j).hom) :
    (D.map f).hom x ∈ I.map (β.app j').hom := by
  have h : (D.map f).hom.comp (β.app j).hom = (β.app j').hom := RingHom.ext (beta_nat β f)
  have := Ideal.mem_map_of_mem (D.map f).hom hx
  rwa [Ideal.map_map, h] at this

def phi (c : Cocone D) : B →+* c.pt :=
  (c.ι.app (IsFiltered.nonempty (C := J)).some).hom.comp (β.app (IsFiltered.nonempty (C := J)).some).hom

lemma phi_eq (c : Cocone D) (j : J) (b : B) : (c.ι.app j).hom ((β.app j).hom b) = phi β c b := by
  let j0 := (IsFiltered.nonempty (C := J)).some
  show _ = (c.ι.app j0).hom ((β.app j0).hom b)
  rw [← iota_nat c (IsFiltered.leftToMax j j0), ← iota_nat c (IsFiltered.rightToMax j j0), beta_nat, beta_nat]

lemma KofI (c : Cocone D) (I : Ideal B) {j : J} {x : D.obj j} (hx : x ∈ I.map (β.app j).hom) :
    (c.ι.app j).hom x ∈ I.map (phi β c) := by
  have h : (c.ι.app j).hom.comp (β.app j).hom = phi β c := RingHom.ext (phi_eq β c j)
  have := Ideal.mem_map_of_mem (c.ι.app j).hom hx
  rwa [Ideal.map_map, h] at this

variable (hc : IsColimit c)
include hc

lemma rep (z : c.pt) : ∃ j, ∃ y : D.obj j, (c.ι.app j).hom y = z :=
  Concrete.isColimit_exists_rep D hc z

lemma rep_above (j : J) (z : c.pt) : ∃ (j' : J) (_ : j ⟶ j') (y : D.obj j'), (c.ι.app j').hom y = z := by
  obtain ⟨j1, y, rfl⟩ := rep hc z
  exact ⟨IsFiltered.max j j1, IsFiltered.leftToMax j j1, (D.map (IsFiltered.rightToMax j j1)).hom y, iota_nat c _ y⟩

lemma eq_later {j : J} (x y : D.obj j) (h : (c.ι.app j).hom x = (c.ι.app j).hom y) :
    ∃ (j' : J) (f : j ⟶ j'), (D.map f).hom x = (D.map f).hom y := by
  obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq D hc x y h
  refine ⟨_, f ≫ IsFiltered.coeqHom f g, ?_⟩
  have hfg' : (D.map f).hom x = (D.map g).hom y := hfg
  calc (D.map (f ≫ IsFiltered.coeqHom f g)).hom x
        = (D.map (IsFiltered.coeqHom f g)).hom ((D.map f).hom x) := by simp
    _ = (D.map (IsFiltered.coeqHom f g)).hom ((D.map g).hom y) := by rw [hfg']
    _ = (D.map (g ≫ IsFiltered.coeqHom f g)).hom y := by simp
    _ = (D.map (f ≫ IsFiltered.coeqHom f g)).hom y := by rw [IsFiltered.coeq_condition]

lemma zero_later {j : J} (x : D.obj j) (h : (c.ι.app j).hom x = 0) :
    ∃ (j' : J) (f : j ⟶ j'), (D.map f).hom x = 0 := by
  obtain ⟨j', f, hf⟩ := eq_later hc x 0 (by rw [h, map_zero])
  exact ⟨j', f, by rw [hf, map_zero]⟩

lemma Krep (I : Ideal B) {k : c.pt} (hk : k ∈ I.map (phi β c)) :
    ∃ j, ∃ x : D.obj j, x ∈ I.map (β.app j).hom ∧ (c.ι.app j).hom x = k := by
  have hk' : k ∈ Ideal.span (phi β c '' I) := hk
  clear hk
  induction hk' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨(IsFiltered.nonempty (C := J)).some, _, Ideal.mem_map_of_mem _ hi, phi_eq β c _ i⟩
  | zero => exact ⟨(IsFiltered.nonempty (C := J)).some, 0, zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨j1, x1, h1, rfl⟩ := hx
    obtain ⟨j2, x2, h2, rfl⟩ := hy
    refine ⟨IsFiltered.max j1 j2, (D.map (IsFiltered.leftToMax j1 j2)).hom x1 +
      (D.map (IsFiltered.rightToMax j1 j2)).hom x2, add_mem (mapI β I _ h1) (mapI β I _ h2), ?_⟩
    rw [map_add (f := _), iota_nat, iota_nat]
  | smul a x _ hx =>
    obtain ⟨j2, x2, h2, rfl⟩ := hx
    obtain ⟨j1, y, rfl⟩ := rep hc a
    refine ⟨IsFiltered.max j1 j2, (D.map (IsFiltered.leftToMax j1 j2)).hom y *
      (D.map (IsFiltered.rightToMax j1 j2)).hom x2, Ideal.mul_mem_left _ _ (mapI β I _ h2), ?_⟩
    rw [map_mul, iota_nat, iota_nat, smul_eq_mul]

lemma memK_descend (I : Ideal B) {j : J} (y : D.obj j) (hy : (c.ι.app j).hom y ∈ I.map (phi β c)) :
    ∃ (j' : J) (f : j ⟶ j'), (D.map f).hom y ∈ I.map (β.app j').hom := by
  obtain ⟨j1, x, hx, hxe⟩ := Krep β hc I hy
  let l := IsFiltered.leftToMax j j1
  let r := IsFiltered.rightToMax j j1
  obtain ⟨j', g, hg⟩ := zero_later hc ((D.map l).hom y - (D.map r).hom x)
    (by rw [map_sub, iota_nat, iota_nat, hxe, sub_self])
  refine ⟨j', l ≫ g, ?_⟩
  rw [map_sub, sub_eq_zero] at hg
  have : (D.map (l ≫ g)).hom y = (D.map (r ≫ g)).hom x := by simpa using hg
  rw [this]
  exact mapI β I _ hx

lemma poly_lift (g : Polynomial c.pt) : ∃ j, g ∈ Polynomial.lifts (c.ι.app j).hom := by
  have mono : ∀ {j j' : J} (f : j ⟶ j') (g : Polynomial c.pt),
      g ∈ Polynomial.lifts (c.ι.app j).hom → g ∈ Polynomial.lifts (c.ι.app j').hom := by
    intro j j' f g ⟨q, hq⟩
    refine ⟨q.map (D.map f).hom, ?_⟩
    have h : (c.ι.app j').hom.comp (D.map f).hom = (c.ι.app j).hom := RingHom.ext (iota_nat c f)
    simp only [Polynomial.coe_mapRingHom] at hq ⊢
    rw [Polynomial.map_map, h, hq]
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨j1, h1⟩ := hp
    obtain ⟨j2, h2⟩ := hq
    exact ⟨_, add_mem (mono (IsFiltered.leftToMax j1 j2) _ h1)
      (mono (IsFiltered.rightToMax j1 j2) _ h2)⟩
  | monomial n a =>
    obtain ⟨j, y, hy⟩ := rep hc a
    exact ⟨j, Polynomial.monomial_mem_lifts n ⟨y, hy⟩⟩

omit hc in
lemma ev_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (p : Polynomial R) (b : R) :
    φ (p.eval b) = (p.map φ).eval (φ b) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]

omit hc in
lemma pmap (c : Cocone D) {j j' : J} (f : j ⟶ j') (p : Polynomial (D.obj j)) :
    (p.map (D.map f).hom).map (c.ι.app j').hom = p.map (c.ι.app j).hom := by
  have h : (c.ι.app j').hom.comp (D.map f).hom = (c.ι.app j).hom := RingHom.ext (iota_nat c f)
  rw [Polynomial.map_map, h]

end LateralTheory.E.ColimHensPf

namespace LateralTheory.E.ColimHensPf
open LateralTheory.E.ColimHensPf

theorem ColimHens_of : LateralTheory.E.HensCut.ColimHens := by
  intro B _ I J _ _ D β c hc ha hb hcc
  refine ⟨I.map (phi β c), ⟨?_, ?_⟩, ⟨RingEquiv.ofBijective
    (Ideal.quotientMap (I.map (phi β c)) (phi β c) Ideal.le_comap_map) ⟨?_, ?_⟩⟩⟩
  ·
    intro k hk
    rw [Ring.mem_jacobson_iff]
    intro y
    obtain ⟨j, x, hx, hxe⟩ := Krep β hc I (Ideal.mul_mem_right y _ hk)
    obtain ⟨j', f, hu⟩ := hb j x hx
    have := hu.map (c.ι.app j').hom
    rw [iota_nat, map_add (f := _), map_one, hxe, add_comm] at this
    exact this
  ·
    intro g hg a₀ hev hder
    by_cases hnt : Nontrivial c.pt
    swap
    · rw [not_nontrivial_iff_subsingleton] at hnt
      exact ⟨a₀, Subsingleton.elim _ _, by rw [sub_self]; exact zero_mem _⟩
    obtain ⟨j1, hj1⟩ := poly_lift hc g
    haveI : Nontrivial (((Functor.const J).obj c.pt).obj j1) := hnt
    obtain ⟨p, hp, -, hpm⟩ := Polynomial.lifts_and_degree_eq_and_monic hj1 hg
    obtain ⟨w, hw⟩ := hder.exists_right_inv
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective w
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (I.map (phi β c))), Ideal.Quotient.eq] at hw
    obtain ⟨j2, f12, b0, hb0⟩ := rep_above hc j1 a₀
    obtain ⟨j3, f23, v, hv⟩ := rep_above hc j2 u
    set p3 := p.map (D.map (f12 ≫ f23)).hom with hp3
    set b3 := (D.map f23).hom b0 with hb3
    have hp3g : p3.map (c.ι.app j3).hom = g := by rw [hp3, pmap, hp]
    have hb3a : (c.ι.app j3).hom b3 = a₀ := by rw [hb3, iota_nat, hb0]
    have hy1 : (c.ι.app j3).hom (p3.eval b3) ∈ I.map (phi β c) := by
      rw [ev_map, hp3g, hb3a]; exact hev
    have hy2 : (c.ι.app j3).hom (p3.derivative.eval b3 * v - 1) ∈ I.map (phi β c) := by
      rw [map_sub, map_mul, map_one, ev_map, ← Polynomial.derivative_map, hp3g, hb3a, hv]; exact hw
    obtain ⟨j4, f34, h4⟩ := memK_descend β hc I _ hy1
    obtain ⟨j5, f45, h5⟩ := memK_descend β hc I ((D.map f34).hom (p3.derivative.eval b3 * v - 1))
      (by rw [iota_nat]; exact hy2)
    let h := f34 ≫ f45
    set P := p3.map (D.map h).hom with hP
    set b := (D.map h).hom b3 with hb
    have hPm : P.Monic := (hpm.map _).map _
    have hPe : P.eval b ∈ I.map (β.app j5).hom := by
      rw [hP, hb, ← ev_map]
      have := mapI β I f45 h4
      simpa [h] using this
    have hPd : IsUnit (Ideal.Quotient.mk (I.map (β.app j5).hom) (P.derivative.eval b)) := by
      have e : (D.map h).hom (p3.derivative.eval b3 * v - 1) = P.derivative.eval b * (D.map h).hom v - 1 := by
        rw [map_sub, map_mul, map_one, ev_map, ← Polynomial.derivative_map]
      have h5' : P.derivative.eval b * (D.map h).hom v - 1 ∈ I.map (β.app j5).hom := by
        rw [← e]; simpa [h] using h5
      refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ ((D.map h).hom v)) ?_
      rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
      exact h5'
    obtain ⟨j6, f56, a, ha1, ha2⟩ := hcc j5 P b hPm hPe hPd
    refine ⟨(c.ι.app j6).hom a, ?_, ?_⟩
    · have hr := ha1.map (f := (c.ι.app j6).hom)
      rwa [pmap, hP, pmap, hp3g] at hr
    · have := KofI β c I ha2
      rwa [map_sub, iota_nat, hb, iota_nat, hb3a] at this
  ·
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha0
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at ha0
    obtain ⟨j, x, hx, hxe⟩ := Krep β hc I ha0
    obtain ⟨j', f, hf⟩ := zero_later hc ((β.app j).hom b - x)
      (by rw [map_sub, hxe, phi_eq, sub_self])
    rw [map_sub, sub_eq_zero, beta_nat] at hf
    have hm : (β.app j').hom b ∈ I.map (β.app j').hom := by rw [hf]; exact mapI β I f hx
    apply (ha j').1
    rw [map_zero, Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hm
  ·
    intro z
    obtain ⟨z', rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨j, y, rfl⟩ := rep hc z'
    obtain ⟨w, hw⟩ := (ha j).2 (Ideal.Quotient.mk _ y)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective w
    refine ⟨Ideal.Quotient.mk I b, ?_⟩
    rw [Ideal.quotientMap_mk] at hw ⊢
    rw [Ideal.Quotient.eq] at hw ⊢
    have := KofI β c I hw
    rwa [map_sub, phi_eq] at this

end LateralTheory.E.ColimHensPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafCoprodPf
section -- merged from Development.EtaleCohomology.WeilConjectures.GlueOfSig
section -- merged from Development.EtaleCohomology.WeilConjectures.GluePf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

namespace LateralTheory.EWeil.Gys.LV.GluePf
open LateralTheory.EWeil LateralTheory.EWeil.Gys LateralTheory.EWeil.Gys.LV

def ShvSigma : Prop := ∀ (R : Type) [CommRing R] (F : GlobalTheory.EtC.Shv R) {T : Type} {Y : T → Scheme.{0}} (c : Cofan Y), IsColimit c →
  Function.Bijective (fun (s : GlobalTheory.EtC.Sec F c.pt) (t : T) => GlobalTheory.EtC.Sec.res (c.inj t) s)

end LateralTheory.EWeil.Gys.LV.GluePf
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.EWeil.Gys.LV.GluePf

theorem shvSigma : ShvSigma := by
  intro R _ F T Y c hc
  let G : Scheme.{0}ᵒᵖ ⥤ Type 1 := F.obj ⋙ forget _
  have hG : Presieve.IsSheaf Scheme.zariskiTopology G :=
    Presieve.isSheaf_of_le G Scheme.zariskiTopology_le_etaleTopology
      ((isSheaf_iff_isSheaf_of_type _ G).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ F.obj (forget _)).1 F.property))
  have : PreservesLimitsOfShape (Discrete T) G := preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hG
  let hL : IsLimit (G.mapCone c.op) := isLimitOfPreserves G (Cofan.IsColimit.op hc)
  let e := Types.isLimitEquivSections hL
  have he : ∀ s t, (e s).1 ⟨t⟩ = GlobalTheory.EtC.Sec.res (c.inj t) s := fun s t => rfl
  constructor
  · intro s₁ s₂ h
    apply e.injective
    apply Subtype.ext
    funext ⟨t⟩
    rw [he, he]
    exact congrFun h t
  · intro y
    let sec : (Discrete.functor (fun a => op (Y a)) ⋙ G).sections :=
      ⟨fun j => y j.as, by
        rintro ⟨j⟩ ⟨j'⟩ ⟨h⟩
        cases h
        show G.map (𝟙 _) _ = _
        rw [G.map_id]; rfl⟩
    refine ⟨e.symm sec, ?_⟩
    funext t
    show GlobalTheory.EtC.Sec.res (c.inj t) (e.symm sec) = y t
    rw [← he, e.apply_symm_apply]

end LateralTheory.EWeil.Gys.LV.GluePf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LSchClsPfYon
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.L_sch_clsPfYon

variable (R : Type) [CommRing R]

def yon0 (G : Shv R) (X : Scheme.{0}) (z : Sec G X) : (freeP R).obj (yoneda.obj X) ⟶ G.obj where
  app U := ModuleCat.freeDesc (R := ULift.{1} R) (X := ULift.{1} (U.unop ⟶ X)) (TypeCat.ofHom (fun g : ULift.{1} (U.unop ⟶ X) => (G.obj.map g.down.op).hom z))
  naturality U V f := by
    apply ModuleCat.free_hom_ext (R := ULift.{1} R)
    rintro ⟨g⟩
    have e1 : (((freeP R).obj (yoneda.obj X)).map f).hom (ModuleCat.freeMk (ULift.up g)) =
        ModuleCat.freeMk (ULift.up (f.unop ≫ g)) := ModuleCat.free_map_apply (R := ULift.{1} R) _ _
    erw [ConcreteCategory.comp_apply, e1, ConcreteCategory.comp_apply, ModuleCat.freeDesc_apply]
    erw [ModuleCat.freeDesc_apply]
    show (G.obj.map (f.unop ≫ g).op).hom z = (G.obj.map f).hom ((G.obj.map g.op).hom z)
    rw [op_comp, Functor.map_comp]
    rfl

def yon (G : Shv R) (X : Scheme.{0}) (z : Sec G X) : (free R).obj (yoneda.obj X) ⟶ G :=
  ⟨sheafifyLift Scheme.etaleTopology (yon0 R G X z) G.property⟩

theorem yon_gen (G : Shv R) (X : Scheme.{0}) (z : Sec G X) : Sec.map (yon R G X z) (freeGen R _ X (𝟙 X)) = z := by
  have h := toSheafify_sheafifyLift Scheme.etaleTopology (yon0 R G X z) G.property
  have := congrArg (fun φ => (φ.app (op X)).hom (ModuleCat.freeMk (ULift.up (𝟙 X)))) h
  refine this.trans ?_
  dsimp only [yon0]
  erw [ModuleCat.freeDesc_apply]
  simp

theorem yon_ext {G : Shv R} {X : Scheme.{0}} (φ ψ : (free R).obj (yoneda.obj X) ⟶ G)
    (h : Sec.map φ (freeGen R _ X (𝟙 X)) = Sec.map ψ (freeGen R _ X (𝟙 X))) : φ = ψ := by
  have key : ∀ (U : Scheme.{0}) (g : U ⟶ X), Sec.map φ (freeGen R _ U g) = Sec.map ψ (freeGen R _ U g) := by
    intro U g
    have hg : freeGen R (yoneda.obj X) U g = Sec.res g (freeGen R _ X (𝟙 X)) := by
      rw [LateralTheory.E.LeafKumSpecPf.freeGen_res]
      simp
    rw [hg, ← LateralTheory.E.LeafKumSpecPf.sec_res_map, ← LateralTheory.E.LeafKumSpecPf.sec_res_map, h]
  have hv : φ.hom = ψ.hom := by
    apply sheafify_hom_ext Scheme.etaleTopology _ _ G.property
    refine NatTrans.ext (funext fun U => ?_)
    apply ModuleCat.free_hom_ext (R := ULift.{1} R)
    rintro ⟨g⟩
    exact key U.unop g
  first | exact Sheaf.hom_ext hv | (cases φ; cases ψ; cases hv; rfl)

theorem yon_res {G : Shv R} {X : Scheme.{0}} (z : Sec G X) (U : Scheme.{0}) (g : U ⟶ X) :
    Sec.map (yon R G X z) (freeGen R _ U g) = Sec.res g z := by
  have hg : freeGen R (yoneda.obj X) U g = Sec.res g (freeGen R _ X (𝟙 X)) := by
    rw [LateralTheory.E.LeafKumSpecPf.freeGen_res]
    simp
  rw [hg, ← LateralTheory.E.LeafKumSpecPf.sec_res_map, yon_gen]

end LateralTheory.E.L_sch_clsPfYon
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafCoprodPf

section General
variable {C : Type*} [Category C] [Preadditive C]

theorem sum_comp_split {K L : CochainComplex C ℤ} {n : ℤ} {ι : Type} {Kj : ι → CochainComplex C ℤ}
    (i : ∀ j, Kj j ⟶ K) (p : ∀ j, K ⟶ Kj j) (α : Cochain K L n) (s : Finset ι) :
    ∑ j ∈ s, (Cochain.ofHom (p j)).comp ((Cochain.ofHom (i j)).comp α (zero_add n)) (zero_add n) =
      (Cochain.ofHom (∑ j ∈ s, p j ≫ i j)).comp α (zero_add n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, Cochain.ofHom_add, Cochain.add_comp,
      ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]

theorem cls_inj {K L : CochainComplex C ℤ} {ι : Type} [Fintype ι] {Kj : ι → CochainComplex C ℤ}
    (i : ∀ j, Kj j ⟶ K) (p : ∀ j, K ⟶ Kj j) (hsum : ∑ j, p j ≫ i j = 𝟙 K) (n : ℤ)
    (x : CohomologyClass K L n) (hx : ∀ j, cpre (Cocycle.ofHom (i j)) L n n (zero_add n) x = 0) : x = 0 := by
  classical
  obtain ⟨α, rfl⟩ := x.mk_surjective
  have h : ∀ j, ∃ β : Cochain (Kj j) L (n - 1),
      δ (n - 1) n β = (Cochain.ofHom (i j)).comp α.1 (zero_add n) := by
    intro j
    have := hx j
    rw [cpre_mk, CohomologyClass.mk_eq_zero_iff] at this
    obtain ⟨m, hm, β, hβ⟩ := this
    obtain rfl : m = n - 1 := by omega
    exact ⟨β, by rw [hβ]; rfl⟩
  choose β hβ using h
  have hδ : ∀ s : Finset ι, δ (n - 1) n (∑ j ∈ s, (Cochain.ofHom (p j)).comp (β j) (zero_add _)) =
      ∑ j ∈ s, (Cochain.ofHom (p j)).comp ((Cochain.ofHom (i j)).comp α.1 (zero_add n)) (zero_add n) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, δ_add, ih, δ_ofHom_comp, hβ]
  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨n - 1, by omega, ∑ j, (Cochain.ofHom (p j)).comp (β j) (zero_add _), ?_⟩
  rw [hδ, sum_comp_split, hsum, Cochain.id_comp]

end General

section Sheaves
variable (R : Type) [CommRing R]

abbrev W : Spc ⥤ SimplicialObject (Shv R) := (SimplicialObject.whiskering _ _).obj (free R)

abbrev G : SimplicialObject (Shv R) ⥤ Cx R :=
  AlgebraicTopology.alternatingFaceMapComplex (Shv R) ⋙ ComplexShape.embeddingDownNat.extendFunctor (Shv R)

variable {m : ℕ} (Z : Fin m → Scheme.{0})

def gen (j : Fin m) : Sec ((free R).obj (yoneda.obj (Z j))) (∐ Z) :=
  ((LateralTheory.EWeil.Gys.LV.GluePf.shvSigma R ((free R).obj (yoneda.obj (Z j))) (Cofan.mk (∐ Z) (Sigma.ι Z))
    (coproductIsCoproduct Z)).2
    (Pi.single (M := fun t => Sec ((free R).obj (yoneda.obj (Z j))) (Z t)) j (freeGen R _ (Z j) (𝟙 (Z j))))).choose

theorem gen_res (j t : Fin m) : Sec.res (Sigma.ι Z t) (gen R Z j) =
    Pi.single (M := fun t => Sec ((free R).obj (yoneda.obj (Z j))) (Z t)) j (freeGen R _ (Z j) (𝟙 (Z j))) t :=
  congrFun ((LateralTheory.EWeil.Gys.LV.GluePf.shvSigma R ((free R).obj (yoneda.obj (Z j))) (Cofan.mk (∐ Z) (Sigma.ι Z))
    (coproductIsCoproduct Z)).2
    (Pi.single (M := fun t => Sec ((free R).obj (yoneda.obj (Z j))) (Z t)) j (freeGen R _ (Z j) (𝟙 (Z j))))).choose_spec t

def pr (j : Fin m) : (free R).obj (yoneda.obj (∐ Z)) ⟶ (free R).obj (yoneda.obj (Z j)) :=
  LateralTheory.E.L_sch_clsPfYon.yon R _ _ (gen R Z j)

theorem sec_comp {F F' F'' : Shv R} (φ : F ⟶ F') (ψ : F' ⟶ F'') {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem sum_pr : ∑ j, pr R Z j ≫ (free R).map (yoneda.map (Sigma.ι Z j)) = 𝟙 _ := by
  classical
  apply LateralTheory.E.L_sch_clsPfYon.yon_ext
  apply (LateralTheory.EWeil.Gys.LV.GluePf.shvSigma R ((free R).obj (yoneda.obj (∐ Z))) (Cofan.mk (∐ Z) (Sigma.ι Z))
    (coproductIsCoproduct Z)).1
  funext t
  change Sec.res (Sigma.ι Z t) _ = Sec.res (Sigma.ι Z t) _
  rw [LateralTheory.E.LeafKumSpecPf.sec_res_map, LateralTheory.E.LeafKumSpecPf.sec_res_map]
  erw [LateralTheory.E.LeafKumSpecPf.freeGen_res]
  have hy : (ConcreteCategory.hom ((yoneda.obj (∐ Z)).map (Sigma.ι Z t).op)) (𝟙 (∐ Z)) = Sigma.ι Z t := by
    rfl
  rw [hy, LateralTheory.EtaleFoundations.EvDeltaPf.sec_sum, Finset.sum_eq_single t]
  · rw [sec_comp, pr, LateralTheory.E.L_sch_clsPfYon.yon_res, gen_res, Pi.single_eq_same,
      LateralTheory.EtaleFoundations.EvDeltaPf.freeGen_map]
    rfl
  · intro b _ hb
    rw [sec_comp, pr, LateralTheory.E.L_sch_clsPfYon.yon_res, gen_res, Pi.single_eq_of_ne (Ne.symm hb)]
    exact map_zero _
  · simp

def prS (j : Fin m) : (W R).obj (sch.obj (∐ Z)) ⟶ (W R).obj (sch.obj (Z j)) where
  app _ := pr R Z j
  naturality a b θ := by
    change (free R).map (𝟙 _) ≫ pr R Z j = pr R Z j ≫ (free R).map (𝟙 _)
    simp

theorem sum_prS : ∑ j, prS R Z j ≫ (W R).map (sch.map (Sigma.ι Z j)) = 𝟙 _ := by
  refine NatTrans.ext (funext fun a => ?_)
  rw [NatTrans.app_sum]
  exact sum_pr R Z

end Sheaves

theorem LeafCoprod_of : LateralTheory.E.E4.LeafCoprod := by
  intro _ q n i m Z hZ
  have : ∀ j, Finite (Ht q (sch.obj (Z j)) n i) := hZ
  refine Finite.of_injective (AddMonoidHom.pi fun j => pull (ZMod q) (sch.map (Sigma.ι Z j)) (tw q i) n) ?_
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have hsum : ∑ j, (G (ZMod q)).map (prS (ZMod q) Z j) ≫ (chains (ZMod q)).map (sch.map (Sigma.ι Z j)) = 𝟙 _ := by
    have h1 : (G (ZMod q)).map (∑ j, prS (ZMod q) Z j ≫ (W (ZMod q)).map (sch.map (Sigma.ι Z j))) = 𝟙 _ := by
      rw [sum_prS, CategoryTheory.Functor.map_id]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Functor.map_sum] at h1
    simp only [Functor.map_comp] at h1
    exact h1
  exact cls_inj (fun j => (chains (ZMod q)).map (sch.map (Sigma.ι Z j))) (fun j => (G (ZMod q)).map (prS (ZMod q) Z j))
    hsum n x (fun j => congrFun hx j)

end LateralTheory.E.LeafCoprodPf
end
end
