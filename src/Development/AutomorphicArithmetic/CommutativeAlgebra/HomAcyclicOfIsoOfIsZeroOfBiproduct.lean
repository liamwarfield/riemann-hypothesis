module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CompLeft
public import Development.AutomorphicArithmetic.CommutativeAlgebra.PullCupPowEqCupPowPull

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.HomAcyclicOfIsoOfIsZeroOfBiproduct
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafGhostCut UpperTheory.Et.Loc

namespace UpperTheory.AdditiveHomTwist

universe v₁ v₂ u₁ u₂

private theorem biprod_iso {C : Type u₁} [Category.{v₁} C] [Preadditive C] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (S₁ S₂ : C) [HasBinaryBiproduct S₁ S₂] (T : D)
    (s₁ : F.obj S₁ ⟶ T) (p₁ : T ⟶ F.obj S₁) (s₂ : F.obj S₂ ⟶ T) (p₂ : T ⟶ F.obj S₂)
    (h₁ : s₁ ≫ p₁ = 𝟙 _) (h₂ : s₂ ≫ p₂ = 𝟙 _) (h₁₂ : s₁ ≫ p₂ = 0) (h₂₁ : s₂ ≫ p₁ = 0)
    (ht : p₁ ≫ s₁ + p₂ ≫ s₂ = 𝟙 _) : Nonempty (F.obj (S₁ ⊞ S₂) ≅ T) := by
  refine ⟨{ hom := F.map biprod.fst ≫ s₁ + F.map biprod.snd ≫ s₂
            inv := p₁ ≫ F.map biprod.inl + p₂ ≫ F.map biprod.inr
            hom_inv_id := ?_
            inv_hom_id := ?_ }⟩
  · simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
      reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₁₂, reassoc_of% h₂₁,
      zero_comp, comp_zero, add_zero, zero_add]
    rw [← F.map_comp, ← F.map_comp, ← F.map_add (f := _), biprod.total, F.map_id]
  · simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc]
    rw [← F.map_comp_assoc, ← F.map_comp_assoc, ← F.map_comp_assoc, ← F.map_comp_assoc]
    simp only [biprod.inl_fst, biprod.inl_snd, biprod.inr_fst, biprod.inr_snd,
      F.map_id, F.map_zero, Category.id_comp, zero_comp, comp_zero, add_zero, zero_add]
    exact ht

variable {B : Scheme.{0}} {q : ℕ}

private noncomputable def hm {P P' : B.Etale ⥤ Shv (ZMod q)} (φ : P ⟶ P') (J : Shv (ZMod q)) : HP P' J ⟶ HP P J :=
  Functor.whiskerRight (NatTrans.op φ) _

private theorem hm_id (P : B.Etale ⥤ Shv (ZMod q)) (J : Shv (ZMod q)) : hm (𝟙 P) J = 𝟙 _ := by
  unfold hm
  rw [NatTrans.op_id]
  exact Functor.whiskerRight_id' _

private theorem hm_comp {P P' P'' : B.Etale ⥤ Shv (ZMod q)} (φ : P ⟶ P') (ψ : P' ⟶ P'') (J : Shv (ZMod q)) :
    hm ψ J ≫ hm φ J = hm (φ ≫ ψ) J := by
  refine NatTrans.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  change φ.app U.unop ≫ ψ.app U.unop ≫ (x : P''.obj U.unop ⟶ J) = (φ.app U.unop ≫ ψ.app U.unop) ≫ x
  exact (Category.assoc _ _ _).symm

private theorem hm_zero (P P' : B.Etale ⥤ Shv (ZMod q)) (J : Shv (ZMod q)) : hm (0 : P ⟶ P') J = 0 := by
  refine NatTrans.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  change (0 : P.obj U.unop ⟶ P'.obj U.unop) ≫ (x : P'.obj U.unop ⟶ J) = 0
  exact zero_comp

private theorem hm_add {P P' : B.Etale ⥤ Shv (ZMod q)} (φ ψ : P ⟶ P') (J : Shv (ZMod q)) :
    hm (φ + ψ) J = hm φ J + hm ψ J := by
  refine NatTrans.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  change (φ.app U.unop + ψ.app U.unop) ≫ (x : P'.obj U.unop ⟶ J) = φ.app U.unop ≫ x + ψ.app U.unop ≫ x
  exact Preadditive.add_comp _ _ _ _ _ _

private theorem transfer (S : SShv B q) [Injective S] {G : B.Etaleᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))} (e : S.obj ≅ G) :
    ∃ h : Presheaf.IsSheaf (EtTop B) G, Injective (⟨G, h⟩ : SShv B q) := by
  have h : Presheaf.IsSheaf (EtTop B) G := (Presheaf.isSheaf_of_iso_iff e).1 S.property
  refine ⟨h, ?_⟩
  have i : S ≅ (⟨G, h⟩ : SShv B q) :=
    (fullyFaithfulSheafToPresheaf (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q)))).preimageIso e
  exact Injective.of_iso i inferInstance

end UpperTheory.AdditiveHomTwist

open UpperTheory.AdditiveHomTwist ZeroObject in
theorem UpperTheory.homAcyclic_of_iso_of_isZero_of_biproduct :
    ∀ (q : ℕ) (B : Scheme.{0}), (∀ P P' : B.Etale ⥤ Shv (ZMod q), Nonempty (P ≅ P') → Good P → Good P') ∧ (∀ P : B.Etale ⥤ Shv (ZMod q), (∀ U, IsZero (P.obj U)) → Good P) ∧ ∀ (P P₁ P₂ : B.Etale ⥤ Shv (ZMod q)) (i₁ : P₁ ⟶ P) (r₁ : P ⟶ P₁) (i₂ : P₂ ⟶ P) (r₂ : P ⟶ P₂), i₁ ≫ r₁ = 𝟙 _ → i₂ ≫ r₂ = 𝟙 _ → i₁ ≫ r₂ = 0 → i₂ ≫ r₁ = 0 → r₁ ≫ i₁ + r₂ ≫ i₂ = 𝟙 _ → Good P₁ → Good P₂ → Good P := by
  intro q B
  refine ⟨?_, ?_, ?_⟩
  · intro P P' hPP hP
    obtain ⟨e⟩ := hPP
    unfold Good at hP ⊢
    intro J hJ
    obtain ⟨h, hi⟩ := hP J hJ
    have e' : HP P J ≅ HP P' J :=
      { hom := hm e.inv J
        inv := hm e.hom J
        hom_inv_id := by rw [hm_comp, e.hom_inv_id, hm_id]
        inv_hom_id := by rw [hm_comp, e.inv_hom_id, hm_id] }
    exact transfer (⟨HP P J, h⟩ : SShv B q) e'
  · intro P hP
    unfold Good
    intro J hJ
    have hz : IsZero (HP P J) := by
      rw [IsZero.iff_id_eq_zero]
      have h0 : (𝟙 P : P ⟶ P) = 0 :=
        NatTrans.ext (funext fun U => (hP U).eq_of_src _ _)
      rw [← hm_id, h0, hm_zero]
    have hz0 : IsZero ((sheafToPresheaf (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q)))).obj
        (0 : SShv B q)) :=
      Functor.map_isZero _ (isZero_zero _)
    exact transfer (0 : SShv B q) (hz0.iso hz)
  · intro P P₁ P₂ i₁ r₁ i₂ r₂ h1 h2 h12 h21 ht hP₁ hP₂
    unfold Good at hP₁ hP₂ ⊢
    intro J hJ
    obtain ⟨g₁, hi₁⟩ := hP₁ J hJ
    obtain ⟨g₂, hi₂⟩ := hP₂ J hJ
    let S₁ : SShv B q := ⟨HP P₁ J, g₁⟩
    let S₂ : SShv B q := ⟨HP P₂ J, g₂⟩
    haveI : Injective S₁ := hi₁
    haveI : Injective S₂ := hi₂
    obtain ⟨e⟩ := biprod_iso (sheafToPresheaf (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q))))
      S₁ S₂ (HP P J) (hm r₁ J) (hm i₁ J) (hm r₂ J) (hm i₂ J)
      (by rw [hm_comp, h1, hm_id]; rfl) (by rw [hm_comp, h2, hm_id]; rfl)
      (by rw [hm_comp, h21, hm_zero]) (by rw [hm_comp, h12, hm_zero])
      (by rw [hm_comp, hm_comp, ← hm_add, ht, hm_id])
    exact transfer (S₁ ⊞ S₂) e
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsSectionRepresentingRelativeClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

noncomputable section

private def cut (C : DC) (x : C.Tot) : C.Tot
  | 0, s => x 0 s
  | _ + 1, _ => 0

private theorem unit_map {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) (u : ℤˣ) (a : A) :
    f (u • a) = u • f a := by
  simp [Units.smul_def]

private theorem split (C : DC) (rd : ∀ p s, C.A (p + 1) s →+ C.A p s)
    (h0 : ∀ p s, Even p → ∀ a, C.δ p s a = 0)
    (h1 : ∀ p s, Odd p → ∀ a, C.δ p s (rd p s a) = a)
    (h2 : ∀ p s, Odd p → ∀ a, rd p s (C.δ p s a) = a)
    (h3 : ∀ p s t a, C.d p s t (rd p s a) = rd p t (C.d (p + 1) s t a))
    (m : ℤ) (x : C.Tot) (hd : C.Deg m x) (hD : C.D m x = 0) :
    C.Deg m (cut C x) ∧ C.D m (cut C x) = 0 ∧ C.Deg m (x - cut C x) ∧
      ∃ y, C.Deg (m - 1) y ∧ C.D (m - 1) y = x - cut C x := by
  have key : ∀ (q : ℕ) (s : ℤ) (a : C.A q s), m.negOnePow • m.negOnePow • a = a := by
    intro q s a
    rw [smul_smul, Int.units_mul_self, one_smul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p s hps
    cases p with
    | zero => exact hd 0 s hps
    | succ p => rfl
  · funext p t
    cases p with
    | zero =>
      have := congrFun (congrFun hD 0) t
      simpa [DC.D, cut] using this
    | succ p =>
      cases p with
      | zero => simp [DC.D, cut, h0 0 t ⟨0, rfl⟩]
      | succ p => simp [DC.D, cut]
  · intro p s hps
    cases p with
    | zero => simp [cut]
    | succ p => simp [cut, hd (p + 1) s hps]
  · refine ⟨fun p t => if Odd p then m.negOnePow • rd p t (x (p + 1) t) else 0, ?_, ?_⟩
    · intro p t hpt
      dsimp only
      split_ifs
      · rw [hd (p + 1) t (by push_cast; omega)]
        simp
      · rfl
    · funext p t
      cases p with
      | zero => simp [DC.D, cut]
      | succ p =>
        have hx := congrFun (congrFun hD (p + 2)) t
        simp only [DC.D] at hx
        simp only [DC.D, cut, sub_add_cancel, Pi.sub_apply, sub_zero]
        rcases Nat.even_or_odd p with hp | hp
        · have hp1 : Odd (p + 1) := hp.add_one
          have hp0 : ¬ Odd p := Nat.not_odd_iff_even.mpr hp
          simp only [hp1, hp0, if_true, if_false, map_zero, smul_zero, add_zero]
          rw [unit_map, h3]
          have hx' : C.d (p + 2) (t - 1) t (x (p + 2) (t - 1)) = m.negOnePow • C.δ (p + 1) t (x (p + 1) t) := by
            rw [Int.negOnePow_succ] at hx
            rw [eq_neg_of_add_eq_zero_left hx, Units.neg_smul, neg_neg]
          rw [hx', unit_map, h2 _ _ hp1, key]
        · have hp1 : ¬ Odd (p + 1) := by rw [Nat.odd_add_one]; exact not_not.mpr hp
          simp only [hp1, hp, if_true, if_false, map_zero, zero_add]
          rw [unit_map, h1 _ _ hp, key]

private theorem alt {G : Type*} [AddCommGroup G] (b : G) (n : ℕ) :
    ∑ i : Fin n, (-1 : ℤ) ^ (i : ℕ) • b = if Even n then 0 else b := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    by_cases h : Even n
    · have h' : ¬ Even (n + 1) := by simpa [Nat.even_add_one] using h
      simp [h, h', h.neg_one_pow]
    · have h' : Even (n + 1) := by simpa [Nat.even_add_one] using h
      have ho : Odd n := Nat.not_even_iff_odd.1 h
      simp [h, h', ho.neg_one_pow]

section Concrete
variable {R : Type} [CommRing R] {X : Scheme.{0}}

private def rdF (Z : Sub (sch.obj X)) (hZ : ∀ (p q : ℕ) (W : Scheme.{0}) (t : W ⟶ X), Z.mem p W t → Z.mem q W t)
    (p : ℕ) (M : Shv R) : Fam Z (p + 1) M →+ Fam Z p M where
  toFun a := ⟨fun W t => a.1 W t, fun V W g t => a.2.1 V W g t, fun W t h => a.2.2 W t (hZ _ _ _ _ h)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem delta_apply (Z : Sub (sch.obj X)) (p : ℕ) (M : Shv R) (a : Fam Z p M) (W : Scheme.{0}) (t : W ⟶ X) :
    (Fam.δ Z p M (0 : ℤ).negOnePow a).1 W t = if Even (p + 2) then 0 else a.1 W t := by
  change (0 : ℤ).negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • a.1 W t = _
  rw [Int.negOnePow_zero, one_smul, alt]

private theorem fam_split (Z : Sub (sch.obj X)) (hZ : ∀ (p q : ℕ) (W : Scheme.{0}) (t : W ⟶ X), Z.mem p W t → Z.mem q W t)
    (K : Cx R) (m : ℤ) (x : (famDC Z K 0).Tot) (hd : (famDC Z K 0).Deg m x) (hD : (famDC Z K 0).D m x = 0) :
    (famDC Z K 0).Deg m (cut _ x) ∧ (famDC Z K 0).D m (cut _ x) = 0 ∧ (famDC Z K 0).Deg m (x - cut _ x) ∧
      ∃ y, (famDC Z K 0).Deg (m - 1) y ∧ (famDC Z K 0).D (m - 1) y = x - cut _ x := by
  refine split (famDC Z K 0) (fun p s => rdF Z hZ p (K.X (s + 0))) ?_ ?_ ?_ ?_ m x hd hD
  · intro p s hp (a : Fam Z p (K.X (s + 0)))
    apply Subtype.ext
    funext W (t : W ⟶ X)
    have e := delta_apply Z p (K.X (s + 0)) a W t
    have : Even (p + 2) := by rw [Nat.even_add]; simp [hp]
    rw [if_pos this] at e
    exact e
  · intro p s hp (a : Fam Z (p + 1) (K.X (s + 0)))
    apply Subtype.ext
    funext W (t : W ⟶ X)
    have e := delta_apply Z p (K.X (s + 0)) (rdF Z hZ p (K.X (s + 0)) a) W t
    have : ¬ Even (p + 2) := by rw [Nat.even_add]; simp [Nat.not_even_iff_odd.mpr hp]
    rw [if_neg this] at e
    exact e
  · intro p s hp (a : Fam Z p (K.X (s + 0)))
    apply Subtype.ext
    funext W (t : W ⟶ X)
    have e := delta_apply Z p (K.X (s + 0)) a W t
    have : ¬ Even (p + 2) := by rw [Nat.even_add]; simp [Nat.not_even_iff_odd.mpr hp]
    rw [if_neg this] at e
    exact e
  · intro p s t a
    rfl

end Concrete

theorem UpperTheory.exists_section_representing_relativeClass :
    ∀ (q : ℕ) (X : Scheme.{0}) (U : X.Opens) (m j : ℤ) (c : Hs q (opn U) m j), ∃ β : Sec ((res _ (tw q j)).X m) X, IsRep U β c.1 := by
  intro q X U m j c
  have TM := UpperTheory.relativeCohomology_isTotalModel_of_image q (opn U) j 0 m m (by simp)
  have hZ : ∀ (p q : ℕ) (W : Scheme.{0}) (t : W ⟶ X),
      (Sub.img (opn U).hom).mem p W t → (Sub.img (opn U).hom).mem q W t :=
    fun _ _ _ _ h => h
  obtain ⟨x, hxd, hxD, hxr⟩ := TM.surj c
  obtain ⟨hcd, hcD, hrd, y, hyd, hyD⟩ := fam_split (Sub.img (opn U).hom) hZ _ m x hxd hxD
  obtain ⟨c0, hc0⟩ := TM.ex _ hcd hcD
  have hsub := TM.sub _ _ _ _ hxr hc0
  have hz : c - c0 = 0 := (TM.zero _ _ hrd hsub).2 ⟨y, hyd, hyD⟩
  have hcc : c = c0 := sub_eq_zero.mp hz
  rw [← hcc] at hc0
  obtain ⟨γ, hγ, hcomp, hinr⟩ := hc0
  have cover := (UpperTheory.doubleMappingCylinder_cochain_extension (ZMod q) (opn U)).1
  have hhi : ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + m = s) (W : Scheme)
      (z : Sx (dbl (opn U)) (p + 1) W), ev γ.1 (p + 1) s h W z = 0 := by
    intro p s h W z
    rcases cover (p + 1) W z with ⟨z', rfl⟩ | ⟨z', rfl⟩
    · have e : ∀ h' : -((p + 1 : ℕ) : ℤ) + m = s + 0,
          ev γ.1 (p + 1) (s + 0) h' W (Sx.map (dbl.inl (opn U)) z') = 0 := by
        intro h'
        rw [← hcomp (p + 1) s h' W z']
        rfl
      rw [add_zero] at e
      exact e h
    · exact hinr (p + 1) s h W z'
  have big : ∀ (h : -((0 : ℕ) : ℤ) + m = m + 0),
      (∀ (W : Scheme) (t : W ⟶ X),
        ev γ.1 0 (m + 0) h W (Sx.map (dbl.inl (opn U)) (show Sx (opn U).right 0 W from t)) =
          Sec.res t (ev γ.1 0 (m + 0) h X (Sx.map (dbl.inl (opn U)) (show Sx (opn U).right 0 X from 𝟙 X)))) ∧
      Sec.res U.ι (ev γ.1 0 (m + 0) h X (Sx.map (dbl.inl (opn U)) (show Sx (opn U).right 0 X from 𝟙 X))) = 0 := by
    intro h
    have nat : ∀ (W : Scheme) (t : W ⟶ X),
        ev γ.1 0 (m + 0) h W (Sx.map (dbl.inl (opn U)) (show Sx (opn U).right 0 W from t)) =
          Sec.res t (ev γ.1 0 (m + 0) h X (Sx.map (dbl.inl (opn U)) (show Sx (opn U).right 0 X from 𝟙 X))) := by
      intro W t
      have e1 := hcomp 0 m h W t
      have e2 := hcomp 0 m h X (show Sx (opn U).right 0 X from 𝟙 X)
      have e := (cut _ x 0 m).2.1 W X t (show Sx (opn U).right 0 X from 𝟙 X)
      have r : Sx.res t (show Sx (opn U).right 0 X from 𝟙 X) = (show Sx (opn U).right 0 W from t) :=
        Category.comp_id t
      exact e1.symm.trans ((congrArg (fun z => (cut _ x 0 m).1 W z) r.symm).trans
        (e.symm.trans (congrArg (Sec.res t) e2)))
    refine ⟨nat, ?_⟩
    rw [← nat]
    have mem : (Sub.img (opn U).hom).mem 0 U U.ι := by
      refine ⟨(show Sx (sch.obj (U : Scheme.{0})) 0 U from 𝟙 (U : Scheme.{0})), ?_⟩
      dsimp [Sx.map, opn, sch, disc]
      simp
    exact (hcomp 0 m h U U.ι).symm.trans ((cut _ x 0 m).2.2 U U.ι mem)
  rw [add_zero] at big
  have dz : ∀ (h : -((0 : ℕ) : ℤ) + m = m + 1 - 1 + 0),
      Sec.map ((res (ZMod q) (tw q j)).d (m + 1 - 1 + 0) (m + 1 + 0))
        (ev γ.1 0 (m + 1 - 1 + 0) h X (Sx.map (dbl.inl (opn U)) (show Sx (opn U).right 0 X from 𝟙 X))) = 0 := by
    intro h
    have e2 := hcomp 0 (m + 1 - 1) h X (show Sx (opn U).right 0 X from 𝟙 X)
    have e := congrArg (fun a => a.1 X (show Sx (opn U).right 0 X from 𝟙 X)) (congrFun (congrFun hcD 0) (m + 1))
    refine (congrArg (Sec.map ((res (ZMod q) (tw q j)).d (m + 1 - 1 + 0) (m + 1 + 0))) e2).symm.trans ?_
    exact e
  rw [add_zero, add_zero, add_sub_cancel_right] at dz
  exact ⟨ev γ.1 0 m (by simp) X (Sx.map (dbl.inl (opn U)) (show Sx (opn U).right 0 X from 𝟙 X)),
    dz _, (big _).2, γ, hγ, fun W t => (big _).1 W t, fun W t => hinr 0 m _ W t, hhi⟩

end
end
