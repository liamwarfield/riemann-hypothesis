module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HtBijOfParts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SglMem
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.ZarAbs
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsDetEquivOfSubsingleton
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.EtaleChartBaseChange.DivisorCoverOfChartLaws
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.EtaleChartBaseChange.ChartLaws
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NullClassVanishing.CupLaws
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.EtaleChartBaseChange.RelInjOf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NullClassVanishing.ClsZeroOfNull
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.OntoLow
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.Retract
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineFormsOfFormUniqueness
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedLogCocycleD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelNullCast
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleMapRight
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.OmNatB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsLocalizationAway
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.OntoOf3Pf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SlantOf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.HodgeTateDimensionEquality
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.FormUniq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTheta
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechDApply

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.Faithful
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto.EquivalenceOnIso

open Pb HT

variable {K : Type} [CommRing K] {W Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}

theorem obj_ext {C : Type 1} [Category.{0} C] {P : ObjectProperty C} (a b : P.FullSubcategory) (h : a.obj = b.obj) :
    a = b := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  subst h
  rfl

def preim [Mono i] {T₁ T₂ : Thick (smFun W (i ≫ q))}
    (g : (smS (p := q) i rfl).G.obj T₁ ⟶ (smS (p := q) i rfl).G.obj T₂) : T₁ ⟶ T₂ :=
  mkH (γ := dividedPowersBot K) (p := 0) (q := i ≫ q) (κ := Ideal.Quotient.mk ⊥) g.φ (fun r => g.comm r) g.dp g.hle (by
    have e := g.pt
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z : PtOver Z q (Ideal.Quotient.mk (⊥ : Ideal K)) (T₂.B ⧸ T₂.J) => z.1.1) e
    · apply (cancel_mono i).1
      exact (Category.assoc _ _ _).trans
        (congrArg (fun z : PtOver Z q (Ideal.Quotient.mk (⊥ : Ideal K)) (T₂.B ⧸ T₂.J) => z.1.2) e))

def lift (T : Thick (smFun Z q)) (w : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ W)
    (hw : w ≫ i = pt (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T) :
    Thick (smFun W (i ≫ q)) :=
  mkT (γ := dividedPowersBot K) (p := 0) (q := i ≫ q) (κ := Ideal.Quotient.mk ⊥) T.B T.i T.J T.δ T.adm T.compat
    ⟨((show PtOver Z q (Ideal.Quotient.mk (⊥ : Ideal K)) (T.B ⧸ T.J) from T.y).1.1, w),
      (Category.assoc w i q).symm.trans ((congrArg (· ≫ q) hw).trans
        (show PtOver Z q (Ideal.Quotient.mk (⊥ : Ideal K)) (T.B ⧸ T.J) from T.y).2)⟩
    T.w

theorem G_lift (T : Thick (smFun Z q)) (w : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ W)
    (hw : w ≫ i = pt (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T) :
    (smS (p := q) i rfl).G.obj (lift T w hw) = T := by
  have hs1 := s_eq_one (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T
  obtain ⟨B, i₀, J, δ, adm, compat, α, y, inα, w₀, x, v, s, hx, hs, hv⟩ := T
  change Thick.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _
  congr 1
  all_goals first
    | exact RingHom.comp_id _
    | (funext j; exact (j : Empty).elim)
    | (apply Subtype.ext; apply Prod.ext; rfl; exact hw)
    | (have h1 : s = 1 := hs1
       refine Eq.trans ?_ h1.symm
       show (1 : Bˣ) ^ 1 * (Units.map _ (1 : Kˣ))⁻¹ = 1
       simp)

theorem essSurj [Mono i] (U : ObjectProperty (Thick (smFun Z q))) (U' : ObjectProperty (Thick (smFun W (i ≫ q))))
    (h : ∀ T, U' T → (U ⊓ On q i) ((smS i rfl).G.obj T)) (hU : ∀ T, U ((smS i rfl).G.obj T) → U' T) (a : ℕ) :
    (morV i rfl a h).G.EssSurj where
  mem_essImage Y := by
    have hY : (U ⊓ On q i) Y.obj := Y.property
    obtain ⟨w, hw⟩ := hY.2
    have hY' : U' (lift Y.obj w hw) := hU _ (by rw [G_lift]; exact hY.1)
    exact ⟨⟨lift Y.obj w hw, hY'⟩, ⟨eqToIso (obj_ext _ _ (G_lift Y.obj w hw))⟩⟩

theorem full [Mono i] {U : ObjectProperty (Thick (smFun Z q))} {U' : ObjectProperty (Thick (smFun W (i ≫ q)))}
    (h : ∀ T, U' T → (U ⊓ On q i) ((smS i rfl).G.obj T)) (a : ℕ) : (morV i rfl a h).G.Full where
  map_surjective {X Y} g := ⟨ObjectProperty.homMk (preim (T₁ := X.obj) (T₂ := Y.obj) g.hom),
    ObjectProperty.hom_ext _ (hom_ext rfl)⟩

theorem faithful {U : ObjectProperty (Thick (smFun Z q))} {U' : ObjectProperty (Thick (smFun W (i ≫ q)))}
    (h : ∀ T, U' T → (U ⊓ On q i) ((smS i rfl).G.obj T)) (a : ℕ) : (morV i rfl a h).G.Faithful where
  map_injective {X Y} {f g} e := ObjectProperty.hom_ext _ (hom_ext (congrArg (fun k => k.hom.φ) e))

theorem tau_bij {U : ObjectProperty (Thick (smFun Z q))} {U' : ObjectProperty (Thick (smFun W (i ≫ q)))}
    (h : ∀ T, U' T → (U ⊓ On q i) ((smS i rfl).G.obj T)) (a : ℕ) (T : U'.FullSubcategory) :
    Function.Bijective ((morV i rfl a h).τ T) := by
  have hτ : ∀ x, ((morV i rfl a h).τ T x).1 = x.1 := by
    intro x
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  exact ⟨fun x y e => Subtype.ext ((hτ x).symm.trans ((congrArg Subtype.val e).trans (hτ y))),
    fun y => ⟨y, Subtype.ext (hτ y)⟩⟩

end CrystallineSemistableComparison.Onto.EquivalenceOnIso

namespace CrystallineSemistableComparison.Onto


open EquivalenceOnIso in
theorem onIso_pf : OnIso := by
  intro K _ W Z q i _ U U' h hU a n
  have := faithful h a
  have := full h a
  have := essSurj U U' h hU a
  have : (morV i rfl a h).G.IsEquivalence := {}
  exact CrystallineSemistableComparison.P.adj_mor (morV i rfl a h) (tau_bij h a) n

end CrystallineSemistableComparison.Onto

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneResOfOneLow
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CrystallineSemistableComparison CrystallineSemistableComparison.Onto

universe w

namespace GlobalTheory.CompanionTheory.OneResProof

variable {R : Type} [CommRing R]

section Abstract

variable (D : DCx.{w} R)

def IsB (p : ℕ) : ∀ q, D.X p q → Prop
  | 0, y => y = 0
  | q + 1, y => ∃ u, D.dv p q u = y

def EZ (q : ℕ) : Prop := ∀ p (y : D.X (p + 1) q), D.dv (p + 1) q y = 0 → D.dh (p + 1) q y = 0 →
  ∃ x, D.dv p q x = 0 ∧ D.dh p q x = y

variable {D}

theorem eb (hrow : ∀ q p (u : D.X (p + 1) q), D.dh (p + 1) q u = 0 → ∃ t, D.dh p q t = u)
    {q : ℕ} (hZ : EZ D q) (p : ℕ) (u : D.X (p + 1) q) (hy : D.dh (p + 1) (q + 1) (D.dv (p + 1) q u) = 0) :
    ∃ t, D.dh p (q + 1) (D.dv p q t) = D.dv (p + 1) q u := by
  have h1 : D.dv (p + 2) q (D.dh (p + 1) q u) = 0 := by rw [← D.hv, hy]
  obtain ⟨w, hw, hw'⟩ := hZ (p + 1) (D.dh (p + 1) q u) h1 (D.hh _ _ _)
  obtain ⟨t, ht⟩ := hrow q p (u - w) (by rw [map_sub, hw', sub_self])
  exact ⟨t, by rw [D.hv, ht, map_sub, hw, sub_zero]⟩

theorem ez (hrow : ∀ q p (u : D.X (p + 1) q), D.dh (p + 1) q u = 0 → ∃ t, D.dh p q t = u) (a : ℕ)
    (hcol : ∀ p q, q ≠ a → ∀ y : D.X p q, D.dv p q y = 0 → IsB D p q y)
    (hA : ∀ p (y : D.X (p + 1) a), D.dv (p + 1) a y = 0 → D.dh (p + 1) a y = 0 →
      ∃ x, D.dv p a x = 0 ∧ IsB D (p + 1) a (y - D.dh p a x)) (q : ℕ) : EZ D q := by
  induction q with
  | zero =>
    intro p y hv hh
    by_cases h : 0 = a
    · subst h
      obtain ⟨x, hx, hb⟩ := hA p y hv hh
      exact ⟨x, hx, (sub_eq_zero.1 hb).symm⟩
    · exact ⟨0, map_zero _, by rw [map_zero]; exact (hcol _ 0 h y hv : y = 0).symm⟩
  | succ q ih =>
    intro p y hv hh
    by_cases h : q + 1 = a
    · subst h
      obtain ⟨x, hx, u, hu⟩ := hA p y hv hh
      obtain ⟨t, ht⟩ := eb hrow ih p u (by rw [hu, map_sub, hh, D.hh, sub_zero])
      exact ⟨x + D.dv p q t, by rw [map_add (f := _), hx, D.vv, add_zero], by rw [map_add (f := _), ht, hu]; abel⟩
    · obtain ⟨u, rfl⟩ : ∃ u, D.dv (p + 1) q u = y := hcol _ _ h y hv
      obtain ⟨t, ht⟩ := eb hrow ih p u hh
      exact ⟨D.dv p q t, D.vv _ _ _, ht⟩

end Abstract

variable {ι : Type} [DecidableEq ι]

theorem cech_nat {P Q : PM.{w} R ι} (φ : ∀ S, P.M S →ₗ[R] Q.M S)
    (nat : ∀ {S T : Finset ι} (h : S ⊆ T) x, φ T (P.res h x) = Q.res h (φ S x)) (p : ℕ) (x : P.cech.X p)
    (t : Fin (p + 2) → ι) : φ _ (P.cech.d p x t) = Q.cech.d p (fun i => φ _ (x i)) t := by
  rw [Cos.d_apply, Cos.d_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  exact nat _ _

abbrev dcx (A : Sy.{w} R ι) : DCx.{w} R where
  X p q := (A.term q).cech.X p
  dh p q := (A.term q).cech.d p
  dv p q := LinearMap.pi fun i => ((A.K (ent i)).d q).comp (LinearMap.proj i)
  hh p q := (A.term q).cech.dd p
  vv p q x := funext fun i => (A.K (ent i)).dd q (x i)
  hv p q x := funext fun t => (cech_nat (P := A.term q) (Q := A.term (q + 1)) (fun S => (A.K S).d q)
    (fun h x => (A.res h).comm _ x) p x t).symm

abbrev zpm (A : Sy.{w} R ι) (a : ℕ) : PM.{w} R ι where
  M S := (A.K S).Z a
  res h := (A.res h).mapZ a
  res_id S h x := Subtype.ext (A.res_id S h a x.1)
  res_comp h h' x := Subtype.ext (A.res_comp h h' a x.1)

theorem isB_of (A : Sy.{w} R ι) (p q : ℕ) (y : (dcx A).X p q) (h : ∀ i, y i ∈ (A.K (ent i)).B q) : IsB (dcx A) p q y := by
  cases q with
  | zero => exact funext fun i => h i
  | succ q =>
    choose u hu using h
    exact ⟨u, funext hu⟩

theorem ent_nonempty {n : ℕ} (i : Fin (n + 1) → ι) : (ent i).Nonempty :=
  ⟨i 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩

theorem hcol (A : Sy.{w} R ι) (a : ℕ) (hO : A.One a) (p q : ℕ) (hq : q ≠ a) (y : (dcx A).X p q)
    (hy : (dcx A).dv p q y = 0) : IsB (dcx A) p q y := by
  refine isB_of A p q y fun i => ?_
  have hs := hO (ent i) (ent_nonempty i) q hq
  have hi : (A.K (ent i)).d q (y i) = 0 := congrFun hy i
  have h0 : (Submodule.Quotient.mk ⟨y i, hi⟩ : (A.K (ent i)).H q) = 0 := Subsingleton.elim _ _
  have h2 : (⟨y i, hi⟩ : (A.K (ent i)).Z q) ∈ ((A.K (ent i)).B q).submoduleOf ((A.K (ent i)).Z q) :=
    (Submodule.Quotient.mk_eq_zero _).1 h0
  exact h2

theorem hrow (A : Sy.{w} R ι) (hD : A.Desc) (q p : ℕ) (u : (dcx A).X (p + 1) q) (hu : (dcx A).dh (p + 1) q u = 0) :
    ∃ t, (dcx A).dh p q t = u := by
  obtain ⟨t, ht⟩ := (hD q).2.2.2 p u hu
  exact ⟨t, ht.trans (one_smul _ _)⟩

theorem hA (A : Sy.{w} R ι) (a : ℕ)
    (hres : (A.coh a).cech.cx.ResUpTo 1 (LinearMap.ker ((A.coh a).cech.d 0)).subtype) (p : ℕ) (y : (dcx A).X (p + 1) a)
    (hv : (dcx A).dv (p + 1) a y = 0) (hh : (dcx A).dh (p + 1) a y = 0) :
    ∃ x, (dcx A).dv p a x = 0 ∧ IsB (dcx A) (p + 1) a (y - (dcx A).dh p a x) := by
  have natI : ∀ (p : ℕ) (z : (zpm A a).cech.X p) (t : Fin (p + 2) → ι),
      ((zpm A a).cech.d p z t).1 = (dcx A).dh p a (fun i => (z i).1) t := fun p z t =>
    cech_nat (P := zpm A a) (Q := A.term a) (fun S => ((A.K S).Z a).subtype) (fun h x => rfl) p z t
  have natQ : ∀ (p : ℕ) (z : (zpm A a).cech.X p) (t : Fin (p + 2) → ι),
      Submodule.Quotient.mk ((zpm A a).cech.d p z t) =
        (A.coh a).cech.d p (fun i => Submodule.Quotient.mk (z i)) t := fun p z t =>
    cech_nat (P := zpm A a) (Q := A.coh a) (fun S => Submodule.mkQ _) (fun h x => rfl) p z t
  let y' : (zpm A a).cech.X (p + 1) := fun i => ⟨y i, congrFun hv i⟩
  have h0 : (zpm A a).cech.d (p + 1) y' = 0 := funext fun t => Subtype.ext ((natI (p + 1) y' t).trans (congrFun hh t))
  obtain ⟨c, hc⟩ := hres.2.2.2 p (fun i => Submodule.Quotient.mk (y' i)) (funext fun t => by
    have := natQ (p + 1) y' t
    rw [h0] at this
    exact this.symm)
  have hlift : ∀ i, ∃ z : (A.K (ent i)).Z a, Submodule.Quotient.mk z = c i := fun i =>
    Submodule.Quotient.mk_surjective _ (c i)
  choose z hz using hlift
  refine ⟨fun i => (z i).1, funext fun i => (z i).2, isB_of A _ _ _ fun t => ?_⟩
  have h1 : (Submodule.Quotient.mk (y' t - (zpm A a).cech.d p z t) : (A.K (ent t)).H a) = 0 := by
    rw [Submodule.Quotient.mk_sub, natQ, sub_eq_zero]
    have e : (fun i => Submodule.Quotient.mk (z i)) = c := funext hz
    rw [e]
    exact (congrFun (hc.trans (one_smul R _)) t).symm
  have h2 := (Submodule.Quotient.mk_eq_zero _).1 h1
  have e : (y - (dcx A).dh p a fun i => (z i).1) t = (y' t - (zpm A a).cech.d p z t).1 := by
    rw [Submodule.coe_sub, natI]
    rfl
  rw [e]
  exact h2

theorem high (A : Sy.{w} R ι) (a : ℕ) (hD : A.Desc) (hO : A.One a) (hZ : ∀ q, EZ (dcx A) q) (q : ℕ) (hq : q + 1 ≠ a) :
    Subsingleton ((A.K ∅).H (q + 1)) := by
  have hall : ∀ h : (A.K ∅).H (q + 1), h = 0 := by
    intro h
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ h
    rw [Submodule.Quotient.mk_eq_zero]
    change x ∈ (A.K ∅).B (q + 1)
    have hx' : (A.K ∅).d (q + 1) x = 0 := hx
    have hev : (dcx A).dv 0 (q + 1) ((A.term (q + 1)).aug x) = 0 := funext fun i => by
      change (A.K (ent i)).d (q + 1) ((A.res _).f (q + 1) x) = 0
      rw [(A.res _).comm, hx', map_zero]
    obtain ⟨u, hu⟩ : ∃ u, (dcx A).dv 0 q u = (A.term (q + 1)).aug x := hcol A a hO 0 (q + 1) hq _ hev
    have hdh : (dcx A).dh 0 (q + 1) ((A.term (q + 1)).aug x) = 0 := (hD (q + 1)).1 x
    obtain ⟨v, hv, hv'⟩ := hZ q 0 ((dcx A).dh 0 q u) (by rw [← (dcx A).hv, hu, hdh]) ((dcx A).hh _ _ _)
    obtain ⟨s, hs⟩ := (hD q).2.2.1 (u - v) (by
      have : (dcx A).dh 0 q (u - v) = 0 := by rw [map_sub, hv', sub_self]
      exact this)
    rw [one_smul] at hs
    have h1 : (A.term (q + 1)).aug ((A.K ∅).d q s) = (A.term (q + 1)).aug x := by
      have e : (dcx A).dv 0 q ((A.term q).aug s) = (A.term (q + 1)).aug ((A.K ∅).d q s) :=
        funext fun i => (A.res _).comm q s
      rw [← e, hs, map_sub, hv, sub_zero, hu]
    have h2 := (hD (q + 1)).2.1 ((A.K ∅).d q s - x) (by rw [map_sub, h1, sub_self])
    rw [one_smul, sub_eq_zero] at h2
    exact ⟨s, h2⟩
  exact ⟨fun h₁ h₂ => by rw [hall h₁, hall h₂]⟩

theorem oneRes_of_oneLow : OneLow → OneRes := by
  intro hL R _ ι _ A a hD hO hres
  obtain ⟨hlow, hinj, hex⟩ := hL R ι A a hD hO
  have hZ : ∀ q, EZ (dcx A) q := ez (hrow A hD) a (hcol A a hO) (hA A a hres)
  refine ⟨fun j hj => ?_, ?_⟩
  · rcases lt_or_gt_of_ne hj with h | h
    · exact hlow j h
    · obtain ⟨q, rfl⟩ : ∃ q, j = q + 1 := ⟨j - 1, by omega⟩
      exact high A a hD hO hZ q hj
  · unfold PM.Ex Cx.ResUpTo
    refine ⟨fun x => (hex _).2 ⟨x, rfl⟩, fun x hx => ?_, fun y hy => ?_, hres.2.2.2⟩
    · rw [one_smul]
      exact hinj (hx.trans (map_zero _).symm)
    · obtain ⟨x, rfl⟩ := (hex y).1 hy
      exact ⟨x, (one_smul _ _).symm⟩

end GlobalTheory.CompanionTheory.OneResProof

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PiCongrRightSingle
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBaseChangeEquiv
open TensorProduct

namespace GlobalTheory.CompanionTheory.ExteriorBase

theorem exists_baseChange_equiv (A R M : Type) [CommRing A] [CommRing R] [Algebra A R]
    [AddCommGroup M] [Module A M] (a : ℕ) :
    ∃ e : R ⊗[A] (⋀[A]^a M) ≃ₗ[R] ⋀[R]^a (R ⊗[A] M), ∀ (r : R) (m : Fin a → M),
      e (r ⊗ₜ exteriorPower.ιMulti A a m) =
        r • exteriorPower.ιMulti R a (fun k => (1 : R) ⊗ₜ[A] m k) := by
  have h := GlobalTheory.TopForm.isBaseChange_exteriorPower (TensorProduct.isBaseChange A M R) a
  refine ⟨h.equiv, fun r m => ?_⟩
  rw [h.equiv_tmul, GlobalTheory.exteriorPowerMapOver_ιMulti]
  rfl

end GlobalTheory.CompanionTheory.ExteriorBase
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExteriorPowerSplit
open TensorProduct Module Function

namespace GlobalTheory.CompanionTheory.TopExtSplit

open GlobalTheory.TopExt

variable {R F H L : Type*} [CommRing R] [AddCommGroup F] [Module R F] [AddCommGroup H] [Module R H]
  [AddCommGroup L] [Module R L]


variable (R F) in
noncomputable def gradeProj (n : ℕ) : ExteriorAlgebra R F →ₗ[R] ⋀[R]^n F :=
  DirectSum.component R ℕ (fun k => ⋀[R]^k F) n ∘ₗ
    (DirectSum.decomposeLinearEquiv (fun k : ℕ => ⋀[R]^k F)).toLinearMap

theorem gradeProj_same {n : ℕ} (x : ⋀[R]^n F) :
    gradeProj R F n (x : ExteriorAlgebra R F) = x := by
  change (DirectSum.decompose (fun k : ℕ => ⋀[R]^k F) (x : ExteriorAlgebra R F)) n = x
  rw [DirectSum.decompose_coe, DirectSum.of_eq_same]

theorem gradeProj_ne {m n : ℕ} (h : m ≠ n) (x : ⋀[R]^m F) :
    gradeProj R F n (x : ExteriorAlgebra R F) = 0 := by
  change (DirectSum.decompose (fun k : ℕ => ⋀[R]^k F) (x : ExteriorAlgebra R F)) n = 0
  exact Subtype.ext (DirectSum.decompose_of_mem_ne _ x.2 h)

theorem exists_bigradedProj {i : F →ₗ[R] H} {s : L →ₗ[R] H} {r : H →ₗ[R] F} {π : H →ₗ[R] L}
    (hri : ∀ x, r (i x) = x) (hrs : ∀ y, r (s y) = 0) (hπi : ∀ x, π (i x) = 0)
    (hπs : ∀ y, π (s y) = y) :
    ∃ Ψ : ∀ a b : ℕ, ExteriorAlgebra R H →ₗ[R] (⋀[R]^a F) ⊗[R] (⋀[R]^b L),
      ∀ (a b a' b' : ℕ) (x : ⋀[R]^a' F) (y : ⋀[R]^b' L),
        Ψ a b (wedgeMap i s a' b' (x ⊗ₜ y) : ExteriorAlgebra R H) =
          gradeProj R F a (x : ExteriorAlgebra R F) ⊗ₜ
            gradeProj R L b (y : ExteriorAlgebra R L) := by
  let e : (0 : QuadraticForm R H) →qᵢ
      (QuadraticMap.prod (0 : QuadraticForm R F) (0 : QuadraticForm R L)) :=
    { r.prod π with map_app' := fun x => by simp }
  have he : ∀ x, e x = (r x, π x) := fun _ => rfl
  let Φ := (CliffordAlgebra.ofProd (0 : QuadraticForm R F) (0 : QuadraticForm R L)).comp
    (CliffordAlgebra.map e)
  have h₁ : Φ.comp (ExteriorAlgebra.map i) = GradedTensorProduct.includeLeft _ _ := by
    ext x
    simp [Φ, he, hri, hπi]
  have h₂ : Φ.comp (ExteriorAlgebra.map s) = GradedTensorProduct.includeRight _ _ := by
    ext x
    simp [Φ, he, hrs, hπs]
  refine ⟨fun a b => TensorProduct.map (gradeProj R F a) (gradeProj R L b) ∘ₗ
    (GradedTensorProduct.of R (CliffordAlgebra.evenOdd (0 : QuadraticForm R F))
      (CliffordAlgebra.evenOdd (0 : QuadraticForm R L))).symm.toLinearMap ∘ₗ Φ.toLinearMap, ?_⟩
  intro a b a' b' x y
  have hx := AlgHom.congr_fun h₁ x
  have hy := AlgHom.congr_fun h₂ y
  rw [AlgHom.comp_apply] at hx hy
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply,
    coe_wedgeMap_tmul, map_mul, hx, hy, GradedTensorProduct.includeLeft_apply,
    GradedTensorProduct.includeRight_apply, GradedTensorProduct.tmul_one_mul_one_tmul]
  change TensorProduct.map (gradeProj R F a) (gradeProj R L b)
    ((x : ExteriorAlgebra R F) ⊗ₜ (y : ExteriorAlgebra R L)) = _
  rw [TensorProduct.map_tmul]

noncomputable def wedgePiece (i : F →ₗ[R] H) (s : L →ₗ[R] H) (c : ℕ) (a : Fin (c + 1)) :
    (⋀[R]^(a : ℕ) F) ⊗[R] (⋀[R]^(c - a) L) →ₗ[R] ⋀[R]^c H :=
  (LinearEquiv.ofEq _ _ (by rw [Nat.add_sub_cancel' (Nat.lt_succ_iff.1 a.2)])).toLinearMap ∘ₗ
    wedgeMap i s a (c - a)

theorem coe_wedgePiece (i : F →ₗ[R] H) (s : L →ₗ[R] H) (c : ℕ) (a : Fin (c + 1))
    (t : (⋀[R]^(a : ℕ) F) ⊗[R] (⋀[R]^(c - a) L)) :
    (wedgePiece i s c a t : ExteriorAlgebra R H) = wedgeMap i s a (c - a) t := rfl

noncomputable def wedgeSum (i : F →ₗ[R] H) (s : L →ₗ[R] H) (c : ℕ) :
    (∀ a : Fin (c + 1), (⋀[R]^(a : ℕ) F) ⊗[R] (⋀[R]^(c - a) L)) →ₗ[R] ⋀[R]^c H :=
  LinearMap.lsum R _ ℕ (wedgePiece i s c)

theorem coe_wedgeSum (i : F →ₗ[R] H) (s : L →ₗ[R] H) (c : ℕ)
    (t : ∀ a : Fin (c + 1), (⋀[R]^(a : ℕ) F) ⊗[R] (⋀[R]^(c - a) L)) :
    (wedgeSum i s c t : ExteriorAlgebra R H) =
      ∑ a : Fin (c + 1), (wedgeMap i s a (c - a) (t a) : ExteriorAlgebra R H) := by
  simp [wedgeSum, LinearMap.lsum_apply, coe_wedgePiece]

theorem wedgeSum_single (i : F →ₗ[R] H) (s : L →ₗ[R] H) (c : ℕ) (a : Fin (c + 1))
    (t : (⋀[R]^(a : ℕ) F) ⊗[R] (⋀[R]^(c - a) L)) :
    wedgeSum i s c (Pi.single a t) = wedgePiece i s c a t := by
  rw [wedgeSum, LinearMap.lsum_apply, LinearMap.sum_apply, Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

theorem wedgeSum_injective {i : F →ₗ[R] H} {s : L →ₗ[R] H} {r : H →ₗ[R] F} {π : H →ₗ[R] L}
    (hri : ∀ x, r (i x) = x) (hrs : ∀ y, r (s y) = 0) (hπi : ∀ x, π (i x) = 0)
    (hπs : ∀ y, π (s y) = y) (c : ℕ) : Injective (wedgeSum i s c) := by
  obtain ⟨Ψ, hΨ⟩ := exists_bigradedProj hri hrs hπi hπs
  have key : ∀ (a b a' b' : ℕ) (t : (⋀[R]^a F) ⊗[R] (⋀[R]^b L)),
      Ψ a' b' (wedgeMap i s a b t : ExteriorAlgebra R H) =
        TensorProduct.map (gradeProj R F a' ∘ₗ (⋀[R]^a F).subtype)
          (gradeProj R L b' ∘ₗ (⋀[R]^b L).subtype) t := by
    intro a b a' b' t
    induction t using TensorProduct.inductionOn with
    | add x y hx hy =>
      simp only [map_add (f := _), Submodule.coe_add] at hx hy ⊢
      rw [hx, hy]
    | tmul x y =>
      rw [hΨ, TensorProduct.map_tmul]
      rfl
  have hl : ∀ t (a' : Fin (c + 1)),
      Ψ a' (c - a') (wedgeSum i s c t : ExteriorAlgebra R H) = t a' := by
    intro t a'
    set_option synthInstance.maxHeartbeats 100000 in
      rw [coe_wedgeSum, map_sum, Finset.sum_eq_single a']
    · rw [key]
      have h₁ : gradeProj R F a' ∘ₗ (⋀[R]^(a' : ℕ) F).subtype = LinearMap.id :=
        LinearMap.ext gradeProj_same
      have h₂ : gradeProj R L (c - a') ∘ₗ (⋀[R]^(c - a') L).subtype = LinearMap.id :=
        LinearMap.ext gradeProj_same
      rw [h₁, h₂, TensorProduct.map_id, LinearMap.id_apply]
    · intro a _ hne
      rw [key]
      have h₁ : gradeProj R F a' ∘ₗ (⋀[R]^(a : ℕ) F).subtype = 0 :=
        LinearMap.ext (gradeProj_ne (Fin.val_ne_of_ne hne))
      rw [h₁, TensorProduct.map_zero_left, LinearMap.zero_apply]
    · simp
  intro t t' h
  funext a'
  rw [← hl t a', ← hl t' a', h]

theorem wedgeSum_surjective {i : F →ₗ[R] H} {s : L →ₗ[R] H}
    (hsup : LinearMap.range i ⊔ LinearMap.range s = ⊤) (c : ℕ) :
    Surjective (wedgeSum i s c) := by
  set A := LinearMap.range (ExteriorAlgebra.ι R ∘ₗ i) with hA
  set B := LinearMap.range (ExteriorAlgebra.ι R ∘ₗ s) with hB
  have hAB : LinearMap.range (ExteriorAlgebra.ι R : H →ₗ[R] _) = A + B := by
    rw [hA, hB, LinearMap.range_comp, LinearMap.range_comp, Submodule.add_eq_sup,
      ← Submodule.map_sup, hsup, Submodule.map_top]
  have key : ∀ C D : Submodule R (ExteriorAlgebra R H),
      C ≤ LinearMap.range (ExteriorAlgebra.ι R : H →ₗ[R] _) →
      D ≤ LinearMap.range (ExteriorAlgebra.ι R : H →ₗ[R] _) → C * D ≤ D * C := by
    intro C D hC hD
    refine Submodule.mul_le.2 fun x hx y hy => ?_
    obtain ⟨u, rfl⟩ := hC hx
    obtain ⟨v, rfl⟩ := hD hy
    rw [eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap u v)]
    exact Submodule.neg_mem _ (Submodule.mul_mem_mul hy hx)
  have hA' : A ≤ LinearMap.range (ExteriorAlgebra.ι R : H →ₗ[R] _) := hAB ▸ le_sup_left
  have hB' : B ≤ LinearMap.range (ExteriorAlgebra.ι R : H →ₗ[R] _) := hAB ▸ le_sup_right
  have hc : Commute A B := le_antisymm (key _ _ hA' hB') (key _ _ hB' hA')
  obtain ⟨S, hS⟩ : ∃ S, S = (LinearMap.range (wedgeSum i s c)).map (⋀[R]^c H).subtype := ⟨_, rfl⟩
  have hpiece : ∀ k l, k + l = c → A ^ k * B ^ l ≤ S := by
    intro k l hkl
    obtain rfl : l = c - k := by omega
    have hk : k < c + 1 := by omega
    refine Submodule.mul_le.2 fun x hx y hy => ?_
    rw [range_pow_eq_map] at hx hy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    rw [hS]
    refine ⟨wedgeSum i s c (Pi.single (⟨k, hk⟩ : Fin (c + 1))
      ((⟨x, hx⟩ : ⋀[R]^k F) ⊗ₜ (⟨y, hy⟩ : ⋀[R]^(c - k) L))), ⟨_, rfl⟩, ?_⟩
    rw [wedgeSum_single, Submodule.subtype_apply, coe_wedgePiece]
    exact coe_wedgeMap_tmul _ _ _ _
  have hle : (⋀[R]^c H) ≤ S := by
    rw [ExteriorAlgebra.exteriorPower, hAB, hc.add_pow']
    refine Finset.sum_induction _ (· ≤ S) (fun x y hx hy => sup_le hx hy) bot_le ?_
    rintro ⟨k, l⟩ hkl
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
    have := hpiece k l hkl
    generalize c.choose (k, l).1 = n
    induction n with
    | zero => rw [zero_nsmul]; exact bot_le
    | succ n ih => rw [succ_nsmul]; exact sup_le ih this
  intro z
  have hz := hle z.2
  rw [hS] at hz
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := hz
  exact ⟨t, Subtype.ext ht⟩

theorem ιMulti_cast {m n : ℕ} (h : n = m) (v : Fin m → H) :
    ExteriorAlgebra.ιMulti R m v = ExteriorAlgebra.ιMulti R n (v ∘ Fin.cast h) := by
  subst h
  rfl

theorem exteriorPower_split :
    ∀ (R F L H : Type) [CommRing R] [AddCommGroup F] [Module R F] [AddCommGroup L] [Module R L]
      [AddCommGroup H] [Module R H] (i : F →ₗ[R] H) (s : L →ₗ[R] H) (r : H →ₗ[R] F)
      (π : H →ₗ[R] L) (hri : ∀ x, r (i x) = x) (hrs : ∀ y, r (s y) = 0)
      (hπi : ∀ x, π (i x) = 0) (hπs : ∀ y, π (s y) = y)
      (hsup : LinearMap.range i ⊔ LinearMap.range s = ⊤) (c : ℕ),
      ∃ e : (∀ a : Fin (c + 1), (⋀[R]^(a : ℕ) F) ⊗[R] (⋀[R]^(c - a) L)) ≃ₗ[R] ⋀[R]^c H,
        ∀ (a : Fin (c + 1)) (f : Fin a → F) (h : Fin (c - a) → L),
          e (Pi.single a (exteriorPower.ιMulti R a f ⊗ₜ exteriorPower.ιMulti R (c - a) h)) =
            exteriorPower.ιMulti R c
              (Fin.append (fun k => i (f k)) (fun k => s (h k)) ∘
                Fin.cast (by have := a.2; omega)) := by
  intro R F L H _ _ _ _ _ _ _ i s r π hri hrs hπi hπs hsup c
  refine ⟨LinearEquiv.ofBijective (wedgeSum i s c)
    ⟨wedgeSum_injective hri hrs hπi hπs c, wedgeSum_surjective hsup c⟩, fun a f h =>
      Subtype.ext ?_⟩
  change (wedgeSum i s c _ : ExteriorAlgebra R H) = _
  rw [wedgeSum_single, coe_wedgePiece, coe_wedgeMap_tmul]
  simp only [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.map_apply_ιMulti,
    ExteriorAlgebra.ιMulti_mul_ιMulti]
  exact ιMulti_cast _ _

end GlobalTheory.CompanionTheory.TopExtSplit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KaehlerPushoutSplit
open TensorProduct

namespace GlobalTheory.CompanionTheory.KaehlerPushout

open KaehlerDifferential

theorem exists_retraction (K A B R : Type) [CommRing K] [CommRing A] [CommRing B] [CommRing R]
    [Algebra K A] [Algebra K B] [Algebra K R] [Algebra A R] [Algebra B R]
    [IsScalarTower K A R] [IsScalarTower K B R] [Algebra.IsPushout K B A R] :
    ∃ r : Ω[R⁄K] →ₗ[R] R ⊗[A] Ω[A⁄K],
      (∀ x, r (KaehlerDifferential.mapBaseChange K A R x) = x) ∧
      (∀ y, r (KaehlerDifferential.mapBaseChange K B R y) = 0) := by
  let e := KaehlerDifferential.tensorKaehlerEquiv K B A R
  refine ⟨e.symm.toLinearMap ∘ₗ KaehlerDifferential.map K B R R, ?_, ?_⟩
  · intro x
    have key : KaehlerDifferential.map K B R R (KaehlerDifferential.mapBaseChange K A R x) = e x := by
      induction x with
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul s w =>
        have hw : w ∈ Submodule.span A (Set.range (KaehlerDifferential.D K A)) := by
          rw [KaehlerDifferential.span_range_derivation]; trivial
        induction hw using Submodule.span_induction generalizing s with
        | mem w hw =>
          obtain ⟨a, rfl⟩ := hw
          simp [e, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
        | zero => simp
        | add u v _ _ hu hv => simp only [tmul_add, map_add (f := _), hu, hv]
        | smul a u _ hu =>
          rw [← TensorProduct.smul_tmul]
          exact hu _
    simp [key]
  · intro y
    induction y with
    | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
    | tmul s w =>
      have hw : w ∈ Submodule.span B (Set.range (KaehlerDifferential.D K B)) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hw using Submodule.span_induction generalizing s with
      | mem w hw =>
        obtain ⟨b, rfl⟩ := hw
        simp [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
      | zero => simp
      | add u v _ _ hu hv => simp only [tmul_add, map_add (f := _), hu, hv, add_zero]
      | smul b u _ hu =>
        rw [← TensorProduct.smul_tmul]
        exact hu _

theorem range_sup_range (K A B R : Type) [CommRing K] [CommRing A] [CommRing B] [CommRing R]
    [Algebra K A] [Algebra K B] [Algebra K R] [Algebra A R] [Algebra B R]
    [IsScalarTower K A R] [IsScalarTower K B R] [h : Algebra.IsPushout K A B R] :
    LinearMap.range (KaehlerDifferential.mapBaseChange K A R) ⊔
      LinearMap.range (KaehlerDifferential.mapBaseChange K B R) = ⊤ := by
  set S := LinearMap.range (KaehlerDifferential.mapBaseChange K A R) ⊔
      LinearMap.range (KaehlerDifferential.mapBaseChange K B R) with hS
  have hA : ∀ a : A, KaehlerDifferential.D K R (algebraMap A R a) ∈ S := fun a =>
    Submodule.mem_sup_left ⟨1 ⊗ₜ KaehlerDifferential.D K A a, by
      simp [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]⟩
  have hB : ∀ b : B, KaehlerDifferential.D K R (algebraMap B R b) ∈ S := fun b =>
    Submodule.mem_sup_right ⟨1 ⊗ₜ KaehlerDifferential.D K B b, by
      simp [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]⟩
  have hD : ∀ r : R, KaehlerDifferential.D K R r ∈ S := by
    intro r
    induction r using h.out.inductionOn with
    | tmul b => exact hB b
    | smul a y hy =>
      rw [Algebra.smul_def, Derivation.leibniz]
      exact S.add_mem (S.smul_mem _ hy) (S.smul_mem _ (hA a))
    | add x y hx hy => rw [map_add (f := _)]; exact S.add_mem hx hy
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨r, rfl⟩
  exact hD r

theorem kaehler_pushout_split : ∀ (K A B R : Type) [CommRing K] [CommRing A] [CommRing B] [CommRing R] [Algebra K A] [Algebra K B] [Algebra K R] [Algebra A R] [Algebra B R] [IsScalarTower K A R] [IsScalarTower K B R] [Algebra.IsPushout K A B R], ∃ (r : Ω[R⁄K] →ₗ[R] R ⊗[A] Ω[A⁄K]) (π : Ω[R⁄K] →ₗ[R] R ⊗[B] Ω[B⁄K]), (∀ x, r (KaehlerDifferential.mapBaseChange K A R x) = x) ∧ (∀ y, r (KaehlerDifferential.mapBaseChange K B R y) = 0) ∧ (∀ x, π (KaehlerDifferential.mapBaseChange K A R x) = 0) ∧ (∀ y, π (KaehlerDifferential.mapBaseChange K B R y) = y) ∧ LinearMap.range (KaehlerDifferential.mapBaseChange K A R) ⊔ LinearMap.range (KaehlerDifferential.mapBaseChange K B R) = ⊤ := by
  intro K A B R _ _ _ _ _ _ _ _ _ _ _ h
  haveI hs : Algebra.IsPushout K B A R := h.symm
  obtain ⟨r, hr₁, hr₂⟩ := exists_retraction K A B R
  obtain ⟨π, hπ₁, hπ₂⟩ := exists_retraction K B A R
  exact ⟨r, π, hr₁, hr₂, hπ₂, hπ₁, range_sup_range K A B R⟩

end GlobalTheory.CompanionTheory.KaehlerPushout
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEquivBaseChangeTensor
open TensorProduct

namespace GlobalTheory.CompanionTheory.TensorPushout

theorem tensor_equiv_baseChange_tensor :
    ∀ (K A B R X Y : Type) [CommRing K] [CommRing A] [CommRing B] [CommRing R] [Algebra K A]
      [Algebra K B] [Algebra K R] [Algebra A R] [Algebra B R] [IsScalarTower K A R]
      [IsScalarTower K B R] [Algebra.IsPushout K A B R] [AddCommGroup X] [Module K X] [Module A X]
      [IsScalarTower K A X] [AddCommGroup Y] [Module K Y] [Module B Y] [IsScalarTower K B Y],
      ∃ t : X ⊗[K] Y ≃ₗ[K] (R ⊗[A] X) ⊗[R] (R ⊗[B] Y),
        ∀ x y, t (x ⊗ₜ y) = ((1 : R) ⊗ₜ[A] x) ⊗ₜ[R] ((1 : R) ⊗ₜ[B] y) := by
  intro K A B R X Y
  intros
  refine ⟨((TensorProduct.AlgebraTensorModule.cancelBaseChange K A A X Y).symm.restrictScalars K).trans <|
    (((Algebra.IsPushout.cancelBaseChange K A B R Y).symm.lTensor X).restrictScalars K).trans <|
    ((TensorProduct.comm A X (R ⊗[B] Y)).restrictScalars K).trans <|
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange A R R (R ⊗[B] Y) X).symm.restrictScalars K).trans <|
    ((TensorProduct.comm R (R ⊗[B] Y) (R ⊗[A] X)).restrictScalars K), fun x y => ?_⟩
  simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearEquiv.lTensor_tmul,
    Algebra.IsPushout.cancelBaseChange_symm_tmul, map_one, TensorProduct.comm_tmul]

end GlobalTheory.CompanionTheory.TensorPushout
end

open TensorProduct CrystallineSemistableComparison.Onto

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.OmKun

theorem piCongrRight_single {K ι : Type} [CommRing K] [DecidableEq ι] {X Y : ι → Type}
    [∀ i, AddCommGroup (X i)] [∀ i, Module K (X i)] [∀ i, AddCommGroup (Y i)] [∀ i, Module K (Y i)]
    (f : ∀ i, X i ≃ₗ[K] Y i) (a : ι) (x : X a) :
    LinearEquiv.piCongrRight f (Pi.single a x) = Pi.single a (f a x) := by
  funext b
  by_cases h : b = a
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem omKun_pushout (K A B R : Type) [CommRing K] [CommRing A] [CommRing B] [CommRing R]
    [Algebra K A] [Algebra K B] [Algebra K R] [Algebra A R] [Algebra B R]
    [IsScalarTower K A R] [IsScalarTower K B R] [Algebra.IsPushout K A B R] (c : ℕ) :
    ∃ e : (∀ a : Fin (c + 1), TensorProduct K (Om K A a) (Om K B (c - a))) ≃ₗ[K] Om K R c,
      ∀ (a : Fin (c + 1)) (g₀ : A) (g : Fin a → A) (h₀ : B) (h : Fin (c - a) → B),
        e (Pi.single a (form K g₀ g ⊗ₜ form K h₀ h)) = form K (algebraMap A R g₀ * algebraMap B R h₀)
          (Fin.append (fun k => algebraMap A R (g k)) (fun k => algebraMap B R (h k)) ∘
            Fin.cast (by have := a.2; omega)) := by
  obtain ⟨r, π, h1, h2, h3, h4, h5⟩ := GlobalTheory.CompanionTheory.KaehlerPushout.kaehler_pushout_split K A B R
  obtain ⟨E, hE⟩ := GlobalTheory.CompanionTheory.TopExtSplit.exteriorPower_split R _ _ _ _ _ r π h1 h2 h3 h4 h5 c
  choose bA hbA using fun a : ℕ => GlobalTheory.CompanionTheory.ExteriorBase.exists_baseChange_equiv A R (Ω[A⁄K]) a
  choose bB hbB using fun a : ℕ => GlobalTheory.CompanionTheory.ExteriorBase.exists_baseChange_equiv B R (Ω[B⁄K]) a
  choose t ht using fun a : Fin (c + 1) => GlobalTheory.CompanionTheory.TensorPushout.tensor_equiv_baseChange_tensor K A B R (Om K A a) (Om K B (c - a))
  refine ⟨LinearEquiv.piCongrRight (fun a => t a ≪≫ₗ
    (TensorProduct.congr (bA a) (bB (c - a))).restrictScalars K) ≪≫ₗ E.restrictScalars K, ?_⟩
  intro a g₀ g h₀ h
  have hA : bA a ((1 : R) ⊗ₜ[A] form K g₀ g) = algebraMap A R g₀ •
      exteriorPower.ιMulti R a (fun k => (1 : R) ⊗ₜ[A] KaehlerDifferential.D K A (g k)) := by
    unfold form
    rw [← TensorProduct.smul_tmul, hbA, Algebra.smul_def, mul_one]
  have hB : bB (c - a) ((1 : R) ⊗ₜ[B] form K h₀ h) = algebraMap B R h₀ •
      exteriorPower.ιMulti R (c - a) (fun k => (1 : R) ⊗ₜ[B] KaehlerDifferential.D K B (h k)) := by
    unfold form
    rw [← TensorProduct.smul_tmul, hbB, Algebra.smul_def, mul_one]
  have hmain : (TensorProduct.congr (bA a) (bB (c - a))) (((1 : R) ⊗ₜ[A] form K g₀ g) ⊗ₜ[R]
      ((1 : R) ⊗ₜ[B] form K h₀ h)) = (algebraMap A R g₀ * algebraMap B R h₀) •
        (exteriorPower.ιMulti R a (fun k => (1 : R) ⊗ₜ[A] KaehlerDifferential.D K A (g k)) ⊗ₜ[R]
        exteriorPower.ιMulti R (c - a) (fun k => (1 : R) ⊗ₜ[B] KaehlerDifferential.D K B (h k))) := by
    rw [TensorProduct.congr_tmul, hA, hB, TensorProduct.smul_tmul_smul]
  simp only [LinearEquiv.trans_apply, piCongrRight_single, LinearEquiv.restrictScalars_apply, ht,
    hmain, Pi.single_smul, map_smul, hE]
  unfold form
  congr 2
  funext k
  simp only [Function.comp_apply, KaehlerDifferential.mapBaseChange_tmul, one_smul]
  generalize Fin.cast _ k = j
  induction j using Fin.addCases with
  | left j => simp [KaehlerDifferential.mapBaseChange_tmul]
  | right j => simp [KaehlerDifferential.mapBaseChange_tmul]

theorem omKun : CrystallineSemistableComparison.Onto.OmKun := by
  intro K A B _ _ _ _ _ c
  let _ : Algebra B (A ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower K B (A ⊗[K] B) := Algebra.TensorProduct.right_isScalarTower
  obtain ⟨e, he⟩ := omKun_pushout K A B (A ⊗[K] B) c
  refine ⟨e, fun a g₀ g h₀ h => ?_⟩
  rw [he]
  congr 1
  change g₀ ⊗ₜ[K] (1 : B) * (1 : A) ⊗ₜ[K] h₀ = _
  simp [Algebra.TensorProduct.tmul_mul_tmul]

end GlobalTheory.CompanionTheory.OmKun
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DWedgeExists
open CrystallineSemistableComparison.Onto

namespace GlobalTheory.CompanionTheory.Forms

theorem dWedge_exists : CrystallineSemistableComparison.Onto.DWedge := by
  intro K A _ _ _ a f
  refine ⟨exteriorPower.alternatingMapLinearEquiv
    ((exteriorPower.ιMulti A (a + 1) (M := Ω[A⁄K])).curryLeft (KaehlerDifferential.D K A f)), ?_⟩
  intro g₀ g
  unfold CrystallineSemistableComparison.Onto.form
  rw [map_smul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.curryLeft_apply_apply]
  congr 2
  funext k
  refine Fin.cases ?_ (fun i => ?_) k <;> simp

end GlobalTheory.CompanionTheory.Forms
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormConsEqSmul
open CrystallineSemistableComparison.Onto

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.OntoDLog

variable {K A : Type} [CommRing K] [CommRing A] [Algebra K A]

theorem form_mul_left {a : ℕ} (c g₀ : A) (g : Fin a → A) :
    form K (c * g₀) g = c • form K g₀ g := by
  simp only [form, mul_smul]

theorem form_cons_mem {a : ℕ} (f h : A) (g : Fin a → A) :
    form K h (Fin.cons f g : Fin (a + 1) → A) ∈ relOm K (Ideal.span {f}) (a + 1) := by
  apply Submodule.subset_span
  exact ⟨h, Fin.cons f g, Or.inr ⟨0, by rw [Fin.cons_zero]; exact Ideal.mem_span_singleton_self f⟩, rfl⟩

theorem form_cons_eq_smul {a : ℕ} (f h g₀ : A) (g : Fin a → A) (k : Fin a)
    (hk : g k = f * h) :
    form K g₀ (Fin.cons f g : Fin (a + 1) → A) =
      f • form K g₀ (Fin.cons f (Function.update g k h) : Fin (a + 1) → A) := by
  set v : Fin (a + 1) → Ω[A⁄K] := fun i =>
    KaehlerDifferential.D K A ((Fin.cons f (Function.update g k h) : Fin (a + 1) → A) i) with hv
  have hcons : (fun i => KaehlerDifferential.D K A ((Fin.cons f g : Fin (a + 1) → A) i)) =
      Function.update v k.succ (f • KaehlerDifferential.D K A h + h • KaehlerDifferential.D K A f) := by
    funext i
    induction i using Fin.cases with
    | zero => simp [v, Function.update_apply, (Fin.succ_ne_zero k).symm]
    | succ j =>
      by_cases hj : j = k
      · subst hj
        simp [hk, Derivation.leibniz]
      · simp [v, hj, Function.update_apply]
  have hv1 : Function.update v k.succ (KaehlerDifferential.D K A h) = v := by
    funext i
    by_cases hi : i = k.succ
    · subst hi
      simp [v]
    · simp [Function.update_apply, hi]
  have hv2 : exteriorPower.ιMulti A (a + 1) (Function.update v k.succ (KaehlerDifferential.D K A f)) = 0 := by
    apply AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := k.succ)
    · simp [v, Function.update_apply, (Fin.succ_ne_zero k).symm]
    · exact (Fin.succ_ne_zero k).symm
  simp only [form]
  rw [hcons, AlternatingMap.map_update_add, AlternatingMap.map_update_smul,
    AlternatingMap.map_update_smul, hv1, hv2, smul_zero, add_zero, smul_comm]

theorem dLog : DLog := by
  unfold DLog
  intro K A _ _ _ a f hf w hw ω hω
  have hex : ∀ ω ∈ relOm K (Ideal.span {f}) a,
      ∃ η ∈ relOm K (Ideal.span {f}) (a + 1), f • η = w ω := by
    intro ω hω
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g₀, g, hg, rfl⟩ := hx
      rcases hg with hg₀ | ⟨k, hk⟩
      · obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hg₀
        refine ⟨form K c (Fin.cons f g), form_cons_mem f c g, ?_⟩
        rw [hw, ← form_mul_left]
      · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hk
        refine ⟨form K g₀ (Fin.cons f (Function.update g k c)), form_cons_mem f g₀ _, ?_⟩
        rw [hw, form_cons_eq_smul f c g₀ g k hc]
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨η₁, h₁, e₁⟩ := hx
      obtain ⟨η₂, h₂, e₂⟩ := hy
      exact ⟨η₁ + η₂, Submodule.add_mem _ h₁ h₂, by rw [smul_add, e₁, e₂, map_add (f := _)]⟩
    | smul c x _ hx =>
      obtain ⟨η, h₁, e₁⟩ := hx
      exact ⟨c • η, Submodule.smul_mem _ c h₁, by rw [smul_comm, e₁, map_smul]⟩
  obtain ⟨η, hη, e⟩ := hex ω hω
  refine ⟨η, ⟨hη, e⟩, ?_⟩
  rintro η' ⟨_, e'⟩
  have hz : f • (η' - η) = 0 := by rw [smul_sub, e, e', sub_self]
  exact sub_eq_zero.mp (hf _ hz)

end GlobalTheory.CompanionTheory.OntoDLog
end

namespace CrystallineSemistableComparison.Onto

theorem parts : Parts := by
  exact {
    mv := GlobalTheory.CompanionTheory.Onto.mvBij
    surj := GlobalTheory.CompanionTheory.OneSurjC.oneSurj
    cov := GlobalTheory.CompanionTheory.CovDescent.covDesc
    site := siteLaws_pf
    on := onIso_pf
    zar := zarAbs_pf
    laws := GlobalTheory.CompanionTheory.OntoForms.formLaws
    dw := GlobalTheory.CompanionTheory.Forms.dWedge_exists
    dl := GlobalTheory.CompanionTheory.OntoDLog.dLog
    kun := GlobalTheory.CompanionTheory.OmKun.omKun
    fc := formCup_pf
    div := divisor_cover_of_chart_laws chartLaws_pf
    chart := chartLaws_pf
    cup := cupLaws_pf
    zarRel := zarRelOf_pf
    affRel := affRelOf_pf
    lift := relLiftOf_pf
    inj := relInjOf_pf topRes_pf
    cone := GlobalTheory.CompanionTheory.ConeKillC.coneKillOf
    killOf := killOf3_pf
    low := ontoLow_pf
    retr := retract_pf
    aff := GlobalTheory.CompanionTheory.AffOmP.affOm formUniq_pf
    c1 := GlobalTheory.CompanionTheory.OntoFirstChernCocycle.main
    kill := GlobalTheory.CompanionTheory.RelKill.relKillOf topRes_pf formUniq_pf omRes_pf
    kunAff := GlobalTheory.CompanionTheory.KunAffP.kunAffOf formUniq_pf
    nat := omNatB_pf
    iso := isoBij_pf
    bij := GlobalTheory.CompanionTheory.ChartBijOf.chartBij_of
      GlobalTheory.CompanionTheory.SurjectionOntoH4.h4a siteLaws_pf
      GlobalTheory.CompanionTheory.CechOne.oneLow
      (GlobalTheory.CompanionTheory.OneResProof.oneRes_of_oneLow
        GlobalTheory.CompanionTheory.CechOne.oneLow)
      GlobalTheory.CompanionTheory.CovDescent.covDesc (zarRelOf_pf siteLaws_pf onIso_pf zarAbs_pf)
      (GlobalTheory.CompanionTheory.AffOmP.affOm formUniq_pf) omNatB_pf omRes_pf
      (affRelOf_pf siteLaws_pf onIso_pf (GlobalTheory.CompanionTheory.AffOmP.affOm formUniq_pf)
        omNatB_pf GlobalTheory.CompanionTheory.OntoForms.formLaws)
      GlobalTheory.CompanionTheory.OntoForms.formLaws chartLaws_pf
    onto := ontoOf3_pf
    slant := GlobalTheory.CompanionTheory.KunGlue.slantOf topRes_pf
  }

theorem htBij_of  (hH : HT.HodgeTateMapExists) (hS : SqEx3) (hD : DiagEt3) (hF : EtFin) : HTBij :=
  htBij_of_parts (parts ) rank_equality hH hS hD hF

end CrystallineSemistableComparison.Onto
