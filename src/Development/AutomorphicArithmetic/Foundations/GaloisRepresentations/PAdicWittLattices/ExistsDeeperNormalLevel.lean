module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIntegralModelNonemptyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateModuleIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionOfBirigidifiedBundleTrivialOnSlice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharZeroGenericModelNonempty
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionOfGeneratingSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveWeightSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

noncomputable section

namespace GlobalTheory.UPel.HT.GenKer

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R' : Type} [CommRing R'] [Algebra ℚ R'] {S : Scheme.{0}}

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (u : Sp B ⟶ Sp A) : ∃ β : A →+* B, u = spMap β :=
  ⟨(Spec.preimage u).hom, by simp [spMap]⟩

theorem charZero_of_hom {k : Type} [Field k] (β : R' →+* k) : CharZero k :=
  charZero_of_injective_ringHom (β.comp (algebraMap ℚ R')).injective

theorem pow_eq_one_geom {gb : GBase D.toG R'} {N : ℕ} {t : S ⟶ Sp R'} (o : GObj gb N t) (e : ℕ)
    (hEF : ∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S)
    (g : Over.mk x₀ ⟶ o.A) (M : ℕ) (hM : 0 < M) (hn : g ^ M = 1)
    (hg : ∃ u : (o.P.pull (lift (snd o.A (Over.mk x₀) ≫ g) (fst o.A (Over.mk x₀))).left).Gen, u.IsGen) :
    g ^ e = 1 := by
  obtain ⟨β, hβ⟩ := exists_spMap (x₀ ≫ t)
  haveI := charZero_of_hom β
  obtain ⟨I, -⟩ := o.geom k x₀ β hβ
  obtain ⟨y, hy⟩ : ∃ y : D.La, I.ev M y = g := (I.onto M hM g).1 hn
  have key : ∀ z : D.La, (M : ℤ) ∣ D.EF y z := by
    intro z
    have hm : 0 < M * 2 := by omega
    have ha : I.ev (M * 2) y ^ 2 = g := by rw [I.tower M 2 hM two_pos y, hy]
    have hc := GlobalTheory.WeilSqKer.weilIs_eq_one S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.symm o.ample k x₀ (M * 2)
      (Nat.cast_ne_zero.2 hm.ne') _ _ ((I.onto _ hm _).2 ⟨y, rfl⟩) ((I.onto _ hm _).2 ⟨z, rfl⟩) (ha ▸ hg) _
      (I.isom _ hm y z)
    have h1 : I.ζ (M * 2) ^ (2 * D.EF y z) = 1 :=
      GlobalTheory.Ex.Specialise.unitOn_bijective.1 (hc.trans (map_one _).symm)
    have h3 := ((I.ζ_prim (M * 2) hm).zpow_eq_one_iff_dvd _).1 h1
    have h4 : (M : ℤ) * 2 ∣ D.EF y z * 2 := by
      rw [mul_comm (D.EF y z)]; exact_mod_cast h3
    exact (mul_dvd_mul_iff_right (by norm_num : (2 : ℤ) ≠ 0)).1 h4
  let f : D.La →ₗ[ℤ] ℤ :=
    { toFun := fun z => D.EF y z / M
      map_add' := fun u v => by
        rw [map_add (f := _), Int.add_ediv_of_dvd_left (key u)]
      map_smul' := fun r u => by
        rw [map_smul, smul_eq_mul, smul_eq_mul, RingHom.id_apply, Int.mul_ediv_assoc _ (key u)] }
  have hf : ∀ z, (M : ℤ) * f z = D.EF y z := fun z => Int.mul_ediv_cancel' (key z)
  obtain ⟨w, hw⟩ := hEF f
  have hyw : e • y = M • w := by
    apply D.nondeg
    ext z
    have hwz : D.EF w z = e • f z := by rw [hw]; rfl
    simp only [map_nsmul, LinearMap.smul_apply, hwz, nsmul_eq_mul]
    rw [← hf z]; ring
  calc g ^ e = I.ev M y ^ e := by rw [hy]
    _ = I.ev M (e • y) := (KerBy.ev_nsmul (La := D.La) _ (I.add M) e y).symm
    _ = 1 := (I.ker M hM _).2 ⟨w, hyw⟩

theorem exists_coprime_pow_eq_one (p : ℕ) [Fact p.Prime] (D : Datum p) (R' : Type) [CommRing R'] [Algebra ℚ R']
    (gb : GBase D.toG R') (N : ℕ) (_hN : 3 ≤ N) (S : Scheme.{0}) (t : S ⟶ Sp R') (o : GObj gb N t) :
    ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ o.A),
      (∃ u : (o.P.pull (lift (snd o.A T ≫ x) (fst o.A T)).left).Gen, u.IsGen) → x ^ e = 1 := by
  obtain ⟨e, he, hEF⟩ := D.perfP
  refine ⟨e, he, fun T x hx => ?_⟩
  apply Over.OverMorphism.ext
  refine T.left.affineCover.hom_ext _ _ fun i => ?_
  obtain ⟨B, ⟨u⟩⟩ : ∃ B : CommRingCat.{0}, Nonempty (T.left.affineCover.X i ≅ Spec B) :=
    ⟨_, ⟨(T.left.affineCover.X i).isoSpec⟩⟩
  rw [← cancel_epi u.inv]
  let a : Sp B ⟶ T.left := u.inv ≫ T.left.affineCover.f i
  let a' : Over.mk (a ≫ T.hom) ⟶ T := Over.homMk a rfl
  have hx' := KerBy.gen_comp S o.A o.P T _ a' x hx
  obtain ⟨M, hM, hxM⟩ := GlobalTheory.T.isTorsion_of_birigidified_bundle_trivial_on_slice S o.A o.P o.ab o.isLB o.rig₁ o.rig₂ o.symm o.ample B (a ≫ T.hom) _ hx'
  have hu : IsUnit ((M : ℕ) : Γ(S, ⊤)) := by
    have h0 : IsUnit ((M : ℕ) : R') := by
      simpa using (IsUnit.mk0 (M : ℚ) (Nat.cast_ne_zero.2 hM.ne')).map (algebraMap ℚ R')
    simpa using (h0.map (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom).map t.appTop.hom
  have h := GlobalTheory.TorsGeomPow.pow_eq_one_of_geometric_points S o.A o.ab M hu _ _ hxM e fun k _ _ ξ =>
    pow_eq_one_geom o e hEF k _ _ M hM (by rw [← MonObj.comp_pow, hxM, MonObj.comp_one])
      (KerBy.gen_comp S o.A o.P _ _ _ _ hx')
  have h' : a' ≫ x ^ e = a' ≫ 1 := by rw [MonObj.comp_pow, h, MonObj.comp_one]
  have h'' : a ≫ (x ^ e).left = a ≫ (1 : T ⟶ o.A).left := congrArg (fun z => z.left) h'
  exact (Category.assoc _ _ _).symm.trans (h''.trans (Category.assoc _ _ _))

end GlobalTheory.UPel.HT.GenKer
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_of_generating_section : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [Algebra ℚ R] (gb : GBase D.toG R) (N : ℕ), 3 ≤ N → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GObj gb N s), ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ o.A), (∃ t : (o.P.pull (lift (snd o.A T ≫ x) (fst o.A T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  first | (exact @GlobalTheory.UPel.HT.GenKer.exists_coprime_pow_eq_one) | (exact GlobalTheory.UPel.HT.GenKer.exists_coprime_pow_eq_one) | (intros; apply GlobalTheory.UPel.HT.GenKer.exists_coprime_pow_eq_one <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharZeroGenericModelNonempty
noncomputable section

namespace GlobalTheory.UPel.HT.Gen

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] [Algebra ℚ R] {S : Scheme.{0}}

def GBase.toBaseAt (gb : GBase D.toG R) : Base D R where
  unit k hk := by
    have hk0 : (k : ℚ) ≠ 0 := by
      rintro h
      have : k = 0 := by exact_mod_cast h
      subst this
      exact (Fact.out : p.Prime).one_lt.ne' (by simpa using hk)
    simpa using (IsUnit.mk0 _ hk0).map (algebraMap ℚ R)
  ρ := gb.ρ
  ρ_root := gb.ρ_root
  t := gb.t
  t_ω := gb.t_ω
  comax := gb.comax
  apart i j _ k _ _ β := by
    exfalso
    have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have h := ((IsUnit.mk0 _ hp).map (algebraMap ℚ R)).map β
    simp at h

theorem fullTate (gb : GBase D.toG R) {N : ℕ} (h3 : 3 ≤ N) (hN : N.Coprime p) {s : S ⟶ Sp R} (o : Obj gb.toBaseAt N s)
    (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : R →+* k) (h : x ≫ s = spMap β) :
    ∃ I : GTateIso D.toG k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
        (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)),
      ∀ y, toUnit _ ≫ o.eta y = I.ev N y := by
  haveI : CharZero k := by
    letI : Algebra ℚ k := (β.comp (algebraMap ℚ R)).toAlgebra
    exact algebraRat.charZero k
  exact GlobalTheory.T.exists_tate_module_iso p D R gb.toBaseAt N h3 hN S s o k x β h

theorem kerPrimeTo {gb : GBase D.toG R} {N : ℕ} (h3 : 3 ≤ N) {s : S ⟶ Sp R} (o : GObj gb N s) :
    ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ o.A),
      (∃ t : (o.P.pull (lift (snd o.A T ≫ x) (fst o.A T)).left).Gen, t.IsGen) → x ^ e = 1 :=
  GlobalTheory.T.torsion_of_generating_section p D R gb N h3 S s o

def GTateIso.toPrimeTo {k : Type} [Field k] {Q : Type} [Group Q] {act : D.O → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : GTateIso D.toG k Q act e) : TateIsoO D k Q act e where
  ζ := I.ζ
  ζ_prim n h _ := I.ζ_prim n h
  ζ_pow n m h h' _ := I.ζ_pow n m h h'
  ev := I.ev
  add := I.add
  lin := I.lin
  ker n h _ := I.ker n h
  onto n h _ := I.onto n h
  tower n m h h' _ := I.tower n m h h'
  isom n h _ := I.isom n h

def GBase.ofObjAt (gb : GBase D.toG R) {N : ℕ} (h3 : 3 ≤ N) (hN : N.Coprime p) {s : S ⟶ Sp R}
    (o : Obj gb.toBaseAt N s) : GObj gb N s where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  rosati := o.rosati
  lie := o.lie
  lieRank := o.lieRank
  eta := o.eta
  eta_add := o.eta_add
  eta_lin := o.eta_lin
  eta_ker := o.eta_ker
  geom := fullTate gb h3 hN o

def GObj.toObjAt {gb : GBase D.toG R} {N : ℕ} {s : S ⟶ Sp R} (o : GObj gb N s) (h3 : 3 ≤ N) :
    Obj gb.toBaseAt N s where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  kerP := kerPrimeTo h3 o
  rosati := o.rosati
  lie := o.lie
  lieRank := o.lieRank
  eta := o.eta
  eta_add := o.eta_add
  eta_lin := o.eta_lin
  eta_ker := o.eta_ker
  geom k _ _ x β h := by
    obtain ⟨I, hI⟩ := o.geom k x β h
    exact ⟨I.toPrimeTo, hI⟩

def GBase.genModelOf (gb : GBase D.toG R) {N : ℕ} (h3 : 3 ≤ N) (hN : N.Coprime p) (M : Model gb.toBaseAt N) :
    GenModel gb N where
  X := M.X
  s := M.s
  univ := gb.ofObjAt h3 hN M.univ
  rep S s' o := by
    obtain ⟨f, ⟨hf, ⟨m⟩⟩, hu⟩ := M.rep S s' (o.toObjAt h3)
    refine ⟨f, ⟨hf, ⟨⟨m.φ, m.φ₂, m.cart, m.sq, m.act, m.pol, m.eta⟩⟩⟩, ?_⟩
    rintro g ⟨hg, ⟨n⟩⟩
    exact hu g ⟨hg, ⟨⟨n.φ, n.φ₂, n.cart, n.sq, n.act, n.pol, n.eta⟩⟩⟩

theorem genModel_nonempty (p : ℕ) [Fact p.Prime] (D : Datum p) (R' : Type) [CommRing R'] [Algebra ℚ R']
    [IsNoetherianRing R'] (gb : GBase D.toG R') (N : ℕ) (h3 : 3 ≤ N) (hN : N.Coprime p) :
    Nonempty (GenModel gb N) := by
  obtain ⟨M⟩ := GlobalTheory.T.harrisTaylorIntegralModel_nonempty p D R' gb.toBaseAt N h3 hN
  exact ⟨gb.genModelOf h3 hN M⟩

end GlobalTheory.UPel.HT.Gen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharZeroGenericModelNonemptyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryCharZeroGenericModel_nonempty : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R' : Type) [CommRing R'] [Algebra ℚ R'] [IsNoetherianRing R'] (gb : GBase D.toG R') (N : ℕ), 3 ≤ N → N.Coprime p → Nonempty (GenModel gb N) := by
  first | (exact @GlobalTheory.UPel.HT.Gen.genModel_nonempty) | (exact GlobalTheory.UPel.HT.Gen.genModel_nonempty) | (intros; apply GlobalTheory.UPel.HT.Gen.genModel_nonempty  <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

section SlopeTestRemainingChoices

open GlobalTheory.KS GlobalTheory.KS.PowPB

private theorem powMap_congr' {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} {f f' : S' ⟶ S}
    {φ φ' : A'.left ⟶ A.left} (hf : f = f') (hφ : φ = φ') (h : φ ≫ A.hom = A'.hom ≫ f)
    (h' : φ' ≫ A.hom = A'.hom ≫ f') (m : ℕ) : powMap f φ h m = powMap f' φ' h' m := by
  subst hf hφ; rfl

private theorem powMap_id' {S : Scheme.{0}} (A : Over S) (h : 𝟙 A.left ≫ A.hom = A.hom ≫ 𝟙 S) (m : ℕ) :
    powMap (𝟙 S) (𝟙 A.left) h m = 𝟙 _ := by
  apply pow_left_hom_ext
  · rw [powMap_w, Category.comp_id, Category.id_comp]
  · intro i
    rw [powMap_pr, Category.comp_id, Category.id_comp]

private theorem powMap_comp' {S S' S'' : Scheme.{0}} {A : Over S} {A' : Over S'} {A'' : Over S''}
    (f : S' ⟶ S) (g : S'' ⟶ S') (φ : A'.left ⟶ A.left) (χ : A''.left ⟶ A'.left)
    (h : φ ≫ A.hom = A'.hom ≫ f) (h' : χ ≫ A'.hom = A''.hom ≫ g)
    (h'' : (χ ≫ φ) ≫ A.hom = A''.hom ≫ g ≫ f) (m : ℕ) :
    powMap g χ h' m ≫ powMap f φ h m = powMap (g ≫ f) (χ ≫ φ) h'' m := by
  apply pow_left_hom_ext
  · rw [Category.assoc, powMap_w, ← Category.assoc, powMap_w, powMap_w, Category.assoc]
  · intro i
    rw [Category.assoc, powMap_pr, ← Category.assoc, powMap_pr, powMap_pr, Category.assoc]

private theorem powMap_ext' {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} (π : S' ⟶ S) (Φ : A'.left ⟶ A.left)
    (w : Φ ≫ A.hom = A'.hom ≫ π) (π' : S' ⟶ S') (Φ' : A'.left ⟶ A'.left) (w' : Φ' ≫ A'.hom = A'.hom ≫ π') (m : ℕ)
    (pb : IsPullback (powMap π Φ w m) (pow A' m).hom (pow A m).hom π) {T : Scheme.{0}} (x y : T ⟶ (pow A' m).left)
    (hxy : x ≫ powMap π Φ w m = y ≫ powMap π Φ w m) (h1 : (x ≫ (pow A' m).hom) ≫ π' = y ≫ (pow A' m).hom)
    (h2 : ∀ a : T ⟶ A'.left, a ≫ A'.hom = x ≫ (pow A' m).hom → a ≫ Φ' ≫ Φ = a ≫ Φ) :
    y = x ≫ powMap π' Φ' w' m := by
  have e1 : x ≫ (pow A' m).hom ≫ π' ≫ π = x ≫ (pow A' m).hom ≫ π := by
    have := congrArg (· ≫ (pow A m).hom) hxy
    simp only [Category.assoc, powMap_w] at this
    rw [← Category.assoc y, ← h1] at this
    simpa only [Category.assoc] using this.symm
  apply pb.hom_ext
  · rw [← hxy, Category.assoc]
    apply pow_left_hom_ext
    · simp only [Category.assoc, powMap_w, reassoc_of% (powMap_w π' Φ' w' m)]
      exact e1.symm
    · intro i
      simp only [Category.assoc, powMap_pr, reassoc_of% (powMap_pr π' Φ' w' m i)]
      have := h2 (x ≫ (pr A' i).left) (by rw [Category.assoc, Over.w])
      simpa only [Category.assoc] using this.symm
  · rw [Category.assoc, powMap_w, ← Category.assoc, h1]

end SlopeTestRemainingChoices

section Lat

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p}

private def intSub (L : Link D G) : Submonoid G.GAf where
  carrier := {h | Integ L h}
  one_mem' := UpperTheory.Gal.Int.Geo.integ_of_mem (one_mem _)
  mul_mem' := UpperTheory.Gal.Int.Geo.Integ.mul

private theorem exists_deeper_normal_level (hK : KNBasic) (L : Link D G) (j : Lv p) (S : Finset (Lv p × G.GAf)) :
    ∃ m : Lv p, L.KN m.1 ≤ L.KN j.1 ∧ (∀ κ ∈ L.KN j.1, ∀ u ∈ L.KN m.1, κ * u * κ⁻¹ ∈ L.KN m.1) ∧
      ∀ x ∈ S, ∀ u ∈ L.KN m.1, x.2 * u * x.2⁻¹ ∈ L.KN x.1.1 := by
  classical
  choose c hc hadm using fun (N : ℕ) (g : G.GAf) => (hK p D G L N).2.1 g
  set M : ℕ := j.1 * ∏ x ∈ S, (x.1.1 * c x.1.1 x.2) with hMdef
  have hcop : M.Coprime p :=
    Nat.Coprime.mul_left j.2.2 (Nat.Coprime.prod_left fun x _ => Nat.Coprime.mul_left x.1.2.2 (hc _ _))
  have hM0 : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · rw [h, Nat.coprime_zero_left] at hcop
      exact absurd hcop (Fact.out : p.Prime).one_lt.ne'
    · exact h
  have hjM : j.1 ∣ M := dvd_mul_right _ _
  refine ⟨⟨M, le_trans j.2.1 (Nat.le_of_dvd hM0 hjM), hcop⟩, UpperTheory.Gal.Int.Geo.KN_anti hjM, ?_, ?_⟩
  · intro κ hκ u hu
    exact (hK p D G L M).1 κ (UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hκ) u hu
  · intro x hx u hu
    have hd : x.1.1 * c x.1.1 x.2 ∣ M := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hx) _
    exact hadm x.1.1 x.2 u (UpperTheory.Gal.Int.Geo.KN_anti hd hu)

end Lat

private theorem comp_univ_hom_eq_of_wit {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {R : Type}
    [CommRing R] [Algebra ℚ R] {gb : GBase D.toG R} {h : G.GAf} {N N' : ℕ} {X' : GenModel gb N'}
    {X : GenModel gb N} {π : X'.X ⟶ X.X} {Φ : X'.univ.A.left ⟶ X.univ.A.left} (hW : Wit L h X' X π Φ) :
    Φ ≫ X.univ.A.hom = X'.univ.A.hom ≫ π := by
  obtain ⟨-, o, ψ, φ, -, rfl⟩ := hW
  rw [Category.assoc, φ.cart.1.w, ← Category.assoc, Over.w]

theorem UpperTheory.Gal.G3.pKSEx :
    KNBasic → WitUniq → WitComp → WitCart → WitEx → WitOne → WitTrans → WitFree → KSEx := by
  intro hK hU hC hCart hEx hOne hTr hFree p _ D G L _ R _ _ gb k
  have hM : ∀ N : Lv p, Nonempty (GenModel gb N.1) := fun N => GlobalTheory.T.unitaryCharZeroGenericModel_nonempty p D R gb N.1 N.2.1 N.2.2
  let M : (N : Lv p) → GenModel gb N.1 := fun N => (hM N).some
  have hint : ∀ {N : ℕ} {u : G.GAf}, u ∈ L.KN N → Integ L u := fun hu =>
    UpperTheory.Gal.Int.Geo.integ_of_mem (UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hu)
  have hw : ∀ (N' N : Lv p) (h : G.GAf), Integ L h → AdmK L N'.1 N.1 h →
      ∃ (π : (M N').X ⟶ (M N).X) (Φ : (M N').univ.A.left ⟶ (M N).univ.A.left), Wit L h (M N') (M N) π Φ :=
    fun N' N h a b => hEx p D G L R gb M N' N h a b
  choose πc Φc hWc using hw
  have hpb : ∀ (i j : Lv p) (a : Integ L 1) (b : AdmK L i.1 j.1 1),
      IsPullback (GlobalTheory.KS.powMap (πc i j 1 a b) (Φc i j 1 a b) (comp_univ_hom_eq_of_wit (hWc i j 1 a b)) k)
        (GlobalTheory.KS.pow (M i).univ.A k).hom (GlobalTheory.KS.pow (M j).univ.A k).hom (πc i j 1 a b) := fun i j a b =>
    GlobalTheory.KS.PowPB.powMap_isPullback _ _ _ _ _ _ _
      (hCart p D G L R gb i.1 j.1 (M i) (M j) 1 (one_mem _) _ _ (hWc i j 1 a b)) k
  let T : Tower (Sp R) G.GAf :=
    Tower.mk (Lv p)
      (K := fun N => L.KN N.1)
      (Δ := intSub L)
      (K_le := fun _ _ hk => hint hk)
      (deep := fun j S => exists_deeper_normal_level hK L j S)
      (idx := fun i j => (hK p D G L j.1).2.2 i.1 (by have := j.2.1; omega) (by have := i.2.1; omega))
      (Z := fun N => (GlobalTheory.KS.pow (M N).univ.A k).left)
      (q := fun N => (GlobalTheory.KS.pow (M N).univ.A k).hom ≫ (M N).s)
      (tr := fun i j h a b => GlobalTheory.KS.powMap (πc i j h a b) (Φc i j h a b) (comp_univ_hom_eq_of_wit (hWc i j h a b)) k)
      (tr_q := by
        intro i j h a b
        rw [← Category.assoc, GlobalTheory.KS.PowPB.powMap_w, Category.assoc, (hWc i j h a b).1])
      (tr_self := by
        intro i u a b hu
        have hid := (hC p D G L R gb i i i (M i) (M i) (M i) u u).1 u hu
        obtain ⟨e1, e2⟩ := hU p D G L R gb i i (M i) (M i) u a b _ _ _ _ (hWc i i u a b) hid
        exact (powMap_congr' e1 e2 _ (by simp) k).trans (powMap_id' _ _ k))
      (tr_mul := by
        intro i j m h h' a b a' b' a'' b''
        have hcomp := (hC p D G L R gb i j m (M i) (M j) (M m) h h').2 a' b' _ _ _ _ (hWc i j h a b) (hWc j m h' a' b')
        obtain ⟨e1, e2⟩ := hU p D G L R gb i m (M i) (M m) (h' * h) a'' b'' _ _ _ _ hcomp (hWc i m (h' * h) a'' b'')
        exact (powMap_comp' _ _ _ _ _ _ (comp_univ_hom_eq_of_wit hcomp) k).trans (powMap_congr' e1 e2 _ _ k))
      (fin := by
        intro i j a b
        exact MorphismProperty.of_isPullback (P := @IsFinite) (hpb i j a b).flip
          (hOne p D G L R gb M i j b _ _ (hWc i j 1 a b)).1)
      (etale := by
        intro i j a b
        exact MorphismProperty.of_isPullback (P := @Etale) (hpb i j a b).flip
          (hOne p D G L R gb M i j b _ _ (hWc i j 1 a b)).2.1)
      (onto := by
        intro i j a b
        exact MorphismProperty.of_isPullback (P := @Surjective) (hpb i j a b).flip
          (hOne p D G L R gb M i j b _ _ (hWc i j 1 a b)).2.2)
      (trans := by
        intro i j a b hnorm Ω _ _ x y hxy
        have hbase : (x ≫ (GlobalTheory.KS.pow (M i).univ.A k).hom) ≫ πc i j 1 a b = (y ≫ (GlobalTheory.KS.pow (M i).univ.A k).hom) ≫ πc i j 1 a b := by
          have := congrArg (· ≫ (GlobalTheory.KS.pow (M j).univ.A k).hom) hxy
          simp only [Category.assoc, GlobalTheory.KS.PowPB.powMap_w] at this
          simpa only [Category.assoc] using this
        obtain ⟨u, hu, hall⟩ := hTr p D G L R gb M i j (πc i j 1 a b) (Φc i j 1 a b) (hWc i j 1 a b) Ω _ _ hbase
        refine ⟨u, hu, hint hu, hnorm u hu, ?_⟩
        obtain ⟨h1, h2⟩ := hall _ _ (hWc i i u (hint hu) (hnorm u hu))
        exact powMap_ext' _ _ _ _ _ _ k (hpb i j a b) x y hxy h1 h2)
      (free := by
        intro i j hij u hu a b Ω _ _ x hx
        refine hFree p D G L R gb M i j hij u hu (πc i i u a b) (Φc i i u a b) (hWc i i u a b) Ω
          (x ≫ (GlobalTheory.KS.pow (M i).univ.A k).hom) ?_
        have := congrArg (· ≫ (GlobalTheory.KS.pow (M i).univ.A k).hom) hx
        simpa only [Category.assoc, GlobalTheory.KS.PowPB.powMap_w] using this)
  refine ⟨⟨T, Equiv.refl _, fun N => rfl, fun h => Iff.rfl, M, fun N => Iso.refl _, fun N => Category.id_comp _, ?_⟩⟩
  intro N' N h a b
  have hc := comp_univ_hom_eq_of_wit (hWc N' N h a b)
  obtain ⟨hs, o, ψ, φ, ht, hΦ⟩ := hWc N' N h a b
  refine ⟨πc N' N h a b, o, ψ, φ, hΦ ▸ hc, hs, ht, ?_⟩
  exact (Category.comp_id _).trans ((powMap_congr' rfl hΦ hc (hΦ ▸ hc) k).trans (Category.id_comp _).symm)
