module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.InWmTeichmullerSubOne
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubsingletonH
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TaylorOfLocalFrame
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullTransport

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedHcPullHc
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.CrisTransition

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O]

def redFn (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m) :
    Mor (Lc F κ k m) (Lc F κ k n) ((base l).red h) :=
  B.crMor (F := F) (F' := F) (b := bs l k m) (b' := bs l k n) (ht := rfl) (ht' := rfl) ((base l).red h) rfl
    (dd_red k _ h) (basePt F _ (red_κb κ k h)) fun _ _ _ => rfl

theorem redHc_pullHc {F F' : Fn O} (κ : O →+* OC l) (u : Fn.Map F F') (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ)
    (x : Hc F' κ k m j) : redHc F κ k h j (pullHc κ u k m j x) = pullHc κ u k n j (redHc F' κ k h j x) := by
  unfold redHc pullHc redMor pullMorC
  exact cr_square (SH.pullM κ u k m) (redFn F κ k h) (redFn F' κ k h) (SH.pullM κ u k n) (SH.idc _)
    (red_cris _ h) (red_cris _ h) (SH.idc _) (fun r => (SH.idc ((base l).red h) r).symm)
    (SH.base_map u (red_κb κ k h)) j x

end GlobalTheory.CompanionTheory.CrisTransition
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedHcOneH
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.CrisUnit

universe w w' u v u' v'

theorem pull_oneH {R R' : Type} [CommRing R] [CommRing R'] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {σ : R →+* R'} (A : C ⥤ CommAlgCat.{w} R) (A' : C' ⥤ CommAlgCat.{w'} R')
    (m : CH.Mor (CH.modF A) (CH.modF A') σ)
    (h : ∀ T : C', m.τ T (1 : A.obj (m.G.obj T)) = (1 : A'.obj T)) :
    m.pull 0 (CH.oneH A) = CH.oneH A' := by
  have e : m.hom.f 0 (fun s : ComposableArrows C 0 => (1 : A.obj (s.obj (Fin.last 0)))) =
      fun s : ComposableArrows C' 0 => (1 : A'.obj (s.obj (Fin.last 0))) :=
    funext fun s => h (s.obj (Fin.last 0))
  have c : ∀ s : ComposableArrows C' 1, (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (A'.map (GlobalTheory.CatH.toLast i s)).hom 1 : A'.obj _) = 0 := by
    intro s
    rw [Fin.sum_univ_two, map_one, map_one]
    simp
  unfold CH.Mor.pull CH.oneH
  refine (CrystallineSemistableComparison.P.mapH_cls m.hom 0 _ _ ?_).trans ?_
  · rw [e]
    exact funext c
  · exact congrArg Submodule.Quotient.mk (Subtype.ext e)

theorem omMor_oneH {b b' : Base} {L : b.Fun} {L' : b'.Fun} {σ : b.R →+* b'.R} (m : GlobalTheory.LogCris.Mor L L' σ)
    {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {c : Λ →+* b.R} {c' : Λ' →+* b'.R}
    (σ₀ : Λ →+* Λ') (h : ∀ a, σ (c a) = c' (σ₀ a)) :
    (omMor m σ₀ h).pull 0 (CH.oneH (OA L c)) = CH.oneH (OA L' c') :=
  pull_oneH _ _ _ fun _ => rfl

theorem redHc_oneH : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m), redHc F κ k h 0 (CH.oneH (OcA F κ k m)) = CH.oneH (OcA F κ k n) := by
  intro l _ O _ F κ k m n h
  exact omMor_oneH _ _ _

end GlobalTheory.CompanionTheory.CrisUnit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmMorImg
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

universe w w' v u v' u'

namespace GlobalTheory.CompanionTheory.CrisFil

section General

variable {R R' : Type} [CommRing R] [CommRing R'] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'} {σ : R →+* R'}

def subMor (m : CH.Mor F F' σ) (S : CH.SubF F) (S' : CH.SubF F')
    (h : ∀ (T : C') (x : F.obj (m.G.obj T)), x ∈ S.S (m.G.obj T) → m.τ T x ∈ S'.S T) :
    CH.Mor S.fn S'.fn σ where
  G := m.G
  τ T := ((m.τ T).domRestrict (S.S (m.G.obj T))).codRestrict (S'.S T) fun x => h T x.1 x.2
  nat φ x := Subtype.ext (m.nat φ x.1)

theorem pull_inc (m : CH.Mor F F' σ) (S : CH.SubF F) (S' : CH.SubF F')
    (h : ∀ (T : C') (x : F.obj (m.G.obj T)), x ∈ S.S (m.G.obj T) → m.τ T x ∈ S'.S T) (n : ℕ) (y : CH.H S.fn n) :
    m.pull n (S.inc.pull n y) = S'.inc.pull n ((subMor m S S' h).pull n y) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rfl

theorem pull_img (m : CH.Mor F F' σ) (S : CH.SubF F) (S' : CH.SubF F')
    (h : ∀ (T : C') (x : F.obj (m.G.obj T)), x ∈ S.S (m.G.obj T) → m.τ T x ∈ S'.S T) (n : ℕ) (x : CH.H F n)
    (hx : x ∈ S.img n) : m.pull n x ∈ S'.img n := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨(subMor m S S' h).pull n y, (pull_inc m S S' h n y).symm⟩

end General

section Thick

variable {b b' : Base} {L : b.Fun} {L' : b'.Fun} {σ : b.R →+* b'.R}

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {c : Λ →+* b.R} {c' : Λ' →+* b'.R}

theorem omMor_img (m : GlobalTheory.LogCris.Mor L L' σ) (σ₀ : Λ →+* Λ') (h : ∀ a, σ (c a) = c' (σ₀ a)) (r j : ℕ)
    (x : CH.H (OM L c) j) (hx : x ∈ (pdS L c r).img j) : (omMor m σ₀ h).pull j x ∈ (pdS L' c' r).img j :=
  pull_img (omMor m σ₀ h) (pdS L c r) (pdS L' c' r) (fun _ _ hz => hz) j x hx

end Thick

theorem red_fil : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m)
    (r j : ℕ), ∀ x ∈ HcFil F κ k m r j, redHc F κ k h j x ∈ HcFil F κ k n r j := by
  intro l _ O _ F κ k m n h r j x hx
  exact omMor_img _ _ _ r j x hx

end GlobalTheory.CompanionTheory.CrisFil
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedHcCup
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.CupTrans

theorem omMor_cup {b b' : Base} {L : b.Fun} {L' : b'.Fun} {σ : b.R →+* b'.R} (m : GlobalTheory.LogCris.Mor L L' σ)
    {Λ : Type} [CommRing Λ] {c : Λ →+* b.R} {c' : Λ →+* b'.R} (h : ∀ a, σ (c a) = c' (RingHom.id Λ a))
    {p q s : ℕ} (e : p + q = s) (x : CH.H (OM L c) p) (y : CH.H (OM L c) q) :
    (omMor m (RingHom.id Λ) h).pull s ((CH.mulP (OA L c)).cup e x y) =
      (CH.mulP (OA L' c')).cup e ((omMor m (RingHom.id Λ) h).pull p x) ((omMor m (RingHom.id Λ) h).pull q y) :=
  CrystallineSemistableComparison.P.cup_pull (CH.mulP (OA L c)) (CH.mulP (OA L' c')) m.functor (omMor m (RingHom.id Λ) h).τ
    (omMor m (RingHom.id Λ) h).τ (omMor m (RingHom.id Λ) h).τ (omMor m (RingHom.id Λ) h).nat
    (omMor m (RingHom.id Λ) h).nat (omMor m (RingHom.id Λ) h).nat (fun _ _ _ => rfl) e x y

theorem redHc_cup : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m) {i j s : ℕ} (e : i + j = s) (x : Hc F κ k m i) (y : Hc F κ k m j), redHc F κ k h s ((CH.mulP (OcA F κ k m)).cup e x y) = (CH.mulP (OcA F κ k n)).cup e (redHc F κ k h i x) (redHc F κ k h j y) := by
  intro l _ O _ F κ k m n h i j s e x y
  exact omMor_cup _ _ e x y

end GlobalTheory.CompanionTheory.CupTrans
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMapFactor
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.BetaCmp

theorem quotientMap_factor {B : Type} [CommRing B] {I J K : Ideal B} (hJ : I ≤ J) (hK : I ≤ K) (h : J ≤ K.comap (RingHom.id B))
    (w : B ⧸ I) : Ideal.quotientMap K (RingHom.id B) h (Ideal.Quotient.factor hJ w) = Ideal.Quotient.factor hK w := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
  rfl

theorem pt_uJ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (A : PAlg l) (n : ℕ) (y : F.Pt.obj (CommRingCat.of A.U))
    (h : JJ false A n ≤ (JJ true A n).comap (RingHom.id _)) :
    F.Pt.map (CommRingCat.ofHom (Ideal.quotientMap (JJ true A n) (RingHom.id _) h)) (F.Pt.map (CommRingCat.ofHom (uJ false A n)) y) =
      F.Pt.map (CommRingCat.ofHom (uJ true A n)) y := by
  have e : (Ideal.quotientMap (JJ true A n) (RingHom.id _) h).comp (uJ false A n) = uJ true A n :=
    RingHom.ext fun x => quotientMap_factor (fil_le false A n) (fil_le true A n) h _
  rw [← Functor.map_comp_apply, ← CommRingCat.ofHom_comp, e]

theorem β_cmp : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (n j : ℕ) (x : Hc F κ false n j), β F κ true n j ((cmpMor F κ n).pull j x) = β F κ false n j x := by
  intro l _ O _ F κ n j x
  have e : β F κ true n j ((cmpMor F κ n).pull j x) =
      ((cmpMor F κ n).comp (σ'' := RingHom.id _) (βMor F κ true n)).pull j x :=
    pull_pull (RingHom.id _) (cmpMor F κ n) (βMor F κ true n) j x
  refine e.trans ?_
  refine (cr_pull_eq (βMor F κ false n) ((cmpMor F κ n).comp (σ'' := RingHom.id _) (βMor F κ true n))
    (fun T => crHom (RingHom.id _) (fun _ => rfl) (T.1.obj.dp_fil_pfil n) ?_) ?_ ?_ j x).symm
  · intro h
    exact pt_uJ F T.1.obj n T.2.1 h
  · intro T T' f z; rfl
  · intro T z; rfl

end GlobalTheory.CompanionTheory.BetaCmp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullCup
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.CupBeta
open CrystallineSemistableComparison.CH
universe w u v u' v'

theorem pull_cup {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    (A : C ⥤ CommAlgCat.{w} R) (A' : C' ⥤ CommAlgCat.{w} R) (m : Mor (modF A) (modF A') (RingHom.id R))
    (hm : ∀ T (x y : A.obj (m.G.obj T)), m.τ T ((mulP A).μ _ x y) = (mulP A').μ T (m.τ T x) (m.τ T y))
    {p q n : ℕ} (h : p + q = n) (x : H (modF A) p) (y : H (modF A) q) :
    m.pull n ((mulP A).cup h x y) = (mulP A').cup h (m.pull p x) (m.pull q y) :=
  CrystallineSemistableComparison.P.cup_pull (mulP A) (mulP A') m.G m.τ m.τ m.τ m.nat m.nat m.nat hm h x y

theorem beta_cup {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (n : ℕ) {i j m : ℕ}
    (h : i + j = m) (x : Hc F κ k n i) (y : Hc F κ k n j) :
    β F κ k n m ((CH.mulP (OcA F κ k n)).cup h x y) =
      (CH.mulP (AcrEl (F.pt κ) n)).cup h (β F κ k n i x) (β F κ k n j y) :=
  pull_cup (OcA F κ k n) (AcrEl (F.pt κ) n) (βMor F κ k n) (fun _ _ _ => rfl) h x y

end GlobalTheory.CompanionTheory.CupBeta
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullFrob
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.CrysPhi

theorem pull_frob {O : Type} [CommRing O] {F : Fn O} {b : Base} {ht : b.t = 1} {κ : O →+* b.R ⧸ b.I}
    {Λ : Type} [CommRing Λ] {c : Λ →+* b.R} {σ : b.R →+* b.R} {τ : Λ →+* Λ}
    (mo : GlobalTheory.LogCris.Mor (F.cr b ht κ) (F.cr b ht κ) σ) (h : ∀ a, σ (c a) = c (τ a))
    {C' : Type 1} [Category.{0} C'] {F' : C' ⥤ ModuleCat.{0} Λ}
    (Bm : CH.Mor (OM (F.cr b ht κ) c) F' (RingHom.id Λ)) (Ph : CH.Mor F' F' τ)
    (η : ∀ T, Bm.G.obj (Ph.G.obj T) ⟶ mo.obj (Bm.G.obj T))
    (nat : ∀ {T T' : C'} (f : T ⟶ T') (x : (Bm.G.obj (Ph.G.obj T)).B),
      (η T').φ ((Bm.G.map (Ph.G.map f)).φ x) = (Bm.G.map f).φ ((η T).φ x))
    (hτ : ∀ (T : C') (x : (Bm.G.obj (Ph.G.obj T)).B), Bm.τ T ((η T).φ x) = Ph.τ T (Bm.τ (Ph.G.obj T) x))
    (j : ℕ) (x : CH.H (OM (F.cr b ht κ) c) j) :
    Bm.pull j ((omMor mo τ h).pull j x) = Ph.pull j (Bm.pull j x) := by
  rw [pull_pull τ, pull_pull τ]
  exact (cr_pull_eq (Bm.comp Ph) ((omMor mo τ h).comp Bm) η nat hτ j x).symm

theorem qmap_frb {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] (J : Ideal A) (ph : A →+* A)
    (hl : (l : A ⧸ J) = 0) (hq : J ≤ J.comap ph)
    (hm : ∀ r, Ideal.Quotient.mk J (ph r) = Ideal.Quotient.mk J r ^ l) :
    Ideal.quotientMap J ph hq = frb hl :=
  Ideal.Quotient.ringHom_ext (RingHom.ext hm)

theorem pt_frb {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) {A : Type} [CommRing A] (J : Ideal A) (ph : A →+* A)
    (hl : (l : A ⧸ J) = 0) (hq : J ≤ J.comap ph)
    (hm : ∀ r, Ideal.Quotient.mk J (ph r) = Ideal.Quotient.mk J r ^ l) (z : F.Pt.obj (CommRingCat.of (A ⧸ J))) :
    F.Pt.map (CommRingCat.ofHom (Ideal.quotientMap J ph hq)) z = F.Pt.map (CommRingCat.ofHom (frb hl)) z := by
  rw [qmap_frb J ph hl hq hm]

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

def etaPhi (n : ℕ) (T : El (F.pt κ)) :
    (gT F κ true n).obj T ⟶ (SH.phiM F κ n).obj ((gT F κ true n).obj T) :=
  crHom (T := (gT F κ true n).obj T) (T' := (SH.phiM F κ n).obj ((gT F κ true n).obj T)) (((elπ (F.pt κ)).obj T).phi n)
    (fun r => (mapAcr_phi ((elπ (F.pt κ)).obj T).fromBase n r).symm) (((elπ (F.pt κ)).obj T).dpP_phi n) fun h => by
      exact pt_frb F (((elπ (F.pt κ)).obj T).PFil n) (((elπ (F.pt κ)).obj T).phi n)
        (l_zero ((gT F κ true n).obj T).y.1.1) h (phi_mk _ n) _

theorem phi_beta (n j : ℕ) (x : Hc F κ true n j) :
    β F κ true n j (phiHc F κ n j x) = (phiMor (F.pt κ) n).pull j (β F κ true n j x) :=
  pull_frob (SH.phiM F κ n) ((base l).phi_cris n) (βMor F κ true n) (phiMor (F.pt κ) n) (etaPhi F κ n)
    (fun f x => (mapAcr_phi ((elπ (F.pt κ)).map f) n x).symm) (fun _ _ => rfl) j x

end GlobalTheory.CompanionTheory.CrysPhi
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapHClsEq
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.CrisOne

universe w w' v u v' u'

theorem mapH_cls_eq {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {K : Cx.{w} R} {L : Cx.{w'} R'}
    (φ : Cx.Hom K L σ) (n : ℕ) (a : K.X n) (ha : K.d n a = 0) (b : L.X n) (hb : L.d n b = 0) (e : φ.f n a = b) :
    φ.mapH n (K.cls a ha) = L.cls b hb := by
  subst e
  exact CrystallineSemistableComparison.P.mapH_cls φ n a ha hb

theorem pull_oneH {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {A : C ⥤ CommAlgCat.{w} R} {B : C' ⥤ CommAlgCat.{w'} R}
    (m : CH.Mor (CH.modF A) (CH.modF B) (RingHom.id R))
    (h : ∀ T : C', m.τ T (1 : A.obj (m.G.obj T)) = (1 : B.obj T)) :
    m.pull 0 (CH.oneH A) = CH.oneH B :=
  mapH_cls_eq m.hom 0 _ _ _ _ (funext fun _ => h _)

theorem β_one {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (n : ℕ) :
    β F κ k n 0 (CH.oneH (OcA F κ k n)) = CH.oneH (AcrEl (F.pt κ) n) :=
  pull_oneH (βMor F κ k n) fun _ => rfl

end GlobalTheory.CompanionTheory.CrisOne
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulFil
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

universe w v u

namespace GlobalTheory.CompanionTheory.BetaFil

open CrystallineSemistableComparison.CH CrystallineSemistableComparison.CechClassBoundaries

theorem img_smul {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {F : C ⥤ ModuleCat.{w} R}
    (S S' : SubF F) (a : R) (h : ∀ T, ∀ x ∈ S.S T, a • x ∈ S'.S T) (j : ℕ) :
    ∀ x ∈ S.img j, a • x ∈ S'.img j := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨c, hc, rfl⟩ := clsSurj y
  let α : S.fn ⟶ S'.fn :=
    { app := fun T => ModuleCat.ofHom ((a • (LinearMap.id : F.obj T →ₗ[R] F.obj T)).restrict fun x hx => h T x hx)
      naturality := fun T T' φ => by
        ext x
        exact Subtype.ext (map_smul (F.map φ).hom a x.1).symm }
  have hc' := cyc (Mor.ofNatTrans α).hom c hc
  have hc'' := cyc S'.inc.hom _ hc'
  have hs := cyc S.inc.hom c hc
  refine ⟨(Mor.ofNatTrans α).pull j ((cx S.fn).cls c hc), ?_⟩
  change S'.inc.hom.mapH j ((Mor.ofNatTrans α).hom.mapH j ((cx S.fn).cls c hc)) =
    a • S.inc.hom.mapH j ((cx S.fn).cls c hc)
  rw [mapH_cls' _ c hc hc', mapH_cls' _ _ hc' hc'', mapH_cls' _ c hc hs,
    ← cls_smul a _ hs (by rw [map_smul, hs, smul_zero])]
  rfl

theorem pdS_smul {b : Base} (L : b.Fun) {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (r j : ℕ) (a : Λ)
    (ha : c a ∈ b.I) : ∀ x ∈ (CrystallineSemistableComparison.B.pdS L c r).img j, a • x ∈ (CrystallineSemistableComparison.B.pdS L c (r + 1)).img j :=
  img_smul _ _ a (fun T _ hx => CrystallineSemistableComparison.B.mul_pdPow L T r (T.i_mem ha) hx) j


set_option maxHeartbeats 1000000 in
theorem smul_fil : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (n r j : ℕ) (a : Acris l), (base l).cris n a ∈ JJ k (base l) n → ∀ x ∈ HcFil F κ k n r j, a • x ∈ HcFil F κ k n (r + 1) j := by
  intro l _ O _ F κ k n r j a ha x hx
  exact @pdS_smul (bs l k n) (Lc F κ k n) (Acris l) _ ((base l).cris n) r j a ha x hx

end GlobalTheory.CompanionTheory.BetaFil
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedCmp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.CrisCmp

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

def redMk (k : Bool) {m n : ℕ} (h : n ≤ m) : Mor (Lc F κ k m) (Lc F κ k n) ((base l).red h) :=
  B.crMor (F := F) (F' := F) (b := bs l k m) (b' := bs l k n) (ht := rfl) (ht' := rfl) ((base l).red h) rfl
    (dd_red k _ h) (basePt F _ (red_κb κ k h)) fun _ _ _ => rfl

def cmpMk (n : ℕ) : Mor (Lc F κ false n) (Lc F κ true n) (RingHom.id _) :=
  B.crMor (F := F) (F' := F) (b := bs l false n) (b' := bs l true n) (ht := rfl) (ht' := rfl) (RingHom.id _) rfl
    ((base l).dp_fil_pfil n) (basePt F (Ideal.Quotient.factor le_sup_right) rfl) fun _ _ _ => rfl

theorem fac_κb (n : ℕ) :
    (Ideal.Quotient.factor (S := JJ false (base l) n) (T := JJ true (base l) n) le_sup_right).comp (κb κ false n) = κb κ true n := rfl

theorem cmp_pt {m n : ℕ} (h : n ≤ m) (B₀ : CommRingCat.{0}) (y : (F.ptK (κb κ true n)).obj B₀) :
    ((cmpMk F κ m).pt.app B₀ ((redMk F κ true h).pt.app B₀ y)).1.2 =
      ((redMk F κ false h).pt.app B₀ ((cmpMk F κ n).pt.app B₀ y)).1.2 :=
  SH.base_base F (κ₁ := κb κ false m) (κ₂ := κb κ true m) (κ₃ := κb κ false n) (κ₄ := κb κ true n)
    (fac_κb κ m) (red_κb κ true h) (red_κb κ false h) (fac_κb κ n) B₀ y

theorem red_cmp {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ false m j) :
    redHc F κ true h j ((cmpMor F κ m).pull j x) = (cmpMor F κ n).pull j (redHc F κ false h j x) := by
  unfold redHc redMor cmpMor
  exact cr_square (cmpMk F κ m) (redMk F κ true h) (redMk F κ false h) (cmpMk F κ n) (SH.idc _)
    (red_cris _ h) (red_cris _ h) (SH.idc _) (fun r => (SH.idc ((base l).red h) r).symm)
    (cmp_pt F κ h) j x

theorem main : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ false m j), redHc F κ true h j ((cmpMor F κ m).pull j x) = (cmpMor F κ n).pull j (redHc F κ false h j x) :=
  fun F κ _ _ h j x => red_cmp F κ h j x

end GlobalTheory.CompanionTheory.CrisCmp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiBaseLe
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.CrisFrob

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

def redLe (k : Bool) {m n : ℕ} (h : n ≤ m) : Mor (Lc F κ k m) (Lc F κ k n) ((base l).red h) :=
  B.crMor (F := F) (F' := F) (b := bs l k m) (b' := bs l k n) (ht := rfl) (ht' := rfl) ((base l).red h) rfl
    (dd_red k _ h) (basePt F _ (red_κb κ k h)) fun _ _ _ => rfl

theorem phi_base_le {m n : ℕ} (h : n ≤ m) (B₀ : CommRingCat.{0}) (y : (F.ptK (κb κ true n)).obj B₀) :
    ((phiPt F κ m).app B₀ ((basePt F _ (red_κb κ true h)).app B₀ y)).1.2 =
      ((basePt F _ (red_κb κ true h)).app B₀ ((phiPt F κ n).app B₀ y)).1.2 := by
  rw [SH.phi_snd F κ m B₀ _ (l_zero y.1.1), SH.base_snd, SH.base_snd, SH.phi_snd F κ n B₀ _ (l_zero y.1.1)]

theorem red_phi_le : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {m n : ℕ} (h : n ≤ m) (j : ℕ)
    (x : Hc F κ true m j), redHc F κ true h j (phiHc F κ m j x) = phiHc F κ n j (redHc F κ true h j x) := by
  intro l _ O _ F κ m n h j x
  unfold redHc phiHc redMor phiMorC
  exact cr_square (SH.phiM F κ m) (redLe F κ true h) (redLe F κ true h) (SH.phiM F κ n) ((base l).phi_cris m)
    (red_cris _ h) (red_cris _ h) ((base l).phi_cris n) ((pdOk_frob _).red_acr h) (phi_base_le F κ h) j x

end GlobalTheory.CompanionTheory.CrisFrob
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionCommutesGaloisAction
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.CrisTransition

section

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

theorem red_galBase_le (σ : Gal(PadicAlgCl l/K)) {m n : ℕ} (h : n ≤ m) (r : (base l).Acr m) :
    (base l).red h (galBase σ m r) = galBase σ n ((base l).red h r) :=
  ((pdOk_twId σ _).red_acr h _).trans (congrArg (twAcr σ _ n) ((pdOk_hom (baseTw σ)).red_acr h r))

def redMle (k : Bool) {m n : ℕ} (h : n ≤ m) : Mor (Lc F κ k m) (Lc F κ k n) ((base l).red h) :=
  B.crMor (F := F) (F' := F) (b := bs l k m) (b' := bs l k n) (ht := rfl) (ht' := rfl) ((base l).red h) rfl
    (dd_red k _ h) (basePt F _ (red_κb κ k h)) fun _ _ _ => rfl

theorem reduction_commutes_galois_action (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ)
    (x : Hc F κ k m j) :
    redHc F κ k h j (galHc F κ σ hσ k m j x) = galHc F κ σ hσ k n j (redHc F κ k h j x) := by
  unfold redHc galHc redMor galMorC
  exact cr_square (SH.galM F κ σ hσ k m) (redMle F κ k h) (redMle F κ k h) (SH.galM F κ σ hσ k n) (galBase_cris σ m)
    (red_cris _ h) (red_cris _ h) (galBase_cris σ n) (red_galBase_le σ h)
    (SH.base_base F (gal_κb κ σ hσ k m) (red_κb κ k h) (red_κb κ k h) (gal_κb κ σ hσ k n)) j x

end

theorem redHc_galHc : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ k m j), redHc F κ k h j (galHc F κ σ hσ k m j x) = galHc F κ σ hσ k n j (redHc F κ k h j x) := by
  intro l _ O _ F κ K σ hσ k m n h j x
  exact reduction_commutes_galois_action F κ σ hσ k h j x

end GlobalTheory.CompanionTheory.CrisTransition
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquarePull
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.BetaRed

universe w₁ w₂ w₃ w₄ u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

theorem square_pull {R : Type} [CommRing R] {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
    {C₃ : Type u₃} [Category.{v₃} C₃] {C₄ : Type u₄} [Category.{v₄} C₄]
    {F₁ : C₁ ⥤ ModuleCat.{w₁} R} {F₂ : C₂ ⥤ ModuleCat.{w₂} R} {F₃ : C₃ ⥤ ModuleCat.{w₃} R} {F₄ : C₄ ⥤ ModuleCat.{w₄} R}
    (a : CH.Mor F₁ F₂ (RingHom.id R)) (b : CH.Mor F₂ F₄ (RingHom.id R))
    (c : CH.Mor F₁ F₃ (RingHom.id R)) (d : CH.Mor F₃ F₄ (RingHom.id R))
    (η : d.G ⋙ c.G ⟶ b.G ⋙ a.G)
    (hτ : ∀ T x, b.τ T (a.τ (b.G.obj T) ((F₁.map (η.app T)).hom x)) = d.τ T (c.τ (d.G.obj T) x))
    (j : ℕ) (x : CH.H F₁ j) : b.pull j (a.pull j x) = d.pull j (c.pull j x) := by
  rw [← (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) a b j x).1, ← (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) c d j x).1]
  exact (CrystallineSemistableComparison.P.prism (c.comp d) (a.comp b) η hτ j x).symm

theorem map_map_eq (P : CommRingCat.{0} ⥤ Type) {A B D : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ D) (f' : A ⟶ D)
    (h : f ≫ g = f') (y : P.obj A) : P.map g (P.map f y) = P.map f' y := by
  subst h
  rw [Functor.map_comp_apply]

variable {l : ℕ} [Fact l.Prime]

theorem uJ_red (k : Bool) (A : PAlg l) {m n : ℕ} (h : n ≤ m) (e) :
    (Ideal.quotientMap (JJ k A n) (A.red h) e).comp (uJ k A m) = uJ k A n := RingHom.ext fun x => by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

variable {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

abbrev redCr (k : Bool) {m n : ℕ} (h : n ≤ m) :
    GlobalTheory.LogCris.Mor (Lc F κ k m) (Lc F κ k n) ((base l).red h) :=
  crMor (F := F) (F' := F) (b := bs l k m) (b' := bs l k n) (ht := rfl) (ht' := rfl) ((base l).red h) rfl (dd_red k _ h)
    (basePt F _ (red_κb κ k h)) fun _ _ _ => rfl

def redTh (k : Bool) {m n : ℕ} (h : n ≤ m) (T : (F.pt κ).Elements) :
    gObj F κ k m T ⟶ (redCr F κ k h).obj (gObj F κ k n T) :=
  crHom (T := gObj F κ k m T) (T' := (redCr F κ k h).obj (gObj F κ k n T)) (T.1.red h)
    (fun r => (pdOk_hom T.1.fromBase).red_acr h r) (dd_red k T.1 h) fun e => by
      exact map_map_eq F.Pt (CommRingCat.ofHom (uJ k T.1 m)) (CommRingCat.ofHom (Ideal.quotientMap (JJ k T.1 n) (T.1.red h) e))
        (CommRingCat.ofHom (uJ k T.1 n)) (CommRingCat.hom_ext (uJ_red k T.1 h e)) T.2.1

def redNat (k : Bool) {m n : ℕ} (h : n ≤ m) :
    (CH.Mor.ofNatTrans (redEl (F.pt κ) h)).G ⋙ (βMor F κ k m).G ⟶ (βMor F κ k n).G ⋙ (redMor F κ k h).G where
  app T := redTh F κ k h ((jE (F.pt κ)).obj T)
  naturality T T' f := Thick.Hom.ext (RingHom.ext fun x => (pdOk_hom f.1.hom).red_acr h x) (funext fun j => j.elim)

theorem beta_red (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ k m j) :
    β F κ k n j (redHc F κ k h j x) = (CH.Mor.ofNatTrans (redEl (F.pt κ) h)).pull j (β F κ k m j x) :=
  square_pull (redMor F κ k h) (βMor F κ k n) (βMor F κ k m) (CH.Mor.ofNatTrans (redEl (F.pt κ) h))
    (redNat F κ k h) (fun _ _ => rfl) j x

end GlobalTheory.CompanionTheory.BetaRed
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.PropsC
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.cp_red : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ k m j), β F κ k n j (redHc F κ k h j x) = (CH.Mor.ofNatTrans (redEl (F.pt κ) h)).pull j (β F κ k m j x) :=
  @GlobalTheory.CompanionTheory.BetaRed.beta_red

theorem CrystallineSemistableComparison.B.P.cp_gal : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) (n j : ℕ) (x : Hc F κ k n j), β F κ k n j (galHc F κ σ hσ k n j x) = (galMor σ (ptTw F κ σ hσ) n).pull j (β F κ k n j x) :=
  @GlobalTheory.CompanionTheory.BetaGal.β_gal

theorem CrystallineSemistableComparison.B.P.cp_phi : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (n j : ℕ) (x : Hc F κ true n j), β F κ true n j (phiHc F κ n j x) = (phiMor (F.pt κ) n).pull j (β F κ true n j x) :=
  @GlobalTheory.CompanionTheory.CrysPhi.phi_beta

theorem CrystallineSemistableComparison.B.P.cp_pull : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] {F F' : Fn O} (κ : O →+* OC l) (u : Fn.Map F F') (k : Bool) (n j : ℕ) (x : Hc F' κ k n j), β F κ k n j (pullHc κ u k n j x) = (pullMor (u.pt κ) n).pull j (β F' κ k n j x) :=
  @GlobalTheory.CompanionTheory.BetaPull.beta_pull

theorem CrystallineSemistableComparison.B.P.cp_cmp : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (n j : ℕ) (x : Hc F κ false n j), β F κ true n j ((cmpMor F κ n).pull j x) = β F κ false n j x :=
  @GlobalTheory.CompanionTheory.BetaCmp.β_cmp

theorem CrystallineSemistableComparison.B.P.cp_cup : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (n : ℕ) {i j m : ℕ} (h : i + j = m) (x : Hc F κ k n i) (y : Hc F κ k n j), β F κ k n m ((CH.mulP (OcA F κ k n)).cup h x y) = (CH.mulP (AcrEl (F.pt κ) n)).cup h (β F κ k n i x) (β F κ k n j y) :=
  @GlobalTheory.CompanionTheory.CupBeta.beta_cup

theorem CrystallineSemistableComparison.B.P.cp_one : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (n : ℕ), β F κ k n 0 (CH.oneH (OcA F κ k n)) = CH.oneH (AcrEl (F.pt κ) n) :=
  @GlobalTheory.CompanionTheory.CrisOne.β_one

theorem CrystallineSemistableComparison.B.P.cp_red_fil : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m) (r j : ℕ), ∀ x ∈ HcFil F κ k m r j, redHc F κ k h j x ∈ HcFil F κ k n r j :=
  @GlobalTheory.CompanionTheory.CrisFil.red_fil

theorem CrystallineSemistableComparison.B.P.cp_smul_fil : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (n r j : ℕ) (a : Acris l), (base l).cris n a ∈ JJ k (base l) n → ∀ x ∈ HcFil F κ k n r j, a • x ∈ HcFil F κ k n (r + 1) j :=
  @GlobalTheory.CompanionTheory.BetaFil.smul_fil

theorem CrystallineSemistableComparison.B.P.ch_gal : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ k m j), redHc F κ k h j (galHc F κ σ hσ k m j x) = galHc F κ σ hσ k n j (redHc F κ k h j x) :=
  @GlobalTheory.CompanionTheory.CrisTransition.redHc_galHc

theorem CrystallineSemistableComparison.B.P.ch_phi : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ true m j), redHc F κ true h j (phiHc F κ m j x) = phiHc F κ n j (redHc F κ true h j x) :=
  @GlobalTheory.CompanionTheory.CrisFrob.red_phi_le

theorem CrystallineSemistableComparison.B.P.ch_pull : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] {F F' : Fn O} (κ : O →+* OC l) (u : Fn.Map F F') (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F' κ k m j), redHc F κ k h j (pullHc κ u k m j x) = pullHc κ u k n j (redHc F' κ k h j x) :=
  @GlobalTheory.CompanionTheory.CrisTransition.redHc_pullHc

theorem CrystallineSemistableComparison.B.P.ch_cup : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m) {i j s : ℕ} (e : i + j = s) (x : Hc F κ k m i) (y : Hc F κ k m j), redHc F κ k h s ((CH.mulP (OcA F κ k m)).cup e x y) = (CH.mulP (OcA F κ k n)).cup e (redHc F κ k h i x) (redHc F κ k h j y) :=
  @GlobalTheory.CompanionTheory.CupTrans.redHc_cup

theorem CrystallineSemistableComparison.B.P.ch_one : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m), redHc F κ k h 0 (CH.oneH (OcA F κ k m)) = CH.oneH (OcA F κ k n) :=
  @GlobalTheory.CompanionTheory.CrisUnit.redHc_oneH

theorem CrystallineSemistableComparison.B.P.ch_cmp : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ false m j), redHc F κ true h j ((cmpMor F κ m).pull j x) = (cmpMor F κ n).pull j (redHc F κ false h j x) :=
  @GlobalTheory.CompanionTheory.CrisCmp.main

theorem CrystallineSemistableComparison.B.P.firstChern_compatible : ∀ (l : ℕ) [Fact l.Prime], FirstChernCompatible l :=
  @GlobalTheory.CompanionTheory.FirstChernComparison.main
end

namespace CrystallineSemistableComparison.B

variable (l : ℕ) [Fact l.Prime]

theorem main : Main l := main_of (D.out l)

theorem compat : Compat l :=
  ⟨P.cp_red, P.cp_gal, P.cp_phi, P.cp_pull, P.cp_cmp, P.cp_cup, P.cp_one, P.cp_red_fil, P.cp_smul_fil⟩

theorem compatH : CompatH l := ⟨P.ch_gal, P.ch_phi, P.ch_pull, P.ch_cup, P.ch_one, P.ch_cmp⟩

theorem firstChern_compatible_l : FirstChernCompatible l := P.firstChern_compatible l

end CrystallineSemistableComparison.B
