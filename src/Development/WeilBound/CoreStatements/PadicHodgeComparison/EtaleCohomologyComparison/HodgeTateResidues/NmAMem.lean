module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.FirstChernHodgeTateCompatAlt

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.SmulMorPull
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT.HomP

open Pb

section Gen
variable {R₁ R₂ R₃ R₄ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] [CommRing R₄]
  {C₁ C₂ C₃ C₄ : Type 1} [Category.{0} C₁] [Category.{0} C₂] [Category.{0} C₃] [Category.{0} C₄]
  {F₁ : C₁ ⥤ ModuleCat.{0} R₁} {F₂ : C₂ ⥤ ModuleCat.{0} R₂} {F₃ : C₃ ⥤ ModuleCat.{0} R₃} {F₄ : C₄ ⥤ ModuleCat.{0} R₄}
  {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₄} {σ₃ : R₁ →+* R₃} {σ₄ : R₃ →+* R₄}

theorem sq4 (m₁ : CH.Mor F₁ F₂ σ₁) (m₂ : CH.Mor F₂ F₄ σ₂) (m₃ : CH.Mor F₁ F₃ σ₃) (m₄ : CH.Mor F₃ F₄ σ₄)
    (hσ : ∀ a, σ₄ (σ₃ a) = σ₂ (σ₁ a)) (η : m₂.G ⋙ m₁.G ⟶ m₄.G ⋙ m₃.G)
    (hτ : ∀ (T : C₄) (x : F₁.obj (m₁.G.obj (m₂.G.obj T))),
      m₄.τ T (m₃.τ _ ((F₁.map (η.app T)).hom x)) = m₂.τ T (m₁.τ _ x)) (j : ℕ) (x : CH.H F₁ j) :
    m₂.pull j (m₁.pull j x) = m₄.pull j (m₃.pull j x) := by
  haveI : RingHomCompTriple σ₁ σ₂ (σ₂.comp σ₁) := ⟨rfl⟩
  haveI : RingHomCompTriple σ₃ σ₄ (σ₂.comp σ₁) := ⟨RingHom.ext hσ⟩
  rw [pull_pull (σ₂.comp σ₁), pull_pull (σ₂.comp σ₁)]
  exact CrystallineSemistableComparison.P.prism (m₁.comp m₂) (m₃.comp m₄) η hτ j x

def smulMor (c : R₂) (m : CH.Mor F₁ F₂ σ₁) : CH.Mor F₁ F₂ σ₁ where
  G := m.G
  τ T := { toFun := fun x => c • m.τ T x
           map_add' := fun x y => by rw [map_add (f := _), smul_add]
           map_smul' := fun r x => by rw [LinearMap.map_smulₛₗ, smul_comm] }
  nat φ x := by
    change c • m.τ _ _ = (F₂.map φ).hom (c • m.τ _ x)
    rw [m.nat, map_smul]

theorem smulMor_pull (c : R₂) (m : CH.Mor F₁ F₂ σ₁) (j : ℕ) (x : CH.H F₁ j) : (smulMor c m).pull j x = c • m.pull j x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

end Gen

section Nl
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

def nlHom {T T' : Thick (nlFun γ p X q κ)} (φ : T.B →+* T'.B) (comm : ∀ r, φ (T.i r) = T'.i r) (dp : IsDPMorphism T.δ T'.δ φ)
    (hpt : ∀ h, Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ h)) ≫ pt T = pt T') : T ⟶ T' :=
  mkH φ comm dp (Ideal.map_le_iff_le_comap.1 dp.1) (Subtype.ext (Prod.ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun r => by
    have h1 : (show PtOver X q κ _ from T.y).1.1 (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk T.J (T.i r) := T.w r
    have h2 : (show PtOver X q κ _ from T'.y).1.1 (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk T'.J (T'.i r) := T'.w r
    change Ideal.quotientMap T'.J φ (Ideal.map_le_iff_le_comap.1 dp.1) ((show PtOver X q κ _ from T.y).1.1 (Ideal.Quotient.mk _ r)) =
      (show PtOver X q κ _ from T'.y).1.1 (Ideal.Quotient.mk _ r)
    rw [h1, h2, Ideal.quotientMap_mk, comm])) (hpt _)))

theorem spec_id {B₀ : Type} [CommRing B₀] (J : Ideal B₀) (h) {Z : Scheme.{0}} (y : Spec (CommRingCat.of (B₀ ⧸ J)) ⟶ Z) :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap J (RingHom.id B₀) h)) ≫ y = y := by
  have e : Ideal.quotientMap J (RingHom.id B₀) h = RingHom.id _ := by ext; rfl
  rw [e, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

end Nl

section S
variable {R₁ R₂ R₃ R₄ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] [CommRing R₄]
  {C₁ C₂ C₃ C₄ : Type 1} [Category.{0} C₁] [Category.{0} C₂] [Category.{0} C₃] [Category.{0} C₄]
  {Φ₁ : PDF R₁ C₁} {Φ₂ : PDF R₂ C₂} {Φ₃ : PDF R₃ C₃} {Φ₄ : PDF R₄ C₄}
  {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₄} {σ₃ : R₁ →+* R₃} {σ₄ : R₃ →+* R₄}
  (m₁ : SMor Φ₁ Φ₂ σ₁) (m₂ : SMor Φ₂ Φ₄ σ₂) (m₃ : SMor Φ₁ Φ₃ σ₃) (m₄ : SMor Φ₃ Φ₄ σ₄)
  {a₁ b₁ : IdF Φ₁.A} {a₂ b₂ : IdF Φ₂.A} {a₃ b₃ : IdF Φ₃.A} {a₄ b₄ : IdF Φ₄.A}

theorem genA (hσ : ∀ a, σ₄ (σ₃ a) = σ₂ (σ₁ a)) (η : m₂.G ⋙ m₁.G ⟶ m₄.G ⋙ m₃.G)
    (hρ : ∀ (T : C₄) (x : Φ₁.A.obj (m₁.G.obj (m₂.G.obj T))), m₄.ρ T (m₃.ρ _ ((Φ₁.A.map (η.app T)).hom x)) = m₂.ρ T (m₁.ρ _ x))
    (h₁ : m₁.Le a₁ a₂) (k₁ : m₁.Le b₁ b₂) (h₂ : m₂.Le a₂ a₄) (k₂ : m₂.Le b₂ b₄) (h₃ : m₃.Le a₁ a₃) (k₃ : m₃.Le b₁ b₃)
    (h₄ : m₄.Le a₃ a₄) (k₄ : m₄.Le b₃ b₄) (j : ℕ) (x : CH.H (sq a₁ b₁) j) :
    (m₂.sq h₂ k₂).pull j ((m₁.sq h₁ k₁).pull j x) = (m₄.sq h₄ k₄).pull j ((m₃.sq h₃ k₃).pull j x) := by
  refine sq4 (m₁.sq h₁ k₁) (m₂.sq h₂ k₂) (m₃.sq h₃ k₃) (m₄.sq h₄ k₄) hσ η (fun T x => ?_) j x
  obtain ⟨y, hy, rfl⟩ := sq_surj _ _ x
  exact Subtype.ext (congrArg (Ideal.Quotient.mk _) (hρ T y))

theorem genB (c₁ : R₂) (c c₄ : R₄) (hσ : ∀ a, σ₄ (σ₃ a) = σ₂ (σ₁ a)) (hc : σ₂ c₁ = c * c₄) (η : m₂.G ⋙ m₁.G ⟶ m₄.G ⋙ m₃.G)
    (hρ : ∀ (T : C₄) (x : Φ₁.A.obj (m₁.G.obj (m₂.G.obj T))), m₄.ρ T (m₃.ρ _ ((Φ₁.A.map (η.app T)).hom x)) = m₂.ρ T (m₁.ρ _ x))
    (h₁ : m₁.LeC c₁ a₁ a₂) (k₁ : m₁.LeC c₁ b₁ b₂) (h₂ : m₂.Le a₂ a₄) (k₂ : m₂.Le b₂ b₄) (h₃ : m₃.Le a₁ a₃) (k₃ : m₃.Le b₁ b₃)
    (h₄ : m₄.LeC c₄ a₃ a₄) (k₄ : m₄.LeC c₄ b₃ b₄) (j : ℕ) (x : CH.H (sq a₁ b₁) j) :
    (m₂.sq h₂ k₂).pull j ((m₁.sqC c₁ h₁ k₁).pull j x) = c • (m₄.sqC c₄ h₄ k₄).pull j ((m₃.sq h₃ k₃).pull j x) := by
  refine Eq.trans ?_ (smulMor_pull c (m₄.sqC c₄ h₄ k₄) j _)
  refine sq4 (m₁.sqC c₁ h₁ k₁) (m₂.sq h₂ k₂) (m₃.sq h₃ k₃) (smulMor c (m₄.sqC c₄ h₄ k₄)) hσ η (fun T x => ?_) j x
  obtain ⟨y, hy, rfl⟩ := sq_surj _ _ x
  have e : c • (algebraMap R₄ _ c₄ * m₄.ρ T (m₃.ρ _ ((Φ₁.A.map (η.app T)).hom y))) =
      m₂.ρ T (algebraMap R₂ _ c₁ * m₁.ρ (m₂.G.obj T) y) := by
    rw [hρ, map_mul, m₂.comm, hc, map_mul, Algebra.smul_def, mul_assoc]
  exact Subtype.ext (congrArg (Ideal.Quotient.mk _) e)

theorem genC {a₁' b₁' : IdF Φ₁.A} {a₂' b₂' : IdF Φ₂.A} (h : m₁.Le a₁ a₂) (k : m₁.Le b₁ b₂) (h' : m₁.Le a₁' a₂') (k' : m₁.Le b₁' b₂')
    (e₁ : ∀ T, a₁.S T ≤ a₁'.S T) (f₁ : ∀ T, b₁.S T ≤ b₁'.S T) (e₂ : ∀ T, a₂.S T ≤ a₂'.S T) (f₂ : ∀ T, b₂.S T ≤ b₂'.S T)
    (j : ℕ) (x : CH.H (sq a₁ b₁) j) :
    (sqLe e₂ f₂).pull j ((m₁.sq h k).pull j x) = (m₁.sq h' k').pull j ((sqLe e₁ f₁).pull j x) := by
  refine sq4 (m₁.sq h k) (sqLe e₂ f₂) (sqLe e₁ f₁) (m₁.sq h' k') (fun _ => rfl) (𝟙 m₁.G) (fun T x => ?_) j x
  obtain ⟨y, hy, rfl⟩ := sq_surj _ _ x
  refine Subtype.ext (congrArg (Ideal.Quotient.mk _) ?_)
  change m₁.ρ T ((Φ₁.A.map (𝟙 _)).hom y) = m₁.ρ T y
  rw [Φ₁.A.map_id]
  rfl

end S

section D
variable {O : Type} [CommRing O] {A A' : Type} [CommRing A] [CommRing A'] [Algebra O A] [Algebra O A'] {I : Ideal A} {I' : Ideal A'}
  {γ : DividedPowers I} {γ' : DividedPowers I'} {R : Type} [CommRing R] {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ}
  {X X' : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {q' : X' ⟶ Spec (CommRingCat.of O)} {s s' : ℕ} {sA : A →+* A'}
  (nm : NMor γ q (κA O I) γ' q' (κA O I') sA)
  (hm : ∀ T, TS γ' q' l s' {⊤} T → TS γ q l s {⊤} ((nm.mor 0).obj T))
  (d : RedIn δ κ γ l n) (d' : RedIn δ κ γ' l n) {σ : R →+* R}
  (hd : ∀ (x : R) (a : A), d.ρ x = Ideal.Quotient.mk _ a → d'.ρ (σ x) = Ideal.Quotient.mk _ (sA a))
  (mm : GlobalTheory.LogCris.Mor (nlFun δ l X q κ) (nlFun δ l X' q' κ) σ)
  (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (nlFun δ l X' q' κ).Pt.obj B₀),
    (show PtOver X q κ B₀ from mm.pt.app B₀ y).1.2 = (show PtOver X' q' κ B₀ from y).1.2 ≫ nm.u)

theorem std_le (r : ℤ) : (nm.smor _ _ hm).Le (stdI (TS γ q l s {⊤}) (some r) ((l : A) ^ n)) (stdI (TS γ' q' l s' {⊤}) (some r) ((l : A') ^ n)) := by
  intro T x hx
  have e : T.obj.i (sA ((l : A) ^ n)) = T.obj.i ((l : A') ^ n) := by rw [map_pow sA, map_natCast]
  have hx' : (show T.obj.B from x) ∈ T.obj.pdPow r.toNat ⊔ Ideal.span {T.obj.i (sA ((l : A) ^ n))} := hx
  rw [e] at hx'
  exact hx'

include hd in
theorem r_comm (T : Thick (nlFun γ' 0 X' q' (κA O I'))) (x : R) :
    iBar ((nm.mor 0).obj T) l n (d.ρ x) = iBar T l n (d'.ρ (σ x)) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (d.ρ x)
  rw [hd x a ha.symm, ← ha]
  rfl

def rEta (T : (TS γ' q' l s' {⊤}).FullSubcategory) :
    (redG q s d {⊤}).obj ((nm.smor _ _ hm).G.obj T) ⟶ mm.obj ((redG q' s' d' {⊤}).obj T) :=
  nlHom (T := (redG q s d {⊤}).obj ((nm.smor _ _ hm).G.obj T)) (T' := mm.obj ((redG q' s' d' {⊤}).obj T))
    (RingHom.id (T.obj.B ⧸ lnT T.obj l n)) (r_comm nm d d' hd T.obj)
    (DPMorphism.id (redδ T.obj T.property.1 n)).isDPMorphism fun e => (spec_id _ e _).trans
      ((Category.assoc _ _ _).symm.trans (hpt _ ((redG q' s' d' {⊤}).obj T).y).symm)

def rNat : (nm.smor _ _ hm).G ⋙ redG q s d {⊤} ⟶ redG q' s' d' {⊤} ⋙ mm.functor where
  app := rEta nm hm d d' hd mm hpt
  naturality T T' f := hom_ext (show (RingHom.id (T'.obj.B ⧸ lnT T'.obj l n)).comp (lnMap f.hom.φ l le_rfl) =
    (lnMap f.hom.φ l le_rfl).comp (RingHom.id (T.obj.B ⧸ lnT T.obj l n)) from rfl)

include hd hpt in
theorem genD {Λ : Type} [CommRing Λ] (c : Λ →+* R) (lam : Λ →+* A) (lam' : Λ →+* A') (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a))
    (hc' : ∀ a, d'.ρ (c a) = Ideal.Quotient.mk _ (lam' a)) (sΛ : Λ →+* Λ) (hs : ∀ a, σ (c a) = c (sΛ a))
    (hl : ∀ a, lam' (sΛ a) = sA (lam a)) (r j : ℕ) (x : CH.H (B.pdS (nlFun δ l X q κ) c r).fn j) :
    ((nm.smor _ _ hm).sq (std_le nm hm (r : ℤ)) (std_le nm hm ((r : ℤ) + 1))).pull j ((redSub q s {⊤} d c lam hc r).pull j x) =
      (redSub q' s' {⊤} d' c lam' hc' r).pull j ((pdOm (c := c) (c' := c) mm sΛ hs r).pull j x) := by
  have key := sq4 (F₁ := (B.pdS (nlFun δ l X q κ) c r).fn) (F₃ := (B.pdS (nlFun δ l X' q' κ) c r).fn)
    (redSub q s {⊤} d c lam hc r) ((nm.smor _ _ hm).sq (std_le nm hm (r : ℤ)) (std_le nm hm ((r : ℤ) + 1)))
    (pdOm (L := nlFun δ l X q κ) (L' := nlFun δ l X' q' κ) (c := c) (c' := c) mm sΛ hs r) (redSub q' s' {⊤} d' c lam' hc' r) hl
    (rNat nm hm d d' hd mm hpt)
  refine key (fun T x => ?_) j x
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l n) x
  exact Subtype.ext rfl

end D

end CrystallineSemistableComparison.HT.HomP
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT.HomP

open Pb

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
  {Y : CB l K} {m m' : ℕ} {L : Lv Y m} {L' : Lv Y m'} {sΛ : Y.Λ →+* Y.Λ} {sn : ∀ n, Y.R n →+* Y.R n}
  {sC : ℂ_[l] →+* ℂ_[l]} {c : ℂ_[l]} (h : LHom L L' sΛ sn sC c) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p)

def muEta (T : (L'.QB M).FullSubcategory) :
    (kS L.γB N.q (L.QB N)).G.obj (((h.nmW u hu).smor _ _ (h.nmW_mem u hu)).G.obj T) ⟶
      (smS (Model.genMap u hu) (Model.genMap_q u hu)).G.obj ((kS L'.γB M.q (L'.QB M)).G.obj T) :=
  nlHom (γ := dividedPowersBot K) (κ := Ideal.Quotient.mk ⊥) (RingHom.id T.obj.B) (fun r => congrArg T.obj.i (h.oB r))
    (DPMorphism.id T.obj.δ).isDPMorphism fun e => (spec_id _ e _).trans (by
      change (pt T.obj ≫ Model.genMap u hu) ≫ 𝟙 _ = (pt T.obj ≫ 𝟙 _) ≫ Model.genMap u hu
      rw [Category.comp_id, Category.comp_id])

theorem mu_sq (a r j : ℕ) (y : Hdg N.q a j) :
    h.fW u hu r j (L.μ N a r j y) = h.cB ^ (r - a) • L'.μ M a r j (pullH (Model.genMap u hu) (Model.genMap_q u hu) a j y) :=
  genB (kS L.γB N.q (L.QB N)) ((h.nmW u hu).smor _ _ (h.nmW_mem u hu)) (smS (Model.genMap u hu) (Model.genMap_q u hu))
    (kS L'.γB M.q (L'.QB M)) (L.tB ^ (r - a)) (h.cB ^ (r - a)) (L'.tB ^ (r - a)) (fun k => (h.oB k).symm)
    (by rw [map_pow h.sB, h.t, mul_pow]) ⟨muEta h u hu, fun T T' f => hom_ext rfl⟩ (fun _ _ => rfl) _ _ _ _ _ _ _ _ j y

def nmA : NMor L.γ N.p (κA (OK l K) L.I) L'.γ M.p (κA (OK l K) L'.I) h.sA where
  hI := h.dpA
  u := u
  g := RingHom.id _
  hu := by simpa using hu
  hκ a r e := by
    have h1 := h.dpA.1 (Ideal.mem_map_of_mem h.sA (Ideal.Quotient.eq.1 e))
    rw [map_sub, h.oA] at h1
    exact Ideal.Quotient.eq.2 h1

theorem nmA_mem (T : Thick (nlFun L'.γ 0 M.X M.p (κA (OK l K) L'.I))) (hT : L'.QA M T) : L.QA N (((nmA h u hu).mor 0).obj T) :=
  ⟨⟨le_bot_iff.1 (le_trans (T.pdPow_anti h.le) hT.1.1.le), hT.1.2⟩, ⊤, rfl, le_rfl⟩

def smA : SMor (sP (L.QA N)) (sP (L'.QA M)) h.sA := (nmA h u hu).smor _ _ (nmA_mem h u hu)

def mZ (r : ℕ) : CH.Mor (sq (sFil (L.QA N) r) (sFil (L.QA N) ((r : ℤ) + 1))) (sq (sFil (L'.QA M) r) (sFil (L'.QA M) ((r : ℤ) + 1))) h.sA :=
  (smA h u hu).sq (fun _ _ hx => hx) fun _ _ hx => hx

def mZn (r n : ℕ) : CH.Mor (sq (stdI (L.QA N) (some (r : ℤ)) ((l : L.A) ^ n)) (stdI (L.QA N) (some ((r : ℤ) + 1)) ((l : L.A) ^ n)))
    (sq (stdI (L'.QA M) (some (r : ℤ)) ((l : L'.A) ^ n)) (stdI (L'.QA M) (some ((r : ℤ) + 1)) ((l : L'.A) ^ n))) h.sA :=
  (smA h u hu).sq (std_le (nmA h u hu) (nmA_mem h u hu) _) (std_le (nmA h u hu) (nmA_mem h u hu) _)

theorem red_sq (r n j : ℕ) (z : HG (L.QA N) r j) :
    redG' (L'.QA M) ((l : L'.A) ^ n) r j ((mZ h u hu r).pull j z) = (mZn h u hu r n).pull j (redG' (L.QA N) ((l : L.A) ^ n) r j z) :=
  genC (smA h u hu) _ _ _ _ _ _ _ _ j z

def bEta (T : (L'.QB M).FullSubcategory) :
    (smA h u hu).G.obj (((L'.nmB M).smor _ _ (L'.nmB_mem M)).G.obj T) ⟶
      ((L.nmB N).smor _ _ (L.nmB_mem N)).G.obj (((h.nmW u hu).smor _ _ (h.nmW_mem u hu)).G.obj T) :=
  ObjectProperty.homMk (nlHom (γ := L.γ) (RingHom.id T.obj.B) (fun r => congrArg T.obj.i (h.ι r).symm)
    (DPMorphism.id T.obj.δ).isDPMorphism fun e => (spec_id _ e _).trans (by
      change (pt T.obj ≫ pullback.fst _ _) ≫ u = (pt T.obj ≫ Model.genMap u hu) ≫ pullback.fst _ _
      rw [Category.assoc, Category.assoc, Model.genMap, pullback.lift_fst]))

theorem b_sq (r j : ℕ) (z : HG (L.QA N) r j) :
    L'.bG M r j ((mZ h u hu r).pull j z) = h.fW u hu r j (L.bG N r j z) :=
  genA (smA h u hu) ((L'.nmB M).smor _ _ (L'.nmB_mem M)) ((L.nmB N).smor _ _ (L.nmB_mem N)) ((h.nmW u hu).smor _ _ (h.nmW_mem u hu))
    h.ι ⟨bEta h u hu, fun T T' f => ObjectProperty.hom_ext _ (hom_ext rfl)⟩ (fun _ _ => rfl) _ _ _ _ _ _ _ _ j z

variable {n : ℕ} (mm : GlobalTheory.LogCris.Mor (Y.L N n) (Y.L M n) (sn n))
  (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (Y.L M n).Pt.obj B₀), (mm.pt.app B₀ y).1.2 = (show Spec B₀ ⟶ M.X from y.1.2) ≫ u)

theorem d_comm (x : Y.R n) (a : L.A) (e : (L.d n).ρ x = Ideal.Quotient.mk _ a) : (L'.d n).ρ (sn n x) = Ideal.Quotient.mk _ (h.sA a) := by
  obtain ⟨b, rfl⟩ := Y.c_surj n x
  rw [L.d_lam] at e
  rw [h.cris, L'.d_lam, ← h.lam]
  exact congrArg (lnMap h.sA l (le_refl n)) e

include hpt in
theorem r_sq (r j : ℕ) (x : CH.H (Y.SS N r n).fn j) :
    (mZn h u hu r n).pull j ((L.rS N r n).pull j x) = (L'.rS M r n).pull j ((pdOm mm sΛ (h.cris n) r).pull j x) :=
  genD (nmA h u hu) (nmA_mem h u hu) (L.d n) (L'.d n) (d_comm h) mm hpt (Y.c n) L.lam L'.lam (L.d_lam n) (L'.d_lam n) sΛ (h.cris n)
    (fun a => (h.lam a).symm) r j x

end CrystallineSemistableComparison.HT.HomP

namespace CrystallineSemistableComparison.HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem homMu : HomMu l K := fun h _ _ u hu a r j y => HomP.mu_sq h u hu a r j y

theorem HomP.step {A A' : Type} [CommRing A] [CommRing A'] {s : A →+* A'} {P P' : Type 1} [AddCommGroup P] [Module A P]
    [AddCommGroup P'] [Module A' P'] (f : P →ₛₗ[s] P') (l e : ℕ) {a b : P} {a' b' : P'} (h : a = (l : A) ^ e • b) (ha : a' = f a)
    (hb : f b = b') : a' = (l : A') ^ e • b' := by
  rw [ha, h, LinearMap.map_smulₛₗ, map_pow, map_natCast, hb]

theorem homRho : HomRho l K := fun h _ _ u hu mm hpt r j x w hw => hw.elim fun e he => he.elim fun z hz =>
  ⟨e, (HomP.mZ h u hu r).pull j z,
    fun n => HomP.step ((HomP.mZn h u hu r n).pull j) l e (hz.1 n) (HomP.red_sq h u hu r n j z)
      (HomP.r_sq h u hu (mm n) (hpt n) r j (x n)),
    (HomP.step (h.fW u hu r j) l e hz.2.symm (HomP.b_sq h u hu r j z) rfl).symm⟩

end CrystallineSemistableComparison.HT
