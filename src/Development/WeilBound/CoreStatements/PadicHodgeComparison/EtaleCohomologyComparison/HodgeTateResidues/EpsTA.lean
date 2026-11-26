module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernClassInFamily
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.ExistsEpsPeriodTUnit
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.EtDefs

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.EpsTA
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge Formalism.Per6

namespace CrystallineSemistableComparison.HT

variable (l : ℕ) [Fact l.Prime]

theorem eps_tA : ∃ (ε : B.Eps l) (u : Acris l), tA l = ε.μ * u := by
  obtain ⟨u, hu, e⟩ := ACris.exists_periodT_eq_mu_mul_unit (K := ℂ_[l]) (p := l) (untilt_epsilon (p := l))
    untilt_frobeniusEquiv_symm_epsilon_ne_one
  exact ⟨GlueBE.eps l, u, by rw [GlueBE.eps_μ]; exact e⟩

theorem tFil : TFil l := fun A n =>
  (eps_tA l).elim fun ε h => h.elim fun u hu => by
    rw [hu, map_mul]
    exact Ideal.mul_mem_right _ _ (ε.μ_mem false A n)

end CrystallineSemistableComparison.HT
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.ResMIncl
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.HT

open Pb

section Gen
variable {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L))

def resM (r r' : ℤ) : CH.Mor (sq (thFil L r) (thFil L r')) (sq (sFil Q r) (sFil Q r')) (RingHom.id b.R) where
  G := Q.ι
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem resM_all (h : ∀ T, Q T) (r r' : ℤ) (n : ℕ) : Function.Bijective ((resM Q r r').pull n) := by
  have e1 : Q.ι.EssSurj := ⟨fun T => ⟨⟨T, h T⟩, ⟨Iso.refl _⟩⟩⟩
  have e2 : Q.ι.IsEquivalence := {}
  have : (resM Q r r').G.IsLeftAdjoint := inferInstanceAs Q.ι.IsLeftAdjoint
  exact CrystallineSemistableComparison.P.adj_mor _ (fun _ => Function.bijective_id) n

variable {Q} in
theorem resM_incl {Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r r' : ℤ) (n : ℕ) (x : CH.H (sq (thFil L r) (thFil L r')) n) :
    (resM Q' r r').pull n x = ((incl h).sq (incl_fil h r) (incl_fil h r')).pull n ((resM Q r r').pull n x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => ?_))
  change (z.1 (s ⋙ Q'.ι) : sqM _ _ _) = ((incl h).sq (incl_fil h r) (incl_fil h r')).τ _ (z.1 (s ⋙ Q'.ι))
  obtain ⟨y, hy, e⟩ := sq_surj _ _ (z.1 (s ⋙ Q'.ι))
  rw [← e]
  rfl

end Gen

section K
variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

def resH (Q : ObjectProperty (Thick (smFun X q))) (a n : ℕ) : Hdg q a n →ₗ[K] HQ Q (a : ℤ) ((a : ℤ) + 1) n :=
  (resM Q (a : ℤ) ((a : ℤ) + 1)).pull n

theorem res_bij (s : ℕ) (𝒱 : Set X.Opens) (h𝒱 : sSup 𝒱 = ⊤) (r r' : ℤ) (hr : r' ≤ s) (n : ℕ) :
    Function.Bijective ((resM (TO q 1 s 𝒱) r r').pull n) := by
  let Q₀ : ObjectProperty (Thick (smFun X q)) :=
    St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) ⊤ {⊤}
  have h0 : ∀ T, Q₀ T := fun T => ⟨trivial, ⊤, rfl, le_rfl⟩
  have h1 : TO q 1 s {⊤} ≤ Q₀ := fun T _ => h0 T
  have h2 : TO q 1 s 𝒱 ≤ TO q 1 s {⊤} := fun T hT => ⟨hT.1, ⊤, rfl, le_rfl⟩
  have b0 := resM_all Q₀ h0 r r' n
  have b1 := refl (γ := dividedPowersBot K) (q := q) (κ := Ideal.Quotient.mk ⊥) ⊤ 1 s (Or.inl ⟨rfl, rfl⟩) {⊤} h1 r r' hr n
  have b2 := (zar (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) (Or.inl ⟨rfl, 1, s, rfl⟩) 𝒱 {⊤} h2
    (fun W _ => by rw [h𝒱]; exact le_top) n).1 r r'
  have e : ⇑((resM (TO q 1 s 𝒱) r r').pull n) = ((incl h2).sq (incl_fil h2 r) (incl_fil h2 r')).pull n ∘
      ((incl h1).sq (incl_fil h1 r) (incl_fil h1 r')).pull n ∘ (resM Q₀ r r').pull n := funext fun x =>
    (resM_incl h2 r r' n x).trans (congrArg _ (resM_incl h1 r r' n x))
  rw [e]
  exact b2.comp (b1.comp b0)

theorem hdg_res (s : ℕ) (𝒱 : Set X.Opens) (h𝒱 : sSup 𝒱 = ⊤) (a : ℕ) (ha : a < s) (n : ℕ) :
    Function.Bijective (resH q (TO q 1 s 𝒱) a n) := res_bij q s 𝒱 h𝒱 _ _ (by omega) n

end K

end CrystallineSemistableComparison.HT
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.RedPullPd
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6

universe u v w

namespace CrystallineSemistableComparison.HT

open PAlg

section Gen
variable {O : Type} [CommRing O] {F : B.Fn O} {b : Base} {ht : b.t = 1} {κ : O →+* b.R ⧸ b.I}

theorem pd_pull_eq {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {c : Λ →+* b.R} {σ : Λ →+* Λ'} {C' : Type u} [Category.{v} C']
    {F' : C' ⥤ ModuleCat.{w} Λ'} {r : ℕ} (m m' : CH.Mor (B.pdS (F.cr b ht κ) c r).fn F' σ) (η : ∀ T, m.G.obj T ⟶ m'.G.obj T)
    (nat : ∀ {T T' : C'} (f : T ⟶ T') (x : (m.G.obj T).B), (η T').φ ((m.G.map f).φ x) = (m'.G.map f).φ ((η T).φ x))
    (hτ : ∀ (T : C') (x : (m.G.obj T).B) hx hx', m'.τ T ⟨(η T).φ x, hx'⟩ = m.τ T ⟨x, hx⟩) (n : ℕ)
    (x : CH.H (B.pdS (F.cr b ht κ) c r).fn n) : m.pull n x = m'.pull n x :=
  CrystallineSemistableComparison.P.prism m m' ⟨η, fun _ _ f => Thick.Hom.ext (RingHom.ext (nat f)) (funext fun j => j.elim)⟩
    (fun T x => hτ T x.1 x.2 _) n x

end Gen

theorem pd_square {O : Type} [CommRing O] {F₁ F₂ F₃ F₄ : B.Fn O} {b₁ b₂ b₃ b₄ : Base} {h₁ : b₁.t = 1} {h₂ : b₂.t = 1} {h₃ : b₃.t = 1}
    {h₄ : b₄.t = 1} {κ₁ : O →+* b₁.R ⧸ b₁.I} {κ₂ : O →+* b₂.R ⧸ b₂.I} {κ₃ : O →+* b₃.R ⧸ b₃.I} {κ₄ : O →+* b₄.R ⧸ b₄.I}
    {Λ : Type} [CommRing Λ] {c₁ : Λ →+* b₁.R} {c₂ : Λ →+* b₂.R} {c₃ : Λ →+* b₃.R} {c₄ : Λ →+* b₄.R}
    {σa : b₁.R →+* b₂.R} {σb : b₂.R →+* b₄.R} {σc : b₁.R →+* b₃.R} {σd : b₃.R →+* b₄.R} {τ : Λ →+* Λ}
    (ma : Mor (F₁.cr b₁ h₁ κ₁) (F₂.cr b₂ h₂ κ₂) σa) (mb : Mor (F₂.cr b₂ h₂ κ₂) (F₄.cr b₄ h₄ κ₄) σb)
    (mc : Mor (F₁.cr b₁ h₁ κ₁) (F₃.cr b₃ h₃ κ₃) σc) (md : Mor (F₃.cr b₃ h₃ κ₃) (F₄.cr b₄ h₄ κ₄) σd)
    (ha : ∀ a, σa (c₁ a) = c₂ (τ a)) (hb : ∀ a, σb (c₂ a) = c₄ (RingHom.id Λ a)) (hc : ∀ a, σc (c₁ a) = c₃ (RingHom.id Λ a))
    (hd : ∀ a, σd (c₃ a) = c₄ (τ a)) (hσ : ∀ r, σb (σa r) = σd (σc r))
    (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (F₄.cr b₄ h₄ κ₄).Pt.obj B₀),
      (ma.pt.app B₀ (mb.pt.app B₀ y)).1.2 = (mc.pt.app B₀ (md.pt.app B₀ y)).1.2)
    (r j : ℕ) (x : CH.H (B.pdS (F₁.cr b₁ h₁ κ₁) c₁ r).fn j) :
    (pdOm (c := c₂) (c' := c₄) mb (RingHom.id Λ) hb r).pull j ((pdOm (c := c₁) (c' := c₂) ma τ ha r).pull j x) =
      (pdOm (c := c₃) (c' := c₄) md τ hd r).pull j ((pdOm (c := c₁) (c' := c₃) mc (RingHom.id Λ) hc r).pull j x) := by
  rw [pull_pull τ, pull_pull τ]
  exact pd_pull_eq _ _ (fun T => crHom (T := ma.obj (mb.obj T)) (T' := mc.obj (md.obj T)) (RingHom.id T.B)
    (fun r => congrArg T.i (hσ r)) (DPMorphism.id T.δ).isDPMorphism fun h => (pt_id _ h _).trans (hpt _ _))
    (fun _ _ => rfl) (fun _ _ _ _ => rfl) j x

theorem pd_id {O : Type} [CommRing O] {F : B.Fn O} {b : Base} {h : b.t = 1} {κ : O →+* b.R ⧸ b.I} {Λ : Type} [CommRing Λ]
    {c : Λ →+* b.R} {σ : b.R →+* b.R} (m : Mor (F.cr b h κ) (F.cr b h κ) σ) (hc : ∀ a, σ (c a) = c (RingHom.id Λ a))
    (hσ : ∀ r, σ r = r) (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (F.cr b h κ).Pt.obj B₀), (m.pt.app B₀ y).1.2 = y.1.2)
    (r j : ℕ) (x : CH.H (B.pdS (F.cr b h κ) c r).fn j) : (pdOm (c := c) (c' := c) m (RingHom.id Λ) hc r).pull j x = x :=
  (pd_pull_eq (pdOm (c := c) (c' := c) m (RingHom.id Λ) hc r) (CH.Mor.id _)
    (fun T => crHom (T := m.obj T) (T' := T) (RingHom.id T.B) (fun r => congrArg T.i (hσ r)) (DPMorphism.id T.δ).isDPMorphism
      fun h => (pt_id _ h _).trans (hpt _ _)) (fun _ _ => rfl) (fun _ _ _ _ => rfl) j x).trans
    (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id Λ) (CH.Mor.id _) (CH.Mor.id _) j x).2

theorem pd_om_sh {b b' : Base} {L : b.Fun} {L' : b'.Fun} {σ : b.R →+* b'.R} (m : Mor L L' σ) {Λ : Type} [CommRing Λ]
    {c : Λ →+* b.R} {c' : Λ →+* b'.R} (h : ∀ a, σ (c a) = c' (RingHom.id Λ a)) {t : Λ} (h1 : c t ∈ b.I) (h2 : c' t ∈ b'.I)
    {r r' : ℕ} (k : ℕ) (e : r + k = r') (j : ℕ) (x : CH.H (B.pdS L c r).fn j) :
    (pdOm (c := c) (c' := c') m (RingHom.id Λ) h r').pull j ((pdSh L c h1 k e).pull j x) =
      (pdSh L' c' h2 k e).pull j ((pdOm (c := c) (c' := c') m (RingHom.id Λ) h r).pull j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
  exact congrArg (fun u => (s.obj (Fin.last j)).i u *
    (show (s.obj (Fin.last j)).B from (show (B.pdS L c r).S _ from z.1 (s ⋙ m.functor)).1)) (h (t ^ k))

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section F
variable {O : Type} [CommRing O] (F : B.Fn O) (κ : O →+* OC l)

theorem red_gal_pd (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (r n j : ℕ)
    (x : CH.H (B.pdS (B.Lc F κ false (n + 1)) ((base l).cris (n + 1)) r).fn j) :
    (pdOm (CrystallineSemistableComparison.SH.redM F κ false n) (RingHom.id _) (B.red_cris _ n.le_succ) r).pull j
        ((pdOm (CrystallineSemistableComparison.SH.galM F κ σ hσ false (n + 1)) (ACris.galCris σ) (galBase_cris σ (n + 1)) r).pull j x) =
      (pdOm (CrystallineSemistableComparison.SH.galM F κ σ hσ false n) (ACris.galCris σ) (galBase_cris σ n) r).pull j
        ((pdOm (CrystallineSemistableComparison.SH.redM F κ false n) (RingHom.id _) (B.red_cris _ n.le_succ) r).pull j x) :=
  pd_square (CrystallineSemistableComparison.SH.galM F κ σ hσ false (n + 1)) (CrystallineSemistableComparison.SH.redM F κ false n) (CrystallineSemistableComparison.SH.redM F κ false n)
    (CrystallineSemistableComparison.SH.galM F κ σ hσ false n) (galBase_cris σ (n + 1)) (B.red_cris _ n.le_succ) (B.red_cris _ n.le_succ) (galBase_cris σ n)
    (CrystallineSemistableComparison.SH.red_galBase σ n)
    (CrystallineSemistableComparison.SH.base_base F (B.gal_κb κ σ hσ false (n + 1)) (B.red_κb κ false n.le_succ) (B.red_κb κ false n.le_succ)
      (B.gal_κb κ σ hσ false n)) r j x

variable {F} {F' : B.Fn O}

theorem red_pull_pd (u : B.Fn.Map F F') (r n j : ℕ) (x : CH.H (B.pdS (B.Lc F' κ false (n + 1)) ((base l).cris (n + 1)) r).fn j) :
    (pdOm (CrystallineSemistableComparison.SH.redM F κ false n) (RingHom.id _) (B.red_cris _ n.le_succ) r).pull j
        ((pdOm (CrystallineSemistableComparison.SH.pullM κ u false (n + 1)) (RingHom.id _) (CrystallineSemistableComparison.SH.idc _) r).pull j x) =
      (pdOm (CrystallineSemistableComparison.SH.pullM κ u false n) (RingHom.id _) (CrystallineSemistableComparison.SH.idc _) r).pull j
        ((pdOm (CrystallineSemistableComparison.SH.redM F' κ false n) (RingHom.id _) (B.red_cris _ n.le_succ) r).pull j x) :=
  pd_square (CrystallineSemistableComparison.SH.pullM κ u false (n + 1)) (CrystallineSemistableComparison.SH.redM F κ false n) (CrystallineSemistableComparison.SH.redM F' κ false n)
    (CrystallineSemistableComparison.SH.pullM κ u false n) (CrystallineSemistableComparison.SH.idc _) (B.red_cris _ n.le_succ) (B.red_cris _ n.le_succ) (CrystallineSemistableComparison.SH.idc _)
    (fun r => (CrystallineSemistableComparison.SH.idc ((base l).red n.le_succ) r).symm) (CrystallineSemistableComparison.SH.base_map u (B.red_κb κ false n.le_succ)) r j x

end F

variable {M N : Model l K} {r r' j : ℕ}

theorem comp_add {x y : Fam M r j} (hx : Comp x) (hy : Comp y) : Comp (x + y) := fun n =>
  (map_add (redS M r n j) (x (n + 1)) (y (n + 1))).trans (congrArg₂ (· + ·) (hx n) (hy n))

theorem comp_smul (c : Acris l) {x : Fam M r j} (hx : Comp x) : Comp (c • x) := fun n =>
  (map_smul (redS M r n j) c (x (n + 1))).trans (congrArg (c • ·) (hx n))

theorem comp_sh (ht : TFil l) (k : ℕ) (h : r + k = r') {x : Fam M r j} (hx : Comp x) : Comp (shS ht k h x) := fun n =>
  (pd_om_sh (CrystallineSemistableComparison.SH.redM (B.schFn M.p) (okToOC l K) false n) (B.red_cris _ n.le_succ) (ht (base l) (n + 1)) (ht (base l) n)
    k h j (x (n + 1))).trans (congrArg ((pdSh (M.L false n) ((base l).cris n) (ht (base l) n) k h).pull j) (hx n))

theorem comp_gal (σ : K.fixingSubgroup) {x : Fam M r j} (hx : Comp x) : Comp (galS σ x) := fun n =>
  (red_gal_pd (B.schFn M.p) (okToOC l K) (IntermediateField.fixingSubgroupEquiv K σ) (galOC_okToOC _) r n j (x (n + 1))).trans
    (congrArg ((pdOm (CrystallineSemistableComparison.SH.galM (B.schFn M.p) (okToOC l K) (IntermediateField.fixingSubgroupEquiv K σ) (galOC_okToOC _) false n)
      (ACris.galCris (IntermediateField.fixingSubgroupEquiv K σ)) (galBase_cris _ n) r).pull j) (hx n))

theorem comp_pull (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) {x : Fam N r j} (hx : Comp x) : Comp (pullS u hu x) := fun n =>
  (red_pull_pd (okToOC l K) (B.schMap u hu) r n j (x (n + 1))).trans
    (congrArg ((pdOm (CrystallineSemistableComparison.SH.pullM (okToOC l K) (B.schMap u hu) false n) (RingHom.id _) (CrystallineSemistableComparison.SH.idc _) r).pull j) (hx n))

end CrystallineSemistableComparison.HT
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsLiftOneSOfLevEqOne
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6

namespace CrystallineSemistableComparison.HT

open CH PAlg

section Gen
variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C C' : Type 1} [Category.{0} C] [Category.{0} C']

theorem subMor_cup {A : C ⥤ CommAlgCat.{0} R} {A' : C' ⥤ CommAlgCat.{0} R'} (m : CH.Mor (modF A) (modF A') σ)
    (hm : ∀ (T : C') (x y : A.obj (m.G.obj T)), m.τ T (x * y) = (show A'.obj T from m.τ T x) * (show A'.obj T from m.τ T y))
    {S₁ S₂ S₃ : SubF (modF A)} {S₁' S₂' S₃' : SubF (modF A')} (h₁ h₂ h₃) (hS hS') {p q n : ℕ} (h : p + q = n)
    (x : H S₁.fn p) (y : H S₂.fn q) :
    (subMor m S₃ S₃' h₃).pull n ((subPair S₁ S₂ S₃ hS).cup h x y) =
      (subPair S₁' S₂' S₃' hS').cup h ((subMor m S₁ S₁' h₁).pull p x) ((subMor m S₂ S₂' h₂).pull q y) :=
  CrystallineSemistableComparison.P.cup_pull (subPair S₁ S₂ S₃ hS) (subPair S₁' S₂' S₃' hS') m.G (subMor m S₁ S₁' h₁).τ (subMor m S₂ S₂' h₂).τ
    (subMor m S₃ S₃' h₃).τ (subMor m S₁ S₁' h₁).nat (subMor m S₂ S₂' h₂).nat (subMor m S₃ S₃' h₃).nat
    (fun T x y => Subtype.ext (hm T _ _)) h x y

theorem mulTo_cup {A : C ⥤ CommAlgCat.{0} R} {c₁ c₂ c₃ : R} (hc : c₃ = c₁ * c₂) {S₁ S₂ S₃ : SubF (modF A)} (h₁ h₂ h₃) (hS)
    {p q n : ℕ} (h : p + q = n) (x : H (modF A) p) (y : H (modF A) q) :
    (mulTo c₃ S₃ h₃).pull n ((mulP A).cup h x y) =
      (subPair S₁ S₂ S₃ hS).cup h ((mulTo c₁ S₁ h₁).pull p x) ((mulTo c₂ S₂ h₂).pull q y) :=
  CrystallineSemistableComparison.P.cup_pull (mulP A) (subPair S₁ S₂ S₃ hS) (𝟭 C) (mulTo c₁ S₁ h₁).τ (mulTo c₂ S₂ h₂).τ
    (mulTo c₃ S₃ h₃).τ (mulTo c₁ S₁ h₁).nat (mulTo c₂ S₂ h₂).nat (mulTo c₃ S₃ h₃).nat
    (fun T (x y : A.obj T) => Subtype.ext (show c₃ • (x * y) = (c₁ • x) * (c₂ • y) by rw [hc, smul_mul_smul_comm])) h x y

theorem subMor_one {A : C ⥤ CommAlgCat.{0} R} {A' : C' ⥤ CommAlgCat.{0} R'} (m : CH.Mor (modF A) (modF A') σ)
    (hm : ∀ T : C', m.τ T (1 : A.obj (m.G.obj T)) = (1 : A'.obj T)) {c : R} {c' : R'} (hc : c = 1) (hc' : c' = 1)
    {S : SubF (modF A)} {S' : SubF (modF A')} (h h₁ h₂) :
    (subMor m S S' h).pull 0 ((mulTo c S h₁).pull 0 (CH.oneH A)) = (mulTo c' S' h₂).pull 0 (CH.oneH A') := by
  subst hc hc'
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
  change m.τ _ ((1 : R) • (1 : A.obj _)) = (1 : R') • (1 : A'.obj _)
  rw [one_smul, one_smul, hm]

end Gen

section Pd
variable {b b' : Base} {L : b.Fun} {L' : b'.Fun} {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {c : Λ →+* b.R} {c' : Λ' →+* b'.R}
  {σ : b.R →+* b'.R} (m : GlobalTheory.LogCris.Mor L L' σ) (σ₀ : Λ →+* Λ') (hσ : ∀ a, σ (c a) = c' (σ₀ a))

theorem pdOm_cup {r r' s : ℕ} (e : r + r' = s) {p q n : ℕ} (h : p + q = n) (x : H (B.pdS L c r).fn p) (y : H (B.pdS L c r').fn q) :
    (pdOm m σ₀ hσ s).pull n ((pdPair L c e).cup h x y) =
      (pdPair L' c' e).cup h ((pdOm m σ₀ hσ r).pull p x) ((pdOm m σ₀ hσ r').pull q y) :=
  subMor_cup (A := B.OA L c) (A' := B.OA L' c') (B.omMor m σ₀ hσ) (fun _ _ _ => rfl) _ _ _ _ _ h x y

theorem pdOm_one : (pdOm m σ₀ hσ 0).pull 0 (pdOne L c) = pdOne L' c' :=
  subMor_one (A := B.OA L c) (A' := B.OA L' c') (B.omMor m σ₀ hσ) (fun _ => rfl) rfl rfl _ _ _

end Pd

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def ttPair (P : PAlg l ⥤ Type) (n : ℕ) {r r' s : ℕ} (h : r + r' = s) : Pairing (TT P r n).fn (TT P r' n).fn (TT P s n).fn :=
  subPair (A := AcrEl P n) (TT P r n) (TT P r' n) (TT P s n) fun T x y hx hy =>
    mem_TT.2 (h ▸ dividedPowerFiltration_mul (B.DD false T.1.obj n) r r' (mem_TT.1 hx) (mem_TT.1 hy))

section F
variable {O : Type} [CommRing O] (F : B.Fn O) (κ : O →+* OC l)

theorem βF_cup (n : ℕ) {r r' s : ℕ} (e : r + r' = s) {p q k : ℕ} (h : p + q = k)
    (x : H (B.pdS (B.Lc F κ false n) ((base l).cris n) r).fn p) (y : H (B.pdS (B.Lc F κ false n) ((base l).cris n) r').fn q) :
    (βMorF F κ s n).pull k ((pdPair (B.Lc F κ false n) ((base l).cris n) e).cup h x y) =
      (ttPair (F.pt κ) n e).cup h ((βMorF F κ r n).pull p x) ((βMorF F κ r' n).pull q y) :=
  subMor_cup (A := B.OcA F κ false n) (A' := AcrEl (F.pt κ) n) (B.βMor F κ false n) (fun _ _ _ => rfl) _ _ _ _ _ h x y

theorem βF_one (ht : TFil l) (n : ℕ) : (βMorF F κ 0 n).pull 0 (pdOne (B.Lc F κ false n) ((base l).cris n)) =
    (tMor ht (F.pt κ) 0 n).pull 0 (CH.oneH (AcrEl (F.pt κ) n)) :=
  subMor_one (A := B.OcA F κ false n) (A' := AcrEl (F.pt κ) n) (B.βMor F κ false n) (fun _ => rfl) rfl (pow_zero _) _ _ _

end F

theorem tMor_cup (ht : TFil l) (P : PAlg l ⥤ Type) (n : ℕ) {r r' s : ℕ} (e : r + r' = s) {p q k : ℕ} (h : p + q = k)
    (x : MH P n p) (y : MH P n q) :
    (tMor ht P s n).pull k ((mulP (AcrEl P n)).cup h x y) =
      (ttPair P n e).cup h ((tMor ht P r n).pull p x) ((tMor ht P r' n).pull q y) :=
  mulTo_cup (A := AcrEl P n) (by rw [← e, pow_add]) _ _ _ _ h x y

theorem comp_cup {M : Model l K} {r r' s i j : ℕ} (h : r + r' = s) {x : Fam M r i} {y : Fam M r' j} (hx : Comp x) (hy : Comp y) :
    Comp (cupS h x y) := fun n =>
  (pdOm_cup (CrystallineSemistableComparison.SH.redM (B.schFn M.p) (okToOC l K) false n) (RingHom.id _) (B.red_cris _ n.le_succ) h rfl
    (x (n + 1)) (y (n + 1))).trans
    (congrArg₂ ((pdPair (M.L false n) ((base l).cris n) h).cup rfl) (hx n) (hy n))

theorem comp_one (M : Model l K) : Comp (oneS M) := fun n =>
  pdOm_one (CrystallineSemistableComparison.SH.redM (B.schFn M.p) (okToOC l K) false n) (RingHom.id _) (B.red_cris _ n.le_succ)

theorem cup_gen (ht : TFil l) {O : Type} [CommRing O] (F : B.Fn O) (κ : O →+* OC l) (n : ℕ) {r r' s i j : ℕ} (e : r + r' = s)
    (x : H (B.pdS (B.Lc F κ false n) ((base l).cris n) r).fn i) (y : H (B.pdS (B.Lc F κ false n) ((base l).cris n) r').fn j)
    (a : MH (F.pt κ) n i) (b : MH (F.pt κ) n j) (w : MH (F.pt κ) n (i + j))
    (hw : w = (mulP (AcrEl (F.pt κ) n)).cup rfl a b)
    (hx : (βMorF F κ r n).pull i x = (tMor ht (F.pt κ) r n).pull i a)
    (hy : (βMorF F κ r' n).pull j y = (tMor ht (F.pt κ) r' n).pull j b) :
    (βMorF F κ s n).pull (i + j) ((pdPair (B.Lc F κ false n) ((base l).cris n) e).cup rfl x y) =
      (tMor ht (F.pt κ) s n).pull (i + j) w :=
  ((βF_cup F κ n e rfl x y).trans (congrArg₂ ((ttPair (F.pt κ) n e).cup rfl) hx hy)).trans
    ((tMor_cup ht (F.pt κ) n e rfl a b).symm.trans (congrArg ((tMor ht (F.pt κ) s n).pull (i + j)) hw.symm))

variable (ht : TFil l) {e : E.EtFam l K}

theorem isLift_cupS_of_cupT (he : EtP e) : ∀ {M : Model l K} {r r' s i j : ℕ} (h : r + r' = s) {v : M.T i} {v' : M.T j} {w : M.T (i + j)}
    {x : Fam M r i} {x' : Fam M r' j}, M.CupT v v' w → IsLift ht e r v x → IsLift ht e r' v' x' → IsLift ht e s w (cupS h x x') :=
  fun {M _ _ _ i j} h {v v' w x x'} hw hx hx' => ⟨comp_cup h hx.1 hx'.1, fun n =>
    cup_gen ht (B.schFn M.p) (okToOC l K) n h (x n) (x' n) (e M n i (v.lev n)) (e M n j (v'.lev n)) (e M n (i + j) (w.lev n))
      ((congrArg (e M n (i + j)) (hw n)).trans (he.good.cup M n i j (v.lev n) (v'.lev n))) (hx.2 n) (hx'.2 n)⟩

theorem isLift_oneS_of_lev_eq_one (he : EtP e) : ∀ (M : Model l K) (v : M.T 0), (∀ k, v.lev k = GlobalTheory.EtC.one (l ^ k) M.spc) →
    IsLift ht e 0 v (oneS M) := fun M v hv => ⟨comp_one M, fun n =>
  (βF_one (B.schFn M.p) (okToOC l K) ht n).trans
    (congrArg ((tMor ht ((B.schFn M.p).pt (okToOC l K)) 0 n).pull 0) ((congrArg (e M n 0) (hv n)).trans (he.one M n)).symm)⟩

end CrystallineSemistableComparison.HT
end
end
