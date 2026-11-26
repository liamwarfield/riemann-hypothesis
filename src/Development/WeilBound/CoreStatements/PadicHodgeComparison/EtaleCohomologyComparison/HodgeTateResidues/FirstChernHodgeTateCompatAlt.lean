module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernClassInJAlt
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.KProps
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.EpsTA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TaylorOfLocalFrame
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.TowerSmulZero
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.FirstChernHodgeTateCompatAlt
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6

namespace CrystallineSemistableComparison.HT

open PAlg Pb

variable (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))

structure RhoEx : Prop where
  ex : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K), M.Sm → ∀ r j : ℕ, r < m → ∀ x : Y.Fam M r j, CB.Comp x → ∃! w, L.Rho x w
  add : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) (r j : ℕ) (x y : Y.Fam M r j) w w', L.Rho x w → L.Rho y w' → L.Rho (x + y) (w + w')
  smul : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) (r j : ℕ) (c : Y.Λ) (x : Y.Fam M r j) w, L.Rho x w →
    L.Rho (c • x) (L.ι (L.lam c) • w)

def CoEx : Prop := ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K), M.Sm → ∀ r j : ℕ, r < m →
  Spans L.γB M.q (L.QB M) L.tB_mem r j ∧ ∃ co, IsCo L.γB M.q (L.QB M) L.θ L.tB_mem r j co

def HomRho : Prop := ∀ {Y : CB l K} {m m' : ℕ} {L : Lv Y m} {L' : Lv Y m'} {sΛ : Y.Λ →+* Y.Λ}
  {sn : ∀ n, Y.R n →+* Y.R n} {sC : ℂ_[l] →+* ℂ_[l]} {c : ℂ_[l]} (h : LHom L L' sΛ sn sC c) {M N : Model l K}
  (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (mm : ∀ n, GlobalTheory.LogCris.Mor (Y.L N n) (Y.L M n) (sn n)),
  (∀ (n : ℕ) (B₀ : CommRingCat.{0}) (y : (Y.L M n).Pt.obj B₀), ((mm n).pt.app B₀ y).1.2 = (show Spec B₀ ⟶ M.X from y.1.2) ≫ u) →
  ∀ (r j : ℕ) (x : Y.Fam N r j) (w : HG (L.QB N) r j), L.Rho x w →
    L'.Rho (M := M) (fun n => (pdOm (mm n) sΛ (h.cris n) r).pull j (x n)) (h.fW u hu r j w)

def HomMu : Prop := ∀ {Y : CB l K} {m m' : ℕ} {L : Lv Y m} {L' : Lv Y m'} {sΛ : Y.Λ →+* Y.Λ}
  {sn : ∀ n, Y.R n →+* Y.R n} {sC : ℂ_[l] →+* ℂ_[l]} {c : ℂ_[l]} (h : LHom L L' sΛ sn sC c) {M N : Model l K}
  (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (a r j : ℕ) (y : Hdg N.q a j),
    h.fW u hu r j (L.μ N a r j y) = h.cB ^ (r - a) • L'.μ M a r j (pullH (Model.genMap u hu) (Model.genMap_q u hu) a j y)

structure MulRho : Prop where
  sh : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) {r r' j : ℕ} (k : ℕ) (h : r + k = r') (x : Y.Fam M r j) w, L.Rho x w →
    L.Rho (CB.shS k h x) (shG (L.QB M) L.tB_mem k h j w)
  sh_μ : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) {r r' j : ℕ} (k : ℕ) (h : r + k = r') (a : ℕ), a ≤ r → ∀ y : Hdg M.q a j,
    shG (L.QB M) L.tB_mem k h j (L.μ M a r j y) = L.μ M a r' j y
  cup : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) {r r' s i j : ℕ} (h : r + r' = s) (x : Y.Fam M r i) (y : Y.Fam M r' j) w w',
    L.Rho x w → L.Rho y w' → L.Rho (CB.cupS h x y) (cupG (L.QB M) h w w')
  cup_μ : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) {r r' s i j a a' c : ℕ} (h : r + r' = s) (ha : a + a' = c), a ≤ r → a' ≤ r' →
    ∀ (y : Hdg M.q a i) (y' : Hdg M.q a' j),
    cupG (L.QB M) h (L.μ M a r i y) (L.μ M a' r' j y') = L.μ M c s (i + j) (cupH M.q ha rfl y y')
  one : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K), L.Rho (Y.oneS M) (L.μ M 0 0 0 (oneH M.q))

def FirstChernHodgeTateCompat : Prop := ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K), 1 < m → ∀ (D : E.LineData M.X), sSup (𝒱D D) = ⊤ →
  ∀ (x : Y.Fam M 1 2) (c : Hdg M.q 1 2), CB.IsFirstChernClassInFamily D x → IsDlogFirstChernClass M.q (genD D) c → L.Rho x (L.μ M 1 1 2 c)

end CrystallineSemistableComparison.HT
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.H1LiftNaturality
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.MulSubMulTo
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6

universe w w' v u v' u'

namespace CrystallineSemistableComparison.HT

open PAlg

section Gen
variable {R R' : Type} [CommRing R] [CommRing R'] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'} {σ : R →+* R'}

theorem sub_mulTo (m : CH.Mor F F' σ) (S : CH.SubF F) (S' : CH.SubF F') (h) (c : R) (hc) (c' a : R') (hc') (e : σ c = a * c')
    (j : ℕ) (y : CH.H F j) :
    (subMor m S S' h).pull j ((mulTo c S hc).pull j y) = a • (mulTo c' S' hc').pull j (m.pull j y) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
  change m.τ _ (c • z.1 (s ⋙ m.G)) = a • c' • m.τ _ (z.1 (s ⋙ m.G))
  rw [LinearMap.map_smulₛₗ, e, mul_smul]

theorem sub_mulSub (m : CH.Mor F F' σ) (S₁ S₂ : CH.SubF F) (S₁' S₂' : CH.SubF F') (h₁ h₂) (c : R) (hc) (c' : R') (hc') (e : σ c = c')
    (j : ℕ) (y : CH.H S₁.fn j) :
    (subMor m S₂ S₂' h₂).pull j ((mulSub c S₁ S₂ hc).pull j y) = (mulSub c' S₁' S₂' hc').pull j ((subMor m S₁ S₁' h₁).pull j y) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
  change m.τ _ (c • (show S₁.S _ from z.1 (s ⋙ m.G)).1) = c' • m.τ _ (show S₁.S _ from z.1 (s ⋙ m.G)).1
  rw [LinearMap.map_smulₛₗ, e]

theorem mulSub_mulTo (S S' : CH.SubF F) (c c' c'' : R) (h h' h'') (e : c' * c = c'') (j : ℕ) (y : CH.H F j) :
    (mulSub c' S S' h').pull j ((mulTo c S h).pull j y) = (mulTo c'' S' h'').pull j y := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
  change c' • c • z.1 s = c'' • z.1 s
  rw [smul_smul, e]

theorem sub_square {C₁ C₂ C₃ C₄ : Type 1} [Category.{0} C₁] [Category.{0} C₂] [Category.{0} C₃] [Category.{0} C₄]
    {F₁ : C₁ ⥤ ModuleCat.{0} R} {F₂ : C₂ ⥤ ModuleCat.{0} R} {F₃ : C₃ ⥤ ModuleCat.{0} R} {F₄ : C₄ ⥤ ModuleCat.{0} R}
    {σ₁ σ₂ σ₃ σ₄ : R →+* R} (τ : R →+* R) [RingHomCompTriple σ₁ σ₂ τ] [RingHomCompTriple σ₃ σ₄ τ]
    (m : CH.Mor F₁ F₂ σ₁) (b : CH.Mor F₂ F₃ σ₂) (b' : CH.Mor F₁ F₄ σ₃) (q : CH.Mor F₄ F₃ σ₄)
    (S₁ : CH.SubF F₁) (S₂ : CH.SubF F₂) (S₃ : CH.SubF F₃) (S₄ : CH.SubF F₄) (hm hb hb' hq)
    (η : b.G ⋙ m.G ⟶ q.G ⋙ b'.G)
    (hτ : ∀ T x, q.τ T (b'.τ (q.G.obj T) ((F₁.map (η.app T)).hom x)) = b.τ T (m.τ (b.G.obj T) x)) (n : ℕ) (x : CH.H S₁.fn n) :
    (subMor b S₂ S₃ hb).pull n ((subMor m S₁ S₂ hm).pull n x) = (subMor q S₄ S₃ hq).pull n ((subMor b' S₁ S₄ hb').pull n x) := by
  rw [pull_pull τ, pull_pull τ]
  exact CrystallineSemistableComparison.P.prism ((subMor m S₁ S₂ hm).comp (σ'' := τ) (subMor b S₂ S₃ hb))
    ((subMor b' S₁ S₄ hb').comp (σ'' := τ) (subMor q S₄ S₃ hq)) η (fun T x => Subtype.ext (hτ T x.1)) n x

end Gen

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section P
variable (ht : TFil l) (P : PAlg l ⥤ Type)

def shT {r r' : ℕ} (k : ℕ) (h : r + k = r') (n : ℕ) : CH.Mor (TT P r n).fn (TT P r' n).fn (RingHom.id _) :=
  mulSub (tA l ^ k) (TT P r n) (TT P r' n) fun T (x : T.1.obj.Acr n) hx => mem_TT.2 (by
    have := dividedPowerFiltration_pow_mul (B.DD false T.1.obj n) (ht T.1.obj n) h (mem_TT.1 hx)
    rw [← map_pow] at this
    exact this)

theorem shT_tMor {r r' : ℕ} (k : ℕ) (h : r + k = r') (n j : ℕ) (y : MH P n j) :
    (shT ht P k h n).pull j ((tMor ht P r n).pull j y) = (tMor ht P r' n).pull j y :=
  mulSub_mulTo (TT P r n) (TT P r' n) (tA l ^ r) (tA l ^ k) (tA l ^ r') _ _ _ (by rw [← pow_add, add_comm, h]) j y

variable {P}

def galT (σ : Gal(PadicAlgCl l/K)) (a : P ⟶ twF σ ⋙ P) (r n : ℕ) : CH.Mor (TT P r n).fn (TT P r n).fn (ACris.galCris σ) :=
  subMor (galMor σ a n) (TT P r n) (TT P r n) fun T x hx =>
    mem_TT.2 (Pb.dividedPowerFiltration_map (GlobalTheory.CompanionTheory.BetaGal.dd_twAcr false σ T.1.obj n) r ((mem_TT (T := (elTw σ a).obj T)).1 hx))

theorem galT_tMor (σ : Gal(PadicAlgCl l/K)) (a : P ⟶ twF σ ⋙ P) (r n j : ℕ) (y : MH P n j) :
    (galT σ a r n).pull j ((tMor ht P r n).pull j y) = χA σ ^ r • (tMor ht P r n).pull j ((galMor σ a n).pull j y) :=
  sub_mulTo (galMor σ a n) (TT P r n) (TT P r n) _ (tA l ^ r) _ (tA l ^ r) (χA σ ^ r) _
    (by rw [map_pow, galCris_tA, mul_pow]) j y

def pullT' {P' : PAlg l ⥤ Type} (u : P ⟶ P') (r n : ℕ) : CH.Mor (TT P' r n).fn (TT P r n).fn (RingHom.id _) :=
  subMor (pullMor u n) (TT P' r n) (TT P r n) fun T x hx => mem_TT.2 ((mem_TT (T := (elMap u).obj T)).1 hx)

theorem pullT_tMor {P' : PAlg l ⥤ Type} (u : P ⟶ P') (r n j : ℕ) (y : MH P' n j) :
    (pullT' u r n).pull j ((tMor ht P' r n).pull j y) = (tMor ht P r n).pull j ((pullMor u n).pull j y) :=
  (sub_mulTo (pullMor u n) (TT P' r n) (TT P r n) _ (tA l ^ r) _ (tA l ^ r) 1 _ (one_mul _).symm j y).trans (one_smul _ _)

end P

section F
variable {O : Type} [CommRing O] (F : B.Fn O) (κ : O →+* OC l)

theorem β_sh (ht : TFil l) {r r' : ℕ} (k : ℕ) (h : r + k = r') (n j : ℕ)
    (x : CH.H (B.pdS (B.Lc F κ false n) ((base l).cris n) r).fn j) :
    (βMorF F κ r' n).pull j ((pdSh (B.Lc F κ false n) ((base l).cris n) (ht (base l) n) k h).pull j x) =
      (shT ht (F.pt κ) k h n).pull j ((βMorF F κ r n).pull j x) :=
  sub_mulSub (B.βMor F κ false n) (B.pdS (B.Lc F κ false n) ((base l).cris n) r) (B.pdS (B.Lc F κ false n) ((base l).cris n) r')
    (TT (F.pt κ) r n) (TT (F.pt κ) r' n) _ _ (tA l ^ k) _ (tA l ^ k) _ rfl j x

theorem β_galF (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (r n j : ℕ)
    (x : CH.H (B.pdS (B.Lc F κ false n) ((base l).cris n) r).fn j) :
    (βMorF F κ r n).pull j ((pdOm (CrystallineSemistableComparison.SH.galM F κ σ hσ false n) (ACris.galCris σ) (galBase_cris σ n) r).pull j x) =
      (galT σ (B.ptTw F κ σ hσ) r n).pull j ((βMorF F κ r n).pull j x) := by
  have h1 := pull_pull (ACris.galCris σ) (pdOm (CrystallineSemistableComparison.SH.galM F κ σ hσ false n) (ACris.galCris σ) (galBase_cris σ n) r)
    (βMorF F κ r n) j x
  have h2 := pull_pull (ACris.galCris σ) (βMorF F κ r n) (galT σ (B.ptTw F κ σ hσ) r n) j x
  refine h1.trans (Eq.trans ?_ h2.symm)
  exact (pd_pull_eq ((βMorF F κ r n).comp (σ'' := ACris.galCris σ) (galT σ (B.ptTw F κ σ hσ) r n))
    ((pdOm (CrystallineSemistableComparison.SH.galM F κ σ hσ false n) (ACris.galCris σ) (galBase_cris σ n) r).comp (σ'' := ACris.galCris σ) (βMorF F κ r n))
    (GlobalTheory.CompanionTheory.BetaGal.etaGal F κ σ hσ false n) (fun f x => twAcr_mapAcr σ f.1.hom n x) (fun _ _ _ _ => rfl) j x).symm

variable {F} {F' : B.Fn O}

theorem β_pullF (u : B.Fn.Map F F') (r n j : ℕ) (x : CH.H (B.pdS (B.Lc F' κ false n) ((base l).cris n) r).fn j) :
    (βMorF F κ r n).pull j ((pdOm (CrystallineSemistableComparison.SH.pullM κ u false n) (RingHom.id _) (CrystallineSemistableComparison.SH.idc _) r).pull j x) =
      (pullT' (u.pt κ) r n).pull j ((βMorF F' κ r n).pull j x) :=
  sub_square (RingHom.id _) (B.pullMorC κ u false n) (B.βMor F κ false n) (B.βMor F' κ false n) (pullMor (u.pt κ) n)
    (B.pdS (B.Lc F' κ false n) ((base l).cris n) r) (B.pdS (B.Lc F κ false n) ((base l).cris n) r) (TT (F.pt κ) r n) (TT (F'.pt κ) r n)
    _ _ _ _ (GlobalTheory.CompanionTheory.BetaPull.cmpNat κ u false n) (fun _ _ => rfl) j x

end F

end CrystallineSemistableComparison.HT
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6

namespace CrystallineSemistableComparison.HT

open PAlg

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem lin_add {R : Type} [CommRing R] {A B C : Type 1} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module R A] [Module R B]
    [Module R C] (f : A →ₗ[R] C) (g : B →ₗ[R] C) {x x' : A} {y y' y'' : B} (h : f x = g y) (h' : f x' = g y') (e : y'' = y + y') :
    f (x + x') = g y'' := by rw [e, map_add (f := _), map_add (f := _), h, h']

theorem lin_smul {R : Type} [CommRing R] {A B C : Type 1} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module R A] [Module R B]
    [Module R C] (f : A →ₗ[R] C) (g : B →ₗ[R] C) (c : R) {x : A} {y y' : B} (h : f x = g y) (e : y' = c • y) :
    f (c • x) = g y' := by rw [e, map_smul, map_smul, h]

theorem kill_val (A : PAlg l) (n : ℕ) (x : A.Acr n) : A.cris n ((l : Acris l) ^ n) * x = 0 := by
  rw [map_pow, map_natCast, A.pow_l_acr n, zero_mul]

theorem kill_MH (P : PAlg l ⥤ Type) (n j : ℕ) (x : MH P n j) : ((l : Acris l) ^ n) • x = 0 :=
  GlueE.H_smul_eq_zero _ _ (fun T y => kill_val T.1.obj n y) j x

theorem e_smul (e : E.EtFam l K) (M : Model l K) (j n : ℕ) (z : ℤ_[l]) (v : M.T j) :
    e M n j ((z • v).lev n) = zA l z • e M n j (v.lev n) :=
  ((congrArg (e M n j) (GlobalTheory.EtC.HtL.smul_eq l n n le_rfl M.spc j 0 z (v.1 n))).trans (map_nsmul (e M n j) _ _)).trans
    (GlueE.padic_smul (zA l) n _ (kill_MH M.P n j _) z).symm

theorem zA_chi (σ : K.fixingSubgroup) (r : ℕ) :
    zA l ((DeRhamTwist.Twist.chi0 l σ.1 ^ r : ℤ_[l]ˣ) : ℤ_[l]) = χA (IntermediateField.fixingSubgroupEquiv K σ) ^ r := by
  rw [Units.val_pow_eq_pow_val, map_pow]
  rfl

variable (ht : TFil l) {e : E.EtFam l K} (he : EtP e)
include he

theorem h1_lift_add : ∀ {M : Model l K} {r j : ℕ} {v v' : M.T j} {x x' : Fam M r j},
    IsLift ht e r v x → IsLift ht e r v' x' → IsLift ht e r (v + v') (x + x') :=
  fun {M r j v v' x x'} h h' => ⟨comp_add h.1 h'.1, fun n =>
    lin_add ((βMorF (B.schFn M.p) (okToOC l K) r n).pull j) ((tMor ht ((B.schFn M.p).pt (okToOC l K)) r n).pull j) (h.2 n) (h'.2 n)
      (map_add (e M n j) (v.lev n) (v'.lev n))⟩

theorem h1_lift_smul : ∀ {M : Model l K} {r j : ℕ} {v : M.T j} {x : Fam M r j} (z : ℤ_[l]),
    IsLift ht e r v x → IsLift ht e r (z • v) (zA l z • x) :=
  fun {M r j v x} z h => ⟨comp_smul _ h.1, fun n =>
    lin_smul ((βMorF (B.schFn M.p) (okToOC l K) r n).pull j) ((tMor ht ((B.schFn M.p).pt (okToOC l K)) r n).pull j) (zA l z) (h.2 n)
      (e_smul e M j n z v)⟩

theorem h1_lift_shift : ∀ {M : Model l K} {r r' j : ℕ} {v : M.T j} {x : Fam M r j} (k : ℕ) (h : r + k = r'),
    IsLift ht e r v x → IsLift ht e r' v (shS ht k h x) :=
  fun {M r r' j v x} k h hx => ⟨comp_sh ht k h hx.1, fun n =>
    (β_sh (B.schFn M.p) (okToOC l K) ht k h n j (x n)).trans
      ((congrArg ((shT ht ((B.schFn M.p).pt (okToOC l K)) k h n).pull j) (hx.2 n)).trans (shT_tMor ht _ k h n j _))⟩

theorem h1_lift_galois : ∀ {M : Model l K} {r j : ℕ} {v : M.T j} {x : Fam M r j} (σ : K.fixingSubgroup), IsLift ht e r v x →
    IsLift ht e r (DeRhamTwist.Twist.chi0 l σ.1 ^ r • M.actT j σ v) (galS σ x) :=
  fun {M r j v x} σ hx => ⟨comp_gal σ hx.1, fun n =>
    (β_galF (B.schFn M.p) (okToOC l K) (IntermediateField.fixingSubgroupEquiv K σ) (galOC_okToOC _) r n j (x n)).trans
      ((congrArg ((galT (IntermediateField.fixingSubgroupEquiv K σ) (B.ptTw (B.schFn M.p) (okToOC l K)
          (IntermediateField.fixingSubgroupEquiv K σ) (galOC_okToOC _)) r n).pull j) (hx.2 n)).trans
        ((galT_tMor ht _ _ r n j _).trans
          ((map_smul ((tMor ht ((B.schFn M.p).pt (okToOC l K)) r n).pull j) _ _).symm.trans
            (congrArg ((tMor ht ((B.schFn M.p).pt (okToOC l K)) r n).pull j)
              ((e_smul e M j n ((DeRhamTwist.Twist.chi0 l σ.1 ^ r : ℤ_[l]ˣ) : ℤ_[l]) (M.actT j σ v)).trans
                (congrArg₂ (· • ·) (zA_chi σ r)
                  (he.good.equi M n j (IntermediateField.fixingSubgroupEquiv K σ) (v.lev n)))).symm))))⟩

theorem h1_lift_naturality : ∀ {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) {r j : ℕ} {v : N.T j} {x : Fam N r j},
    IsLift ht e r v x → IsLift ht e r (Model.pullT u hu j v) (pullS u hu x) :=
  fun {M N} u hu {r j v x} hx => ⟨comp_pull u hu hx.1, fun n =>
    (β_pullF (okToOC l K) (B.schMap u hu) r n j (x n)).trans
      ((congrArg ((pullT' ((B.schMap u hu).pt (okToOC l K)) r n).pull j) (hx.2 n)).trans
        ((pullT_tMor ht _ r n j _).trans
          (congrArg ((tMor ht ((B.schFn M.p).pt (okToOC l K)) r n).pull j) (he.good.nat M N u hu n j (v.lev n)).symm)))⟩

end CrystallineSemistableComparison.HT
end
end
