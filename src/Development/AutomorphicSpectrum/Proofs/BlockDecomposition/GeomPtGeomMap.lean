module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeomPtGeomMap
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.FNatProof

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem geomPt_geomMap {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (A : PAlg l) (y : M.P.obj A) :
    geomPt M A y ≫ GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu) =
      geomPt N A ((pxMap (okToOC l K) u hu).app A y) := by
  refine gb_ext N ?_ ?_
  · have e1 : GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu) ≫
        pullback.fst _ _ ≫ pullback.fst _ _ = (pullback.fst _ _ ≫ pullback.fst _ _) ≫ u := by
      rw [GlobalTheory.Et.geomMap, pullback.lift_fst_assoc, Category.assoc, Model.genMap, pullback.lift_fst, Category.assoc]
    rw [Category.assoc, e1, geomPt_fst, ← Category.assoc, geomPt_fst, Category.assoc]
    rfl
  · rw [Category.assoc, GlobalTheory.Et.geomMap, pullback.lift_snd, geomPt_snd, geomPt_snd]

def lcPull (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) :
    Mor (probe H r (𝟭 (El N.P) ⋙ CategoryOfElements.π _) n).L (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).L
      (RingHom.id ℤ) where
  G := elMap (pxMap (okToOC l K) u hu)
  τ _ := LinearMap.id
  nat _ _ := rfl

def lcM (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) :
    Mor (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).L (modF (AcrEl M.P n)) (Int.castRingHom (Acris l)) :=
  lcMor hN H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n

theorem cls_surj {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (n : ℕ) (h : CH.H F n) :
    ∃ (z : Cn F n) (hz : d F n z = 0), (cx F).cls z hz = h := by
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  exact ⟨z, hz, rfl⟩

theorem pull_square {R₁ R₂ R₃ R₄ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] [CommRing R₄]
    {C₁ C₂ C₃ C₄ : Type 1} [Category.{0} C₁] [Category.{0} C₂] [Category.{0} C₃] [Category.{0} C₄]
    {F₁ : C₁ ⥤ ModuleCat.{0} R₁} {F₂ : C₂ ⥤ ModuleCat.{0} R₂} {F₃ : C₃ ⥤ ModuleCat.{0} R₃} {F₄ : C₄ ⥤ ModuleCat.{0} R₄}
    {σ₁₂ : R₁ →+* R₂} {σ₂₄ : R₂ →+* R₄} {σ₁₃ : R₁ →+* R₃} {σ₃₄ : R₃ →+* R₄}
    (a : Mor F₁ F₂ σ₁₂) (b : Mor F₂ F₄ σ₂₄) (c : Mor F₁ F₃ σ₁₃) (e : Mor F₃ F₄ σ₃₄) (j : ℕ)
    (h : ∀ z : Cn F₁ j, b.pullC j (a.pullC j z) = e.pullC j (c.pullC j z)) (x : CH.H F₁ j) :
    b.pull j (a.pull j x) = e.pull j (c.pull j x) := by
  obtain ⟨z, hz, rfl⟩ := cls_surj F₁ j x
  change (cx F₄).cls (b.pullC j (a.pullC j z)) _ = (cx F₄).cls (e.pullC j (c.pullC j z)) _
  simp only [h]

theorem square (hN : LcNat) (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n j : ℕ)
    (h : CH.H (probe H r (𝟭 (El N.P) ⋙ CategoryOfElements.π _) n).L j) :
    (lcM hN H r M n).pull j ((lcPull H r u hu n).pull j h) =
      Model.pullMH u hu n j ((lcM hN H r N n).pull j h) :=
  pull_square (lcPull H r u hu n) (lcM hN H r M n) (lcM hN H r N n) (pullMor (pxMap (okToOC l K) u hu) n) j
    (fun z => funext fun s => rfl) h

theorem lcRes_id (q : ℕ) {U : Scheme.{0}} (f : LocallyConstant U (ZMod q)) : lcRes q (𝟙 U) f = f := by
  ext v
  rfl

def gId (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) (c : El M.P) :
    (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).U c ⟶
      (probe H r (𝟭 (El N.P) ⋙ CategoryOfElements.π _) n).U ((lcPull H r u hu n).G.obj c) :=
  𝟙 (Spec (CommRingCat.of c.1.obj.Ug))

theorem gId_nat (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ)
    {c c' : El M.P} (φ : c ⟶ c') :
    gId H r u hu n c' ≫ ((probe H r (𝟭 (El N.P) ⋙ CategoryOfElements.π _) n).S.map ((lcPull H r u hu n).G.map φ)).unop =
      ((probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).S.map φ).unop ≫ gId H r u hu n c :=
  (Category.id_comp _).trans (Category.comp_id _).symm

theorem gId_lc (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) (c : El M.P)
    (f : LocallyConstant ((probe H r (𝟭 (El N.P) ⋙ CategoryOfElements.π _) n).U ((lcPull H r u hu n).G.obj c)) (ZMod (l ^ n))) :
    (lcPull H r u hu n).τ c f = lcRes (l ^ n) (gId H r u hu n c) f :=
  (lcRes_id _ f).symm

theorem gId_pts (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) (c : El M.P) :
    (pts H r M (𝟭 _) n).y c ≫ GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu) =
      gId H r u hu n c ≫ (pts H r N (𝟭 _) n).y ((lcPull H r u hu n).G.obj c) :=
  (geomPt_geomMap u hu c.1.obj c.2).trans (Category.id_comp _).symm

theorem key (hE : CrystallineSemistableComparison.E.EtNat) (hG : InGen) (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X)
    (hu : u ≫ N.p = M.p) (n : ℕ) [NeZero (l ^ n)] (j : ℕ) (x : Ht (l ^ n) (sch.obj (gb N)) j 0) :
    (lcPull H r u hu n).pull j ((pts H r N (𝟭 _) n).et 0 j x) =
      (pts H r M (𝟭 _) n).et 0 j
        (pull _ (sch.map (GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu))) _ j x) :=
  hE hG (l ^ n) (El N.P) (El M.P) (probe H r (𝟭 (El N.P) ⋙ CategoryOfElements.π _) n)
    (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n) (gb N) (gb M) (pts H r N (𝟭 _) n) (pts H r M (𝟭 _) n)
    (GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu)) (lcPull H r u hu n)
    (gId H r u hu n) (gId_nat H r u hu n) (gId_lc H r u hu n) (gId_pts H r u hu n) 0 (Or.inl rfl) j x

theorem nat_step (hE : CrystallineSemistableComparison.E.EtNat) (hG : InGen) (hN : LcNat) (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X)
    (hu : u ≫ N.p = M.p) (n : ℕ) [NeZero (l ^ n)] (j : ℕ) (x : Ht (l ^ n) (sch.obj (gb N)) j 0) :
    eM hN H r M n 0 j
        (pull _ (sch.map (GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu))) _ j x) =
      Model.pullMH u hu n j (eM hN H r N n 0 j x) :=
  (congrArg ((lcM hN H r M n).pull j) (key hE hG H r u hu n j x).symm).trans (square hN H r u hu n j _)

theorem fNat : CrystallineSemistableComparison.E.EtNat → CrystallineSemistableComparison.E.FNat := by
  intro hE E hN l _ H r K M N u hu n j x
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  exact nat_step hE E.gen hN H r u hu n j x

end GlobalTheory.CompanionTheory.FNatProof

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowDivPowSucc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtReduction

section Abstract
universe w u v
variable {R R₁ R₂ R₃ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing R₃] {C : Type u} [Category.{v} C]

theorem pull_sq {F : C ⥤ ModuleCat.{w} R} {F₁ : C ⥤ ModuleCat.{w} R₁} {F₂ : C ⥤ ModuleCat.{w} R₂} {F₃ : C ⥤ ModuleCat.{w} R₃}
    {σ₁ : R →+* R₁} {σ₂ : R₁ →+* R₃} {σ₃ : R →+* R₂} {σ₄ : R₂ →+* R₃}
    (a : Mor F F₁ σ₁) (b : Mor F₁ F₃ σ₂) (c : Mor F F₂ σ₃) (e : Mor F₂ F₃ σ₄) (n : ℕ)
    (h : ∀ z, b.pullC n (a.pullC n z) = e.pullC n (c.pullC n z)) (x : CH.H F n) :
    b.pull n (a.pull n x) = e.pull n (c.pull n x) := by
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h z))

end Abstract

variable {l : ℕ} [Fact l.Prime]

def lcCast {U : Type*} [TopologicalSpace U] {Q q : ℕ} (h : q ∣ Q) :
    LocallyConstant U (ZMod Q) →+ LocallyConstant U (ZMod q) where
  toFun f := f.map (ZMod.castHom h (ZMod q))
  map_zero' := by ext v; simp
  map_add' f g := by
    ext v
    exact map_add (ZMod.castHom h (ZMod q)) (f v) (g v)

theorem pow_div_pow_succ (n : ℕ) : l ^ (n + 1) / l ^ n = l := by
  have h : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  rw [pow_succ', Nat.mul_div_cancel _ h]

theorem rho_pow (r : Roots l) (n : ℕ) : (r.ρ n).1 = (r.ρ (n + 1)).1 ^ l := by
  apply (clToC l).injective
  rw [map_pow, r.hρ, r.hρ, rootSeq_succ_pow]

theorem lcRes_id {U : Scheme.{0}} (q : ℕ) (f : LocallyConstant U (ZMod q)) : lcRes q (𝟙 U) f = f := by
  ext v
  simp [lcRes]

theorem zeta_red (r : Roots l) (A : PAlg l) (n : ℕ) :
    (r.zeta A n).1 = (primRes (𝟙 (SU A)) (r.zeta A (n + 1))).1 ^ (l ^ (n + 1) / l ^ n) := by
  rw [pow_div_pow_succ]
  change ((toΓ A.Ug).comp (kb A)) (r.ρ n).1 = (𝟙 (SU A) : SU A ⟶ SU A).appTop.hom (((toΓ A.Ug).comp (kb A)) (r.ρ (n + 1)).1) ^ l
  rw [rho_pow r n, map_pow]
  simp

theorem lc_red (hN : LcNat) (H : RIn l) (A : Test l) (n : ℕ) (f : LocallyConstant (SU A.obj) (ZMod (l ^ (n + 1)))) :
    A.obj.red n.le_succ (lcA A.obj (n + 1) f) = lcA A.obj n (lcCast (pow_dvd_pow l n.le_succ) f) :=
  (hN l H _ A.property n).2 f

variable {C : Type 1} [Category.{0} C]

def redMor (H : RIn l) (r : Roots l) (G : C ⥤ Test l) (n : ℕ) :
    Mor (probe H r G (n + 1)).L (probe H r G n).L (RingHom.id ℤ) where
  G := 𝟭 C
  τ c :=
    { toFun := lcCast (pow_dvd_pow l n.le_succ)
      map_add' := map_add _
      map_smul' := fun z x => (map_zsmul (lcCast (U := (probe H r G n).U c) (pow_dvd_pow l n.le_succ)) z x).trans rfl }
  nat φ x := rfl

end GlobalTheory.CompanionTheory.EtReduction

namespace GlobalTheory.CompanionTheory.EtReduction

variable {l : ℕ} [Fact l.Prime]

theorem red_lc_sq (hN : LcNat) (H : RIn l) (r : Roots l) (P : PAlg l ⥤ Type) (n j : ℕ)
    (c : CH.H (probe H r (𝟭 (El P) ⋙ CategoryOfElements.π _) (n + 1)).L j) :
    (MSys P j).r n ((lcMor hN H r (𝟭 (El P) ⋙ CategoryOfElements.π _) (n + 1)).pull j c) =
      (lcMor hN H r (𝟭 (El P) ⋙ CategoryOfElements.π _) n).pull j
        ((redMor H r (𝟭 (El P) ⋙ CategoryOfElements.π _) n).pull j c) :=
  pull_sq (F := (probe H r (𝟭 (El P) ⋙ CategoryOfElements.π _) (n + 1)).L)
    (F₁ := CH.modF (AcrEl P (n + 1))) (F₂ := (probe H r (𝟭 (El P) ⋙ CategoryOfElements.π _) n).L)
    (F₃ := CH.modF (AcrEl P n))
    (lcMor hN H r (𝟭 (El P) ⋙ CategoryOfElements.π _) (n + 1)) (Mor.ofNatTrans (redEl P n.le_succ))
    (redMor H r (𝟭 (El P) ⋙ CategoryOfElements.π _) n) (lcMor hN H r (𝟭 (El P) ⋙ CategoryOfElements.π _) n) j
    (fun z => funext fun s => lc_red hN H (s.obj (Fin.last j)).1 n (z s)) c

end GlobalTheory.CompanionTheory.EtReduction

namespace GlobalTheory.CompanionTheory.EtReduction

theorem fred_of_etRed : EtRed → FRed := by
  intro hE E hN l _ H r K M n j x
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have key := hE E.gen E.red E.op (l ^ (n + 1)) (l ^ n) (pow_dvd_pow l n.le_succ) (El M.P) (El M.P)
    (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) (n + 1)) (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n) (gb M)
    (pts H r M (𝟭 _) (n + 1)) (pts H r M (𝟭 _) n) (redMor H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n)
    (fun c => 𝟙 _) (fun φ => (Category.id_comp _).trans (Category.comp_id _).symm)
    (fun c f => (lcRes_id _ _).symm)
    (fun c => (Category.id_comp _).symm)
    (fun c => zeta_red r _ n) 0 j x
  exact (red_lc_sq hN H r M.P n j _).trans (congrArg _ key)

end GlobalTheory.CompanionTheory.EtReduction
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullPullOfPullC
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.FEquiProof

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem pull_pull_of_pullC {R₀ R₁ R₂ R₃ : Type} [CommRing R₀] [CommRing R₁] [CommRing R₂] [CommRing R₃]
    {C₀ C₁ C₂ C₃ : Type 1} [Category.{0} C₀] [Category.{0} C₁] [Category.{0} C₂] [Category.{0} C₃]
    {F₀ : C₀ ⥤ ModuleCat.{0} R₀} {F₁ : C₁ ⥤ ModuleCat.{0} R₁} {F₂ : C₂ ⥤ ModuleCat.{0} R₂} {F₃ : C₃ ⥤ ModuleCat.{0} R₃}
    {a : R₀ →+* R₁} {b : R₁ →+* R₃} {c : R₀ →+* R₂} {e : R₂ →+* R₃}
    (m₁ : Mor F₀ F₁ a) (m₂ : Mor F₁ F₃ b) (m₃ : Mor F₀ F₂ c) (m₄ : Mor F₂ F₃ e) (j : ℕ)
    (h : ∀ z : Cn F₀ j, m₂.pullC j (m₁.pullC j z) = m₄.pullC j (m₃.pullC j z)) (x : H F₀ j) :
    m₂.pull j (m₁.pull j x) = m₄.pull j (m₃.pull j x) := by
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg (Submodule.Quotient.mk (p := ((cx F₃).B j).submoduleOf ((cx F₃).Z j))) (Subtype.ext (h z))

theorem twUg_sharp (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (e : (PAlg.tw σ A).A) :
    twUg σ A (algebraMap (PAlg.tw σ A).U (PAlg.tw σ A).Ug ((PAlg.tw σ A).sharp e)) =
      algebraMap A.U A.Ug (A.sharp (PAlg.twId σ A e)) := by
  rw [twUg_algebraMap]
  refine congrArg (algebraMap A.U A.Ug) ?_
  change PAlg.twU σ A ((PAlg.tw σ A).th (WittVector.teichmuller l e)) = A.th (WittVector.teichmuller l (PAlg.twId σ A e))
  rw [PAlg.twU_th, WittVector.map_teichmuller]

theorem twAcr_lcA (hN : LcNat) (H : RIn l) (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (hA : A.IsTest) (n : ℕ)
    (f : LocallyConstant (SU (PAlg.tw σ A)) (ZMod (l ^ n))) :
    PAlg.twAcr σ A n (lcA (PAlg.tw σ A) n f) =
      lcA A n (lcRes (l ^ n) (Spec.map (CommRingCat.ofHom (twUg σ A))) f) :=
  (hN l H _ (hA.tw σ) n).1 A hA (PAlg.twId σ A) (PAlg.pdOk_twId σ A) (twUg σ A) (fun e _ => twUg_sharp σ A e) f

theorem lcRes_sq {q : ℕ} {A B C D : Scheme.{0}} {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ C} {d : C ⟶ D} (e : a ≫ b = c ≫ d)
    (x : LocallyConstant D (ZMod q)) : lcRes q a (lcRes q b x) = lcRes q c (lcRes q d x) := by
  ext v
  have e' : b (a v) = d (c v) := by
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  exact congrArg x e'

abbrev pM (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) : Probe (El M.P) (l ^ n) :=
  probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n

abbrev tM (M : Model l K) (σ : Gal(PadicAlgCl l/K)) : El M.P ⥤ El M.P :=
  elTw σ (pxTw M.p (okToOC l K) σ (galOC_okToOC σ))

def gM (H : RIn l) (r : Roots l) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n : ℕ) (c : El M.P) :
    (pM H r M n).U c ⟶ (pM H r M n).U ((tM M σ).obj c) :=
  Spec.map (CommRingCat.ofHom (twUg σ c.1.obj))

theorem gM_sq (hT : TwUg) (H : RIn l) (r : Roots l) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n : ℕ) {c c' : El M.P}
    (φ : c ⟶ c') : gM H r M σ n c' ≫ ((pM H r M n).S.map ((tM M σ).map φ)).unop =
      ((pM H r M n).S.map φ).unop ≫ gM H r M σ n c := by
  change Spec.map (CommRingCat.ofHom (twUg σ c'.1.obj)) ≫
      Spec.map (CommRingCat.ofHom (PAlg.mapUg (PAlg.twMap σ φ.1.hom))) =
    Spec.map (CommRingCat.ofHom (PAlg.mapUg φ.1.hom)) ≫ Spec.map (CommRingCat.ofHom (twUg σ c.1.obj))
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) ((hT l K σ).1 _ _ φ.1.hom)

def twMor (hT : TwUg) (H : RIn l) (r : Roots l) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n : ℕ) :
    Mor (pM H r M n).L (pM H r M n).L (RingHom.id ℤ) where
  G := tM M σ
  τ c := (lcRes (l ^ n) (gM H r M σ n c)).toAddMonoidHom.toIntLinearMap
  nat {c c'} φ x := by
    have e := gM_sq hT H r M σ n φ
    change lcRes (l ^ n) (gM H r M σ n c') (lcRes (l ^ n) ((pM H r M n).S.map ((tM M σ).map φ)).unop x) =
      lcRes (l ^ n) ((pM H r M n).S.map φ).unop (lcRes (l ^ n) (gM H r M σ n c) x)
    exact lcRes_sq e x

def lM (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) :
    Mor (pM H r M n).L (modF (AcrEl M.P n)) (Int.castRingHom (Acris l)) :=
  lcMor hN H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n

abbrev gaM (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n : ℕ) : Mor (modF (AcrEl M.P n)) (modF (AcrEl M.P n)) (ACris.galCris σ) :=
  galMor σ (pxTw M.p (okToOC l K) σ (galOC_okToOC σ)) n

theorem lM_pullC_twMor (hT : TwUg) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n j : ℕ)
    (z : Cn (pM H r M n).L j) :
    (lM hN H r M n).pullC j ((twMor hT H r M σ n).pullC j z) = (gaM M σ n).pullC j ((lM hN H r M n).pullC j z) := by
  funext s
  have hA := (s.obj (Fin.last j)).1.property
  let f : LocallyConstant (SU (PAlg.tw σ (s.obj (Fin.last j)).1.obj)) (ZMod (l ^ n)) := z (s ⋙ tM M σ)
  exact (twAcr_lcA hN H σ (s.obj (Fin.last j)).1.obj hA n f).symm

theorem lM_pull_twMor (hT : TwUg) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n j : ℕ)
    (x : CH.H (pM H r M n).L j) :
    (lM hN H r M n).pull j ((twMor hT H r M σ n).pull j x) = (gaM M σ n).pull j ((lM hN H r M n).pull j x) :=
  pull_pull_of_pullC (twMor hT H r M σ n) (lM hN H r M n) (lM hN H r M n) (gaM M σ n) j
    (lM_pullC_twMor hT hN H r M σ n j) x

theorem key (hE : CrystallineSemistableComparison.E.EtNat) (hT : CrystallineSemistableComparison.E.TwUg) (E : EtIn) (H : RIn l) (r : Roots l) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n j : ℕ)
    (x : Ht (l ^ n) (sch.obj (gb M)) j 0) :
    (twMor hT H r M σ n).pull j ((pts H r M (𝟭 _) n).et 0 j x) =
      (pts H r M (𝟭 _) n).et 0 j (pull _ (sch.map (GlobalTheory.Et.galMap (PadicAlgCl l) M.q σ)) _ j x) :=
  hE E.gen (l ^ n) (El M.P) (El M.P) (pM H r M n) (pM H r M n) (gb M) (gb M)
    (pts H r M (𝟭 _) n) (pts H r M (𝟭 _) n) (GlobalTheory.Et.galMap (PadicAlgCl l) M.q σ) (twMor hT H r M σ n)
    (gM H r M σ n) (fun φ => gM_sq hT H r M σ n φ) (fun c f => rfl)
    (fun c => (hT l K σ).2.2 M c.1.obj c.2) 0 (Or.inl rfl) j x

theorem eM_apply (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n j : ℕ) (x : Ht (l ^ n) (sch.obj (gb M)) j 0) :
    eM hN H r M n 0 j x = (lM hN H r M n).pull j ((pts H r M (𝟭 _) n).et 0 j x) := rfl

theorem galMH_apply (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n j : ℕ) (y : M.MH n j) :
    M.galMH σ n j y = (gaM M σ n).pull j y := rfl

theorem equi_at (hE : CrystallineSemistableComparison.E.EtNat) (hT : CrystallineSemistableComparison.E.TwUg) (E : EtIn) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K)
    (σ : Gal(PadicAlgCl l/K)) (n j : ℕ) (x : Ht (l ^ n) (sch.obj (gb M)) j 0) :
    eM hN H r M n 0 j (pull _ (sch.map (GlobalTheory.Et.galMap (PadicAlgCl l) M.q σ)) _ j x) = M.galMH σ n j (eM hN H r M n 0 j x) :=
  (eM_apply hN H r M n j _).trans ((congrArg ((lM hN H r M n).pull j) (key hE hT E H r M σ n j x).symm).trans
    ((lM_pull_twMor hT hN H r M σ n j _).trans ((congrArg ((gaM M σ n).pull j) (eM_apply hN H r M n j x).symm).trans
      (galMH_apply M σ n j _).symm)))

theorem fEqui : CrystallineSemistableComparison.E.EtNat → CrystallineSemistableComparison.E.TwUg → CrystallineSemistableComparison.E.FEqui :=
  fun hE hT E hN l _ H r K M n j σ x => equi_at hE hT E hN H r M σ n j x

end GlobalTheory.CompanionTheory.FEquiProof
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoeffIterateVerschiebung
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.LcSp

section Witt

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]

theorem coeff_iterate_verschiebung (m : ℕ) (y : WittVector p R) (i : ℕ) (h : i < m) :
    (WittVector.verschiebung^[m] y).coeff i = 0 := by
  induction m generalizing i with
  | zero => omega
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    cases i with
    | zero => exact WittVector.verschiebung_coeff_zero _
    | succ i =>
      rw [WittVector.verschiebung_coeff_succ]
      exact ih i (by omega)

theorem idem_eq_zero (u : WittVector p R) (hu : u * u = u) (h0 : u.coeff 0 = 0) : u = 0 := by
  have key : ∀ n, ∀ i < n + 1, u.coeff i = 0 := by
    intro n
    induction n with
    | zero =>
      intro i hi
      obtain rfl : i = 0 := by omega
      exact h0
    | succ n ih =>
      intro i hi
      by_cases h : i < n + 1
      · exact ih i h
      obtain rfl : i = n + 1 := by omega
      obtain ⟨y, e⟩ : ∃ y, u = WittVector.verschiebung^[n + 1] y := ⟨_, WittVector.eq_iterate_verschiebung ih⟩
      have e2 : u = WittVector.verschiebung^[(n + 1) + (n + 1)]
          (WittVector.frobenius^[n + 1] y * WittVector.frobenius^[n + 1] y) := by
        rw [← WittVector.iterate_verschiebung_mul, ← e, hu]
      rw [e2]
      exact coeff_iterate_verschiebung _ _ _ (by omega)
  ext i
  rw [key i i (by omega)]
  simp

theorem sum_teichmuller {ι : Type} [Fintype ι] (e : ι → R) (he : CompleteOrthogonalIdempotents e) :
    ∑ i, WittVector.teichmuller p (e i) = (1 : WittVector p R) := by
  have ho : OrthogonalIdempotents fun i => WittVector.teichmuller p (e i) :=
    { idem := fun i => by
        change _ * _ = _
        rw [← map_mul, (he.idem i).eq]
      ortho := fun i j hij => by
        change _ * _ = _
        rw [← map_mul, he.ortho hij, WittVector.teichmuller_zero] }
  have hs : IsIdempotentElem (∑ i, WittVector.teichmuller p (e i)) := ho.isIdempotentElem_sum
  have h1 : (1 : WittVector p R) - ∑ i, WittVector.teichmuller p (e i) = 0 := by
    refine idem_eq_zero _ hs.one_sub.eq ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← WittVector.constantCoeff_apply, map_sub, map_one, map_sum]
    simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
    rw [he.complete, sub_self]
  exact (sub_eq_zero.1 h1).symm

end Witt

variable {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ)

theorem sum_teich {ι : Type} [Fintype ι] (e : ι → A.A) (he : CompleteOrthogonalIdempotents e) :
    ∑ i, WittVector.teichmuller l (e i) = (1 : A.W) := by
  rcases subsingleton_or_nontrivial A.A with h | h
  · exact WittVector.ext fun _ => Subsingleton.elim _ _
  · haveI : CharP A.A l := (CharP.charP_iff_prime_eq_zero Fact.out).2 A.natCast_l
    exact sum_teichmuller e he

theorem acr_ext {ι : Type} [Fintype ι] (e : ι → A.A) (he : CompleteOrthogonalIdempotents e) {x y : A.Acr n}
    (h : ∀ i, A.toAcr n (WittVector.teichmuller l (e i)) * x = A.toAcr n (WittVector.teichmuller l (e i)) * y) :
    x = y := by
  have hs : ∑ i, A.toAcr n (WittVector.teichmuller l (e i)) = 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, sum_teich A e he, map_one]
  calc x = (∑ i, A.toAcr n (WittVector.teichmuller l (e i))) * x := by rw [hs, one_mul]
    _ = (∑ i, A.toAcr n (WittVector.teichmuller l (e i))) * y := by
      simp only [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => h i
    _ = y := by rw [hs, one_mul]

theorem exists_cast : ∃ c : ZMod (l ^ n) →+* A.Acr n, ∀ a, c a = (a.val : A.Acr n) := by
  haveI : CharP (A.Acr n) (ringChar (A.Acr n)) := ringChar.charP _
  have hd : ringChar (A.Acr n) ∣ l ^ n :=
    (CharP.cast_eq_zero_iff (A.Acr n) (ringChar (A.Acr n)) (l ^ n)).1 (by
      rw [Nat.cast_pow]
      exact A.pow_l_acr n)
  refine ⟨ZMod.castHom hd _, fun a => ?_⟩
  rw [ZMod.castHom_apply, ZMod.natCast_val]

variable {A n}

section Main

variable (hI : LcIdem) (H : RIn l) (hA : A.IsTest)
include hI H hA

theorem exists_isLcA (f : LocallyConstant (SU A) (ZMod (l ^ n))) : ∃ x, IsLcA A n f x := by
  obtain ⟨e, he, -, h2⟩ := hI l H A hA (ZMod (l ^ n)) f
  refine ⟨∑ a, A.toAcr n (WittVector.teichmuller l (e a)) * (a.val : A.Acr n), fun e' a he' hf => ?_⟩
  have h3 : e' * e a = e' := h2 e' a he' hf
  rw [Finset.mul_sum, Finset.sum_eq_single a]
  · rw [← mul_assoc, ← map_mul, ← map_mul, h3]
  · intro b _ hb
    have h4 : e' * e b = 0 := by
      calc e' * e b = e' * e a * e b := by rw [h3]
        _ = 0 := by rw [mul_assoc, he.ortho hb.symm, mul_zero]
    rw [← mul_assoc, ← map_mul, ← map_mul, h4, WittVector.teichmuller_zero, map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem isLcA_unique {f : LocallyConstant (SU A) (ZMod (l ^ n))} {x y : A.Acr n}
    (hx : IsLcA A n f x) (hy : IsLcA A n f y) : x = y := by
  obtain ⟨e, he, h1, -⟩ := hI l H A hA (ZMod (l ^ n)) f
  refine acr_ext A n e he fun a => ?_
  have hf : ∀ p : PrimeSpectrum A.Ug, algebraMap A.U A.Ug (A.sharp (e a)) ∉ p.asIdeal → f p = a :=
    fun p hp => (h1 a p).1 hp
  rw [hx (e a) a (he.idem a) hf, hy (e a) a (he.idem a) hf]

theorem isLcA_one : IsLcA A n 1 1 := by
  obtain ⟨c, hc⟩ := exists_cast A n
  obtain ⟨e, he, -, h2⟩ := hI l H A hA (ZMod (l ^ n)) 1
  intro e' a he' hf
  by_cases ha : a = 1
  · subst ha
    rw [← hc, map_one]
  · have h3 : e' * e a = e' := h2 e' a he' hf
    have h4 : e' * e 1 = e' := h2 e' 1 he' fun _ _ => rfl
    have h5 : e' = 0 := by
      calc e' = e' * e 1 * e a := by rw [h4, h3]
        _ = 0 := by rw [mul_assoc, he.ortho (Ne.symm ha), mul_zero]
    rw [h5, WittVector.teichmuller_zero, map_zero, zero_mul, zero_mul]

theorem exists_pair (f g : LocallyConstant (SU A) (ZMod (l ^ n))) :
    ∃ e : ZMod (l ^ n) × ZMod (l ^ n) → A.A, CompleteOrthogonalIdempotents e ∧
      ∀ (ab : ZMod (l ^ n) × ZMod (l ^ n)) (p : PrimeSpectrum A.Ug),
        algebraMap A.U A.Ug (A.sharp (e ab)) ∉ p.asIdeal → f p = ab.1 ∧ g p = ab.2 := by
  let h : LocallyConstant (SU A) (ZMod (l ^ n) × ZMod (l ^ n)) :=
    ⟨fun p => (f p, g p), f.isLocallyConstant.prodMk g.isLocallyConstant⟩
  obtain ⟨e, he, h1, -⟩ := hI l H A hA _ h
  refine ⟨e, he, fun ab p hp => ?_⟩
  have h2 : (f p, g p) = ab := (h1 ab p).1 hp
  exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

theorem isLcA_add {f g : LocallyConstant (SU A) (ZMod (l ^ n))} {x y z : A.Acr n}
    (hx : IsLcA A n f x) (hy : IsLcA A n g y) (hz : IsLcA A n (f + g) z) : z = x + y := by
  obtain ⟨e, he, h⟩ := exists_pair hI H hA f g
  obtain ⟨c, hc⟩ := exists_cast A n
  refine acr_ext A n e he fun ab => ?_
  have h1 := hx (e ab) ab.1 (he.idem ab) fun p hp => (h ab p hp).1
  have h2 := hy (e ab) ab.2 (he.idem ab) fun p hp => (h ab p hp).2
  have h3 := hz (e ab) (ab.1 + ab.2) (he.idem ab) fun p hp => by
    change f p + g p = _
    rw [(h ab p hp).1, (h ab p hp).2]
  rw [h3, mul_add, h1, h2, ← hc, ← hc, ← hc, map_add (f := _), mul_add]

theorem isLcA_mul {f g : LocallyConstant (SU A) (ZMod (l ^ n))} {x y z : A.Acr n}
    (hx : IsLcA A n f x) (hy : IsLcA A n g y) (hz : IsLcA A n (f * g) z) : z = x * y := by
  obtain ⟨e, he, h⟩ := exists_pair hI H hA f g
  obtain ⟨c, hc⟩ := exists_cast A n
  refine acr_ext A n e he fun ab => ?_
  have h1 := hx (e ab) ab.1 (he.idem ab) fun p hp => (h ab p hp).1
  have h2 := hy (e ab) ab.2 (he.idem ab) fun p hp => (h ab p hp).2
  have h3 := hz (e ab) (ab.1 * ab.2) (he.idem ab) fun p hp => by
    change f p * g p = _
    rw [(h ab p hp).1, (h ab p hp).2]
  have ht : A.toAcr n (WittVector.teichmuller l (e ab)) * A.toAcr n (WittVector.teichmuller l (e ab)) =
      A.toAcr n (WittVector.teichmuller l (e ab)) := by
    rw [← map_mul, ← map_mul, (he.idem ab).eq]
  rw [← hc] at h1 h2 h3
  calc _ = A.toAcr n (WittVector.teichmuller l (e ab)) * (c ab.1 * c ab.2) := by rw [h3, map_mul]
    _ = (A.toAcr n (WittVector.teichmuller l (e ab)) * c ab.1) * (A.toAcr n (WittVector.teichmuller l (e ab)) * c ab.2) := by
      rw [mul_mul_mul_comm, ht]
    _ = (A.toAcr n (WittVector.teichmuller l (e ab)) * x) * (A.toAcr n (WittVector.teichmuller l (e ab)) * y) := by
      rw [h1, h2]
    _ = _ := by rw [mul_mul_mul_comm, ht]

end Main

theorem lcSpec_of_lcIdem : CrystallineSemistableComparison.E.LcIdem → CrystallineSemistableComparison.E.LcSpec := by
  intro hI l _ H A hA n
  have P : ∃ κ : LocallyConstant (SU A) (ZMod (l ^ n)) →+ A.Acr n, ∀ f, IsLcA A n f (κ f) := by
    choose k hk using exists_isLcA (n := n) hI H hA
    exact ⟨AddMonoidHom.mk' k fun f g => isLcA_add hI H hA (hk f) (hk g) (hk (f + g)), hk⟩
  have S : ∀ f, IsLcA A n f (lcA A n f) := pick_spec P
  refine ⟨S, isLcA_unique hI H hA (S 1) (isLcA_one hI H hA),
    fun f g => isLcA_mul hI H hA (S f) (S g) (S (f * g)), fun f e he h => ?_⟩
  refine acr_ext A n e he fun a => ?_
  rw [S f (e a) a (he.idem a) (h a), Finset.mul_sum, Finset.sum_eq_single a]
  · rw [← mul_assoc, ← map_mul, ← map_mul, (he.idem a).eq]
  · intro b _ hb
    rw [← mul_assoc, ← map_mul, ← map_mul, he.ortho hb.symm, WittVector.teichmuller_zero, map_zero, zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ a) h'

end GlobalTheory.CompanionTheory.LcSp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdemMulEqZero
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.LcLogProof

variable {l : ℕ} [Fact l.Prime]

theorem eq_of_idem (A : PAlg l) {a b : A.W} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (h : a.coeff 0 = b.coeff 0) : a = b := by
  have ha' : a * a = a := ha
  have hb' : b * b = b := hb
  set d := a - b with hd
  have hd3 : d * d * d = d := by
    rw [hd]
    linear_combination (a + 1 - 3 * b) * ha' + (3 * a - b - 1) * hb'
  have hmem : d ∈ Ideal.span {(l : A.W)} := by
    rw [A.mem_span_l_iff, hd, ← WittVector.constantCoeff_apply, map_sub, sub_eq_zero]
    exact h
  have hall : ∀ k : ℕ, d ∈ Ideal.span {(l : A.W)} ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← hd3, pow_succ]
      exact Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ ih) hmem
  have h0 : d = 0 := IsHausdorff.haus (A.completeW.toIsHausdorff) d fun k => by
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    exact hall k
  exact sub_eq_zero.1 h0

theorem teich_sum_one (A : PAlg l) {ι : Type} [Fintype ι] {e : ι → A.A}
    (he : CompleteOrthogonalIdempotents e) : ∑ a, WittVector.teichmuller l (e a) = (1 : A.W) := by
  have ho : OrthogonalIdempotents fun i => (WittVector.teichmuller l (e i) : A.W) :=
    ⟨fun i => by
      show _ * _ = _
      rw [← map_mul, (he.idem i).eq],
     fun i j hij => by
      show _ * _ = _
      rw [← map_mul, he.ortho hij, WittVector.teichmuller_zero]⟩
  refine eq_of_idem A ho.isIdempotentElem_sum IsIdempotentElem.one ?_
  show WittVector.constantCoeff (∑ a, (WittVector.teichmuller l (e a) : A.W)) = WittVector.constantCoeff (1 : A.W)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_one]
  simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  exact he.complete

theorem mul_pow_congr {R : Type*} [CommRing R] {s x y : R} (h : s * x = s * y) (k : ℕ) :
    s * x ^ k = s * y ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, ← mul_assoc, ih]
    linear_combination y ^ k * h

theorem idem_mul_eq_zero {R : Type} [CommRing R] {c x : R} (hc : IsIdempotentElem c)
    (h : algebraMap R (Localization.Away c) x = 0) : c * x = 0 := by
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers c) _ x).1 h
  cases k with
  | zero => simp only [pow_zero, one_mul] at hk; simp [hk]
  | succ k => simpa only [hc.pow_succ_eq] using hk

theorem toΓ_injective (B : Type) [CommRing B] : Function.Injective (toΓ B) := fun x y h => by
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom h
  simpa [toΓ] using this

theorem pow_on_part (r : Roots l) (A : PAlg l) (n : ℕ) (f : LocallyConstant (SU A) (ZMod (l ^ n))) (x : A.Ug)
    (hp : IsPow (r.zeta A n) f (toΓ A.Ug x)) (a : ZMod (l ^ n)) (c : A.Ug) (hc : IsIdempotentElem c)
    (hf : ∀ p : PrimeSpectrum A.Ug, c ∉ p.asIdeal → f p = a) :
    c * (x - kb A (r.ρ n).1 ^ a.val) = 0 := by
  have hv : ∀ v : Spec (CommRingCat.of (Localization.Away c)),
      f ((Spec.map (CommRingCat.ofHom (algebraMap A.Ug (Localization.Away c)))) v) = a := by
    intro v
    refine hf (PrimeSpectrum.comap (algebraMap A.Ug (Localization.Away c)) v) fun hm => ?_
    have hu : IsUnit (algebraMap A.Ug (Localization.Away c) c) := IsLocalization.Away.algebraMap_isUnit c
    have hm' : algebraMap A.Ug (Localization.Away c) c ∈ PrimeSpectrum.asIdeal v := hm
    exact (PrimeSpectrum.isPrime v).ne_top (Ideal.eq_top_of_isUnit_mem _ hm' hu)
  have h := hp _ (Spec.map (CommRingCat.ofHom (algebraMap A.Ug (Localization.Away c)))) a hv
  have h2 : toΓ _ (algebraMap A.Ug (Localization.Away c) x) =
      toΓ _ (algebraMap A.Ug (Localization.Away c) (kb A (r.ρ n).1 ^ a.val)) := by
    rw [map_pow, map_pow, ← toΓ_nat, h, ← toΓ_nat]
    rfl
  refine idem_mul_eq_zero hc ?_
  rw [map_sub, toΓ_injective _ h2, sub_self]

theorem ug_injective (H : RIn l) (A : PAlg l) : Function.Injective (algebraMap A.U A.Ug) :=
  IsLocalization.injective _ (Submonoid.powers_le.2 (H.tf A))

theorem kb_rho (r : Roots l) (A : PAlg l) (n : ℕ) :
    kb A (r.ρ n).1 = algebraMap A.U A.Ug (A.oC (rootSeqInt l n)) := by
  show A.cToUg (clToC l (r.ρ n).1) = _
  rw [r.hρ]
  exact A.cToUg_coe (rootSeqInt l n)

theorem root_pow (A : PAlg l) (n : ℕ) : A.oC (rootSeqInt l n) ^ l ^ n = 1 := by
  rw [← map_pow, show rootSeqInt l n ^ l ^ n = 1 from Subtype.ext (rootSeq_pow n), map_one]

theorem isLog_one (hEx : LogEx) (hMul : LogMul) (A : PAlg l) (n : ℕ) : IsLog A n 1 0 := by
  obtain ⟨y, hy⟩ := (hEx l A n).1 1 (map_one _)
  have h := hMul l A n 1 1 y y (map_one _) (map_one _) hy hy
  rw [mul_one] at h
  have h0 : y + y = y := (hEx l A n).2.1 _ _ _ h hy
  have : y = 0 := by linear_combination h0
  rwa [this] at hy

theorem isLog_pow (hEx : LogEx) (hMul : LogMul) (A : PAlg l) (n : ℕ) {w : A.W} {y : A.Acr n} (h1 : A.th w = 1)
    (hy : IsLog A n w y) (k : ℕ) : IsLog A n (w ^ k) ((k : A.Acr n) * y) := by
  induction k with
  | zero => simpa using isLog_one hEx hMul A n
  | succ k ih =>
    have h := hMul l A n (w ^ k) w _ _ (by rw [map_pow, h1, one_pow]) h1 ih hy
    rw [← pow_succ] at h
    have e : (k : A.Acr n) * y + y = ((k + 1 : ℕ) : A.Acr n) * y := by push_cast; ring
    rwa [e] at h

theorem natCast_q (A : PAlg l) (n : ℕ) : ((l ^ n : ℕ) : A.Acr n) = 0 := by
  rw [Nat.cast_pow]; exact A.pow_l_acr n

theorem log_on_part (hEx : LogEx) (hMul : LogMul) (hEps : LogEps) (A : PAlg l) (n : ℕ) {η u c : A.A} {v : ℕ}
    (hη : η ^ l ^ n = A.s (epsilon l)) (hz : A.sharp η ^ l ^ n = 1) (hc : IsIdempotentElem c)
    (hE : A.sharp c * (A.sharp u - A.sharp η ^ v) = 0) {y : A.Acr n}
    (h1 : A.th (WittVector.teichmuller l (u ^ l ^ n)) = 1)
    (hy : IsLog A n (WittVector.teichmuller l (u ^ l ^ n)) y) :
    A.toAcr n (WittVector.teichmuller l c) * y = A.toAcr n (WittVector.teichmuller l c) * ((v : A.Acr n) *
      A.cris n (ACris.periodT (untilt_epsilon (p := l)))) := by
  have hq : 1 ≤ l ^ n := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
  obtain ⟨m, hm⟩ : ∃ m, m + v = l ^ n * v := ⟨(l ^ n - 1) * v, by
    rw [Nat.sub_mul, one_mul]; exact Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ hq)⟩
  set E : A.W := WittVector.teichmuller l c with hEdef
  set U : A.W := WittVector.teichmuller l u with hU
  set N : A.W := WittVector.teichmuller l η with hN
  have hEi : E * E = E := by rw [hEdef, ← map_mul, hc.eq]
  have hthE : A.th E = A.sharp c := rfl
  have hthU : A.th U = A.sharp u := rfl
  have hthN : A.th N = A.sharp η := rfl

  have hw1 : A.th (E * U * N ^ m + (1 - E)) = 1 := by
    have e1 : A.sharp η ^ (m + v) = 1 := by rw [hm, pow_mul, hz, one_pow]
    simp only [map_add (f := _), map_sub, map_mul, map_pow, map_one, hthE, hthU, hthN]
    rw [pow_add] at e1
    linear_combination A.sharp η ^ m * hE + A.sharp c * e1
  obtain ⟨yw, hyw⟩ := (hEx l A n).1 _ hw1
  have hwq := isLog_pow hEx hMul A n hw1 hyw (l ^ n)
  rw [natCast_q, zero_mul] at hwq

  have hε1 : A.th (WittVector.teichmuller l (A.s (epsilon l))) = 1 := by
    rw [← hη]; exact (map_pow A.sharp η (l ^ n)).trans hz
  have hεm := isLog_pow hEx hMul A n hε1 (hEps l A n) m
  have hprod := hMul l A n _ _ _ _ h1 (by rw [map_pow, hε1, one_pow]) hy hεm
  have hid : E * (E * U * N ^ m + (1 - E)) ^ l ^ n =
      E * (WittVector.teichmuller l (u ^ l ^ n) * WittVector.teichmuller l (A.s (epsilon l)) ^ m) := by
    have h2 : E * (E * U * N ^ m + (1 - E)) = E * (U * N ^ m) := by
      linear_combination (U * N ^ m - 1) * hEi
    rw [mul_pow_congr h2, ← hη, map_pow, map_pow, ← hU, ← hN, mul_pow, ← pow_mul, ← pow_mul, mul_comm m]
  have key := (hEx l A n).2.2 E _ _ _ _ (show IsIdempotentElem E from hEi) hid hwq hprod
  have hm' : (m : A.Acr n) + (v : A.Acr n) = 0 := by
    have := congrArg (Nat.cast : ℕ → A.Acr n) hm
    rw [Nat.cast_add, Nat.cast_mul, natCast_q, zero_mul] at this
    exact this
  linear_combination (-1 : A.Acr n) * key + (A.toAcr n E * A.cris n (ACris.periodT (untilt_epsilon (p := l)))) * (-hm')

theorem lcLog : CrystallineSemistableComparison.E.LcIdem → CrystallineSemistableComparison.E.LcSpec → CrystallineSemistableComparison.E.LcCover → CrystallineSemistableComparison.E.LogEx → CrystallineSemistableComparison.E.LogMul → CrystallineSemistableComparison.E.LogEps →
    CrystallineSemistableComparison.E.EpsRoot → CrystallineSemistableComparison.E.LcLog := by
  intro hI hS _ hEx hMul hEps hR l _ H r A hA n u f hp
  obtain ⟨η, hη, hsh⟩ := hR l n
  obtain ⟨e, he, hiff, -⟩ := hI l H A hA (ZMod (l ^ n)) f
  have hz : A.sharp (A.s η) ^ l ^ n = 1 := by rw [hsh A]; exact root_pow A n
  have hη' : (A.s η) ^ l ^ n = A.s (epsilon l) := by rw [← map_pow, hη]
  have hid : ∀ a, IsIdempotentElem (A.sharp (e a)) := fun a => by
    show _ * _ = _
    rw [← map_mul, (he.idem a).eq]
  have hE : ∀ a : ZMod (l ^ n), A.sharp (e a) * (A.sharp u - A.sharp (A.s η) ^ a.val) = 0 := by
    intro a
    have hidg : IsIdempotentElem (algebraMap A.U A.Ug (A.sharp (e a))) := (hid a).map _
    have h := pow_on_part r A n f _ hp a _ hidg (fun p hpn => (hiff a p).1 hpn)
    rw [kb_rho] at h
    apply ug_injective H A
    rw [map_zero, ← h, hsh A]
    simp only [map_mul, map_sub, map_pow]
  have hsum : ∑ a, A.sharp (e a) = 1 := by
    have := congrArg A.th (teich_sum_one A he)
    rwa [map_sum, map_one] at this
  have h1 : A.th (WittVector.teichmuller l (u ^ l ^ n)) = 1 := by
    have e0 : A.th (WittVector.teichmuller l (u ^ l ^ n)) = A.sharp u ^ l ^ n := map_pow A.sharp u _
    rw [e0, ← one_mul (A.sharp u ^ l ^ n), ← hsum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h2 : A.sharp (e a) * A.sharp u = A.sharp (e a) * A.sharp (A.s η) ^ a.val := by
      linear_combination hE a
    rw [mul_pow_congr h2, ← pow_mul, mul_comm a.val, pow_mul, hz, one_pow, mul_one]
  obtain ⟨y, hy⟩ := (hEx l A n).1 _ h1
  have hloc := fun a : ZMod (l ^ n) => log_on_part hEx hMul hEps A n hη' hz (he.idem a) (hE a) h1 hy
  have hsumA : ∑ a, A.toAcr n (WittVector.teichmuller l (e a)) = 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, teich_sum_one A he, map_one]
  have hlc := ((hS l H A hA n).2.2.2 f e he (fun a p hpn => (hiff a p).1 hpn))
  have hfin : y = (ACris.periodT (untilt_epsilon (p := l)) : Acris l) • lcA A n f := by
    rw [Algebra.smul_def, hlc]
    show y = A.cris n _ * _
    rw [← one_mul y, ← hsumA, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hloc a]; ring
  rwa [← hfin]

end GlobalTheory.CompanionTheory.LcLogProof
end
end
