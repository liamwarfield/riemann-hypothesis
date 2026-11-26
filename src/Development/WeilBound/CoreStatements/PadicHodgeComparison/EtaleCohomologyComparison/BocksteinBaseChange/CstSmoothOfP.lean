module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmoothOfEtSide
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.AtlasOf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TiltSectionUnits.FcIsUnitSub
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TiltSectionUnits.NormLtOneOfMemMax
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FirstChernCompatibleL
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.LimitBilinearCup.OmCup
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.FirstChernCocycleAllLevels

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.FirstChernCompatGlue
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

namespace GlueB'

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (Amp : ∀ M : Model l K, E.LineData M.X → Prop)

theorem f_act (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (j : ℕ) (σ : K.fixingSubgroup) (x : ((dat Amp).H a).N j) :
    bβ Amp hC a j (((dat Amp).H a).act j σ x) = ((dat Amp).A a).act j σ (bβ Amp hC a j x) :=
  GlueBL.lim_sq (βS hC (B.schFn M.p) (okToOC l K) false j) (βS hC (B.schFn M.p) (okToOC l K) false j)
    (M.galH false j (IntermediateField.fixingSubgroupEquiv K σ)) (M.galS j (IntermediateField.fixingSubgroupEquiv K σ))
    (fun n y => hC.gal (B.schFn M.p) (okToOC l K) (IntermediateField.fixingSubgroupEquiv K σ) (galOC_okToOC _) false n j y) x

theorem f_act' (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (j : ℕ) (σ : K.fixingSubgroup) (x : ((dat Amp).H' a).N j) :
    bβ' Amp hC a j (((dat Amp).H' a).act j σ x) = ((dat Amp).A a).act j σ (bβ' Amp hC a j x) :=
  GlueBL.lim_sq (βS hC (B.schFn M.p) (okToOC l K) true j) (βS hC (B.schFn M.p) (okToOC l K) true j)
    (M.galH true j (IntermediateField.fixingSubgroupEquiv K σ)) (M.galS j (IntermediateField.fixingSubgroupEquiv K σ))
    (fun n y => hC.gal (B.schFn M.p) (okToOC l K) (IntermediateField.fixingSubgroupEquiv K σ) (galOC_okToOC _) true n j y) x

theorem f_phi' (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (j : ℕ) (x : ((dat Amp).H' a).N j) :
    bβ' Amp hC a j ((dat Amp).phi' a j x) = (dat Amp).phiA a j (bβ' Amp hC a j x) :=
  GlueBL.lim_sq (βS hC (B.schFn M.p) (okToOC l K) true j) (βS hC (B.schFn M.p) (okToOC l K) true j)
    (M.phiH j) (M.phiS j) (fun n y => hC.phi (B.schFn M.p) (okToOC l K) n j y) x

theorem f_nat (hC : B.Compat l) {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : (dat Amp).Ch M}
    {b : (dat Amp).Ch N} (m : (dat Amp).Mo u hu a b) (j : ℕ) (x : ((dat Amp).H b).N j) :
    bβ Amp hC a j ((dat Amp).pullH m j x) = (dat Amp).pullA m j (bβ Amp hC b j x) :=
  GlueBL.lim_sq (βS hC (B.schFn N.p) (okToOC l K) false j) (βS hC (B.schFn M.p) (okToOC l K) false j)
    (Model.pullH u hu false j) (Model.pullS u hu j) (fun n y => hC.pull (okToOC l K) (B.schMap u hu) false n j y) x

theorem f_nat' (hC : B.Compat l) {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : (dat Amp).Ch M}
    {b : (dat Amp).Ch N} (m : (dat Amp).Mo u hu a b) (j : ℕ) (x : ((dat Amp).H' b).N j) :
    bβ' Amp hC a j (datPull Amp m j x) = (dat Amp).pullA m j (bβ' Amp hC b j x) :=
  GlueBL.lim_sq (βS hC (B.schFn N.p) (okToOC l K) true j) (βS hC (B.schFn M.p) (okToOC l K) true j)
    (Model.pullH u hu true j) (Model.pullS u hu j) (fun n y => hC.pull (okToOC l K) (B.schMap u hu) true n j y) x

theorem f_cup (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) {i j : ℕ} (x : ((dat Amp).H a).N i)
    (y : ((dat Amp).H a).N j) (z : ((dat Amp).H a).N (i + j)) (hz : ((dat Amp).H a).cup x y z) :
    ((dat Amp).A a).cup (bβ Amp hC a i x) (bβ Amp hC a j y) (bβ Amp hC a (i + j) z) :=
  GlueBL.lim_cup (fun j => βS hC (B.schFn M.p) (okToOC l K) false j)
    (fun n i j x y => hC.cup (B.schFn M.p) (okToOC l K) false n rfl x y) x y z hz

theorem f_one (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (x : ((dat Amp).H a).N 0) (hx : ((dat Amp).H a).one x) :
    ((dat Amp).A a).one (bβ Amp hC a 0 x) :=
  GlueBL.lim_one (fun j => βS hC (B.schFn M.p) (okToOC l K) false j)
    (fun n => hC.one (B.schFn M.p) (okToOC l K) false n) x hx

theorem first_chern_compat_glue (hC : B.Compat l) (h1 : B.FirstChernCompatible l) {M : Model l K} (a : (dat Amp).Ch M) (x : ((dat Amp).H a).N 2)
    (hx : (dat Amp).c1H a x) : (dat Amp).c1A a (bβ Amp hC a 2 x) :=
  h1 M.p (okToOC l K) false a.1 _ hx

def bmap (hMain : B.Main l) (hC : B.Compat l) (h1 : B.FirstChernCompatible l) : BMap Model.Sm (dat Amp) where
  β a j := bβ Amp hC a j
  β' a j := bβ' Amp hC a j
  act a _ j σ x := f_act Amp hC a j σ x
  nat m _ _ j x := f_nat Amp hC m j x
  cup a _ _ _ x y z hz := f_cup Amp hC a x y z hz
  one a _ x hx := f_one Amp hC a x hx
  c1 a _ x hx := first_chern_compat_glue Amp hC h1 a x hx
  inj a hM j := f_inj Amp hMain hC a hM j
  surj a hM j := f_surj Amp hMain hC a hM j
  act' a _ j σ x := f_act' Amp hC a j σ x
  phi' a _ j x := f_phi' Amp hC a j x
  surj' a hM j := f_surj' Amp hMain hC a hM j

def bphi (hMain : B.Main l) (hC : B.Compat l) (h1 : B.FirstChernCompatible l) : BPhi (bmap Amp hMain hC h1) where
  pull m j := datPull Amp m j
  nat m _ _ j x := f_nat' Amp hC m j x
  inj a hM j := f_inj' Amp hMain hC a hM j

end GlueB'

theorem glueB : GlueB := fun l _ K Amp hMain hC h1 =>
  ⟨GlueB'.bmap Amp hMain hC h1, GlueB'.bphi Amp hMain hC h1, rfl⟩

end CrystallineSemistableComparison
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.FirstChernClassUnique
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.ActSmul
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison

namespace GlueLim

variable {R : Type} [CommRing R] {Γ : Type} (S : ℕ → Sys.{1} R) {σ : Γ → R →+* R} (act : ∀ j g, Sys.Hom (S j) (S j) (σ g))

theorem hom_smul {R' : Type} [CommRing R'] {S₁ : Sys.{1} R} {S₂ : Sys.{1} R'} {τ : R →+* R'} (φ : Sys.Hom S₁ S₂ τ) (c : R)
    (x : S₁.lim) : φ.lim.toAddMonoidHom (c • x) = τ c • φ.lim.toAddMonoidHom x :=
  φ.lim.map_smulₛₗ c x

theorem act_smul (j : ℕ) (g : Γ) (c : R) (y : (limMod S act).N j) :
    (limMod S act).act j g (c • y) = σ g c • (limMod S act).act j g y :=
  (act j g).lim.map_smulₛₗ c (show (S j).lim from y)

variable (one : ∀ n, (S 0).M n) (cup : ∀ n i j, (S i).M n → (S j).M n → (S (i + j)).M n)

theorem one_uniq (x y : (limAlg S act one cup).N 0) (hx : (limAlg S act one cup).one x) (hy : (limAlg S act one cup).one y) :
    x = y :=
  Subtype.ext (funext fun n => (hx n).trans (hy n).symm)

theorem cup_uniq {i j : ℕ} (x : (limAlg S act one cup).N i) (y : (limAlg S act one cup).N j)
    (z z' : (limAlg S act one cup).N (i + j)) (hz : (limAlg S act one cup).cup x y z) (hz' : (limAlg S act one cup).cup x y z') :
    z = z' :=
  Subtype.ext (funext fun n => (hz n).trans (hz' n).symm)

theorem cup_smul (hb : ∀ n i j, ∃ b : (S i).M n →ₗ[R] (S j).M n →ₗ[R] (S (i + j)).M n, ∀ x y, b x y = cup n i j x y)
    {i j : ℕ} (c c' : R) (x : (limAlg S act one cup).N i) (y : (limAlg S act one cup).N j)
    (z : (limAlg S act one cup).N (i + j)) (hz : (limAlg S act one cup).cup x y z) :
    (limAlg S act one cup).cup (c • x) (c' • y) ((c * c') • z) := fun n =>
  Exists.elim (hb n i j) fun b hb => by
    have h : (show (S (i + j)).lim from z).1 n = cup n i j ((show (S i).lim from x).1 n) ((show (S j).lim from y).1 n) := hz n
    change (c * c') • (show (S (i + j)).lim from z).1 n =
      cup n i j (c • (show (S i).lim from x).1 n) (c' • (show (S j).lim from y).1 n)
    rw [h, ← hb, ← hb, LinearMap.map_smul₂, map_smul, smul_smul]

theorem cup_ex (hr : ∀ n i j x y, (S (i + j)).r n (cup (n + 1) i j x y) = cup n i j ((S i).r n x) ((S j).r n y))
    {i j : ℕ} (x : (limAlg S act one cup).N i) (y : (limAlg S act one cup).N j) : ∃ z, (limAlg S act one cup).cup x y z :=
  ⟨(⟨fun n => cup n i j ((show (S i).lim from x).1 n) ((show (S j).lim from y).1 n), fun n =>
    (hr n i j _ _).trans (by rw [(show (S i).lim from x).2 n, (show (S j).lim from y).2 n])⟩ : (S (i + j)).lim), fun _ => rfl⟩

end GlueLim

end CrystallineSemistableComparison
end
end

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

namespace GlueL'

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (Amp : ∀ M : Model l K, E.LineData M.X → Prop)

theorem ch (hS : ∀ M : Model l K, M.Sm → ∃ D, Amp M D) (M : Model l K) (hM : M.Sm) : Nonempty ((dat Amp).Ch M) :=
  Exists.elim (hS M hM) fun D hD => ⟨(⟨D, hD⟩ : {D : E.LineData M.X // Amp M D})⟩

theorem refine (M N : Model l K) (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (a : (dat Amp).Ch M) (b : (dat Amp).Ch N) :
    ∃ a' : (dat Amp).Ch M, Nonempty ((dat Amp).Mo (𝟙 M.X) (Category.id_comp _) a' a) ∧ Nonempty ((dat Amp).Mo u hu a' b) :=
  ⟨a, Nonempty.intro (PUnit.unit : PUnit.{2}), Nonempty.intro (PUnit.unit : PUnit.{2})⟩

theorem act_smul {M : Model l K} (a : (dat Amp).Ch M) (j : ℕ) (σ : K.fixingSubgroup) (c : (per l K).A)
    (y : ((dat Amp).A a).N j) : ((dat Amp).A a).act j σ (c • y) = (per l K).σA σ c • ((dat Amp).A a).act j σ y :=
  GlueLim.act_smul M.MS (fun j g => M.galS j (IntermediateField.fixingSubgroupEquiv K g)) j σ c y

theorem phi_smul {M : Model l K} (a : (dat Amp).Ch M) (j : ℕ) (c : (per l K).A) (y : ((dat Amp).A a).N j) :
    (dat Amp).phiA a j (c • y) = (per l K).φ c • (dat Amp).phiA a j y :=
  GlueLim.hom_smul (M.phiS j) c y

theorem one_uniq {M : Model l K} (a : (dat Amp).Ch M) (x y : ((dat Amp).A a).N 0) :
    ((dat Amp).A a).one x → ((dat Amp).A a).one y → x = y :=
  GlueLim.one_uniq M.MS _ _ _ x y

theorem cup_uniq {M : Model l K} (a : (dat Amp).Ch M) {i j : ℕ} (x : ((dat Amp).A a).N i) (y : ((dat Amp).A a).N j)
    (z z' : ((dat Amp).A a).N (i + j)) : ((dat Amp).A a).cup x y z → ((dat Amp).A a).cup x y z' → z = z' :=
  GlueLim.cup_uniq M.MS _ _ _ x y z z'

theorem bil (M : Model l K) (n i j : ℕ) : ∃ b : (M.MS i).M n →ₗ[Acris l] (M.MS j).M n →ₗ[Acris l] (M.MS (i + j)).M n,
    ∀ x y, b x y = (CH.mulP (AcrEl M.P n)).cup rfl x y :=
  P.cup_bilin (CH.mulP (AcrEl M.P n)) rfl

theorem cup_smul {M : Model l K} (a : (dat Amp).Ch M) {i j : ℕ} (c c' : (per l K).A) (x : ((dat Amp).A a).N i)
    (y : ((dat Amp).A a).N j) (z : ((dat Amp).A a).N (i + j)) :
    ((dat Amp).A a).cup x y z → ((dat Amp).A a).cup (c • x) (c' • y) ((c * c') • z) :=
  GlueLim.cup_smul M.MS _ _ (fun n _ _ x y => (CH.mulP (AcrEl M.P n)).cup rfl x y) (bil M) c c' x y z

theorem first_chern_class_unique (hR : E.RIn l) (hU : E.FirstChernUniqueEtale) (hEt : ∀ M D, Amp M D → Etale D.f) {M : Model l K} (a : (dat Amp).Ch M)
    (x y : ((dat Amp).A a).N 2) : (dat Amp).c1A a x → (dat Amp).c1A a y → x = y := fun hx hy =>
  Subtype.ext (hU l hR (OK l K) M.X M.p (okToOC l K) a.1 (hEt M a.1 a.2) _ _ hx hy)

theorem red_cup (hC : B.CompatH l) (M : Model l K) (k : Bool) (n i j : ℕ) (x : (M.HS k i).M (n + 1)) (y : (M.HS k j).M (n + 1)) :
    (M.HS k (i + j)).r n ((CH.mulP (B.OcA (B.schFn M.p) (okToOC l K) k (n + 1))).cup rfl x y) =
      (CH.mulP (B.OcA (B.schFn M.p) (okToOC l K) k n)).cup rfl ((M.HS k i).r n x) ((M.HS k j).r n y) :=
  hC.cup (B.schFn M.p) (okToOC l K) k n.le_succ rfl x y

theorem cup_ex (hC : B.CompatH l) {M : Model l K} (a : (dat Amp).Ch M) {i j : ℕ} (x : ((dat Amp).H a).N i)
    (y : ((dat Amp).H a).N j) : ∃ z, ((dat Amp).H a).cup x y z :=
  GlueLim.cup_ex (M.HS false) _ _ (fun n _ _ x y => (CH.mulP (B.OcA (B.schFn M.p) (okToOC l K) false n)).cup rfl x y)
    (red_cup hC M false) x y

end GlueL'

theorem glueL : GlueL := fun _ _ _ Amp hC hR hU hEt hS =>
  { ch := GlueL'.ch Amp hS
    refine := fun M N u hu _ _ a b => GlueL'.refine Amp M N u hu a b
    act_smul := GlueL'.act_smul Amp
    phi_smul := GlueL'.phi_smul Amp
    one_uniq := GlueL'.one_uniq Amp
    cup_uniq := GlueL'.cup_uniq Amp
    cup_smul := GlueL'.cup_smul Amp
    first_chern_class_unique := GlueL'.first_chern_class_unique Amp hR hU hEt
    cup_ex := GlueL'.cup_ex Amp hC }

end CrystallineSemistableComparison
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DIsoDR0
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

abbrev Lim (r : Res l K) (M : Model l K) (j : ℕ) : Type 1 := (Wc.HS l (B.schFn M.p) r.ρ j).lim

def LimCup (r : Res l K) (M : Model l K) {i j n : ℕ} (h : i + j = n) (x : Lim r M i) (y : Lim r M j) (z : Lim r M n) : Prop :=
  ∀ m, z.1 m = (CH.mulP (Wc.OA l (B.schFn M.p) r.ρ m)).cup h (x.1 m) (y.1 m)

def toD (r : Res l K) (M : Model l K) (j : ℕ) (x : Lim r M j) : r.iso.D M j := (1 : Wc.K₀ l r.k) ⊗ₜ[WittVector l r.k] x

end CrystallineSemistableComparison.Pb
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.IsCrystallineChernClassLimit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

abbrev Res.Cup (r : Res l K) : Type 1 :=
  ∀ (M : Model l K) (i j : ℕ), r.iso.D M i →ₗ[Wc.K₀ l r.k] r.iso.D M j →ₗ[Wc.K₀ l r.k] r.iso.D M (i + j)

def Res.IsCup (r : Res l K) (μ : r.Cup) : Prop := ∀ (M : Model l K) (i j : ℕ) (x : Pb.Lim r M i) (y : Pb.Lim r M j),
  ∃ z, Pb.LimCup r M rfl x y z ∧ μ M i j (Pb.toD r M i x) (Pb.toD r M j y) = Pb.toD r M (i + j) z

def CupEx : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (r : Res l K), ∃ μ, r.IsCup μ

end CrystallineSemistableComparison
end
end

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison

theorem chapters_of (hP : BocksteinBaseChangeP) : Chapters :=
  { rin := fun l _ => R.forE l
    et := fun l _ K => E.etMap l K
    uniq := E.Main.firstChern_unique
    main := fun l _ => B.main l
    compat := fun l _ => B.compat l
    compatH := fun l _ => B.compatH l
    c1 := fun l _ => B.firstChern_compatible_l l
    p := hP }

theorem etSideS (h4 : GlobalTheory.EtC.E4) (h8 : GlobalTheory.EtC.E8) : EtSideS := fun l _ K _ => (etSide (zIn formalIn h4 h8) l K).1

theorem cstSmooth_of_p (hP : BocksteinBaseChangeP) (h : EtSideS) : CstSmooth :=
  cstSmooth_of_etSide glueL glueE glueB factsC resEx h (chapters_of hP)

end CrystallineSemistableComparison
