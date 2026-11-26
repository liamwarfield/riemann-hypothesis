module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinBaseChangeP
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.ExistsEpsPeriodTUnit
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.PrimOfOver
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.PropsA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.TowerSmulZero

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.AtlasOf
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.LimSurjFil
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison

namespace GlueBL

variable {R : Type} [CommRing R]

theorem lim_sq {A B C D : Sys.{1} R} {σ : R →+* R} (φ : Sys.Hom A B (RingHom.id R)) (ψ : Sys.Hom C D (RingHom.id R))
    (g : Sys.Hom A C σ) (g' : Sys.Hom B D σ) (h : ∀ n x, ψ.f n (g.f n x) = g'.f n (φ.f n x)) (x : A.lim) :
    ψ.lim (g.lim x) = g'.lim (φ.lim x) :=
  Subtype.ext (funext fun n => h n (x.1 n))

variable {Γ Γ' : Type} {S S' : ℕ → Sys.{1} R} {σ : Γ → R →+* R} {σ' : Γ' → R →+* R}
  {act : ∀ j g, Sys.Hom (S j) (S j) (σ g)} {act' : ∀ j g, Sys.Hom (S' j) (S' j) (σ' g)}
  {one : ∀ n, (S 0).M n} {one' : ∀ n, (S' 0).M n}
  {cup : ∀ n i j, (S i).M n → (S j).M n → (S (i + j)).M n} {cup' : ∀ n i j, (S' i).M n → (S' j).M n → (S' (i + j)).M n}

theorem lim_cup (φ : ∀ j, Sys.Hom (S j) (S' j) (RingHom.id R))
    (hc : ∀ n i j x y, (φ (i + j)).f n (cup n i j x y) = cup' n i j ((φ i).f n x) ((φ j).f n y))
    {i j : ℕ} (x : (limAlg S act one cup).N i) (y : (limAlg S act one cup).N j) (z : (limAlg S act one cup).N (i + j))
    (hz : (limAlg S act one cup).cup x y z) :
    (limAlg S' act' one' cup').cup ((φ i).lim x) ((φ j).lim y) ((φ (i + j)).lim z) := fun n =>
  (congrArg ((φ (i + j)).f n) (hz n)).trans (hc n i j _ _)

theorem lim_one (φ : ∀ j, Sys.Hom (S j) (S' j) (RingHom.id R)) (ho : ∀ n, (φ 0).f n (one n) = one' n)
    (x : (limAlg S act one cup).N 0) (hx : (limAlg S act one cup).one x) :
    (limAlg S' act' one' cup').one ((φ 0).lim x) := fun n =>
  (congrArg ((φ 0).f n) (hx n)).trans (ho n)

variable {A B : Sys.{1} R}

theorem lim_inj (φ : Sys.Hom A B (RingHom.id R)) (a u t : R) (N : ℕ) (ht : t = a * u) (h : ∀ n, UpTo (a ^ N) (φ.f n))
    (x : A.lim) (hx : φ.lim x = 0) : t ^ (2 * N) • x = 0 := by
  have h0 : (a ^ N) ^ 2 • x = 0 := (P.lim_upTo φ (a ^ N) h).1 x hx
  have e : t ^ (2 * N) = u ^ (2 * N) * (a ^ N) ^ 2 := by rw [ht]; ring
  rw [e, mul_smul, h0, smul_zero]

theorem lim_surj (φ : Sys.Hom A B (RingHom.id R)) (a u t : R) (N : ℕ) (ht : t = a * u) (h : ∀ n, UpTo (a ^ N) (φ.f n))
    (y : B.lim) : ∃ x, φ.lim x = t ^ (2 * N) • y :=
  Exists.elim ((P.lim_upTo φ (a ^ N) h).2 y) fun x hx =>
    ⟨u ^ (2 * N) • x, by rw [map_smul, hx, smul_smul, ht, mul_pow, mul_comm (a ^ (2 * N)), pow_mul' a]⟩

theorem lim_surj_fil (φ : Sys.Hom A B (RingHom.id R)) (a u t : R) (N : ℕ) (ht : t = a * u)
    (Fil : ∀ n, ℕ → Submodule R (A.M n)) (hsm : ∀ n r, ∀ x ∈ Fil n r, a • x ∈ Fil n (r + 1))
    (hinj : ∀ n x, φ.f n x = 0 → a ^ N • x = 0) (hs : ∀ n y, ∃ x ∈ Fil n N, φ.f n x = a ^ N • y)
    (y : B.lim) : ∃ x : A.lim, (∀ n, x.1 n ∈ Fil n (2 * N)) ∧ φ.lim x = t ^ (2 * N) • y := by
  choose xs hxs hβ using fun n => hs n (y.1 n)
  have hpow : ∀ n (k r : ℕ), ∀ x ∈ Fil n r, a ^ k • x ∈ Fil n (r + k) := by
    intro n k
    induction k with
    | zero => intro r x hx; simpa using hx
    | succ k ih =>
      intro r x hx
      rw [pow_succ', mul_smul, ← add_assoc]
      exact hsm n _ _ (ih r x hx)
  have hc : ∀ n, A.r n (a ^ N • xs (n + 1)) = a ^ N • xs n := by
    intro n
    have h0 : φ.f n (A.r n (xs (n + 1)) - xs n) = 0 := by
      rw [map_sub, ← φ.comm, hβ, hβ, map_smul, y.2 n]
      exact sub_self _
    have h1 := hinj n _ h0
    rw [smul_sub, sub_eq_zero] at h1
    rw [map_smul]
    exact h1
  refine ⟨⟨fun n => u ^ (2 * N) • a ^ N • xs n, fun n => by rw [map_smul, hc]⟩, fun n => ?_, ?_⟩
  · refine Submodule.smul_mem _ _ ?_
    have := hpow n N N (xs n) (hxs n)
    rwa [← two_mul] at this
  · refine Subtype.ext (funext fun n => ?_)
    change φ.f n (u ^ (2 * N) • a ^ N • xs n) = t ^ (2 * N) • y.1 n
    rw [map_smul, map_smul, hβ, smul_smul, smul_smul]
    congr 1
    rw [ht]
    ring

end GlueBL

end CrystallineSemistableComparison
end
end

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

namespace GlueB'

variable {l : ℕ} [Fact l.Prime]

def βS (hC : B.Compat l) {O : Type} [CommRing O] (F : B.Fn O) (κ : O →+* OC l) (k : Bool) (j : ℕ) :
    Sys.Hom (B.HcSys F κ k j) (MSys (F.pt κ) j) (RingHom.id _) where
  f n := B.β F κ k n j
  comm n x := (hC.red F κ k n.le_succ j x).symm

variable {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem atlas_of {M : Model l K} (h : M.Sm) : ∃ d, Nonempty ((B.schFn M.p).Atlas d) := by
  obtain ⟨hG, hS⟩ := h
  have hP := AdicGeo.proper_p hG
  exact B.P.atlas M.p

variable (Amp : ∀ M : Model l K, E.LineData M.X → Prop)

def bβ (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (j : ℕ) :
    ((dat Amp).H a).N j →ₗ[(per l K).A] ((dat Amp).A a).N j :=
  (βS hC (B.schFn M.p) (okToOC l K) false j).lim

def bβ' (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (j : ℕ) :
    ((dat Amp).H' a).N j →ₗ[(per l K).A] ((dat Amp).A a).N j :=
  (βS hC (B.schFn M.p) (okToOC l K) true j).lim

theorem f_inj (hMain : B.Main l) (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (hM : M.Sm) (j : ℕ) :
    ∃ n : ℕ, ∀ x, bβ Amp hC a j x = 0 → (per l K).t ^ n • x = 0 := by
  obtain ⟨d, ⟨A⟩⟩ := atlas_of hM
  obtain ⟨ε, u, -, ht⟩ := GlueBE.exists_eps_period_t_unit l K
  obtain ⟨N, hN⟩ := hMain d j
  exact ⟨2 * N, fun x hx => GlueBL.lim_inj (βS hC (B.schFn M.p) (okToOC l K) false j) ε.μ u (per l K).t N ht
    (fun n => (hN (B.schFn M.p) (okToOC l K) ε A n).1 false) x hx⟩

theorem f_inj' (hMain : B.Main l) (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (hM : M.Sm) (j : ℕ) :
    ∃ n : ℕ, ∀ x, bβ' Amp hC a j x = 0 → (per l K).t ^ n • x = 0 := by
  obtain ⟨d, ⟨A⟩⟩ := atlas_of hM
  obtain ⟨ε, u, -, ht⟩ := GlueBE.exists_eps_period_t_unit l K
  obtain ⟨N, hN⟩ := hMain d j
  exact ⟨2 * N, fun x hx => GlueBL.lim_inj (βS hC (B.schFn M.p) (okToOC l K) true j) ε.μ u (per l K).t N ht
    (fun n => (hN (B.schFn M.p) (okToOC l K) ε A n).1 true) x hx⟩

theorem f_surj' (hMain : B.Main l) (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (hM : M.Sm) (j : ℕ) :
    ∃ n : ℕ, ∀ y, ∃ x, bβ' Amp hC a j x = (per l K).t ^ n • y := by
  obtain ⟨d, ⟨A⟩⟩ := atlas_of hM
  obtain ⟨ε, u, -, ht⟩ := GlueBE.exists_eps_period_t_unit l K
  obtain ⟨N, hN⟩ := hMain d j
  exact ⟨2 * N, fun y => GlueBL.lim_surj (βS hC (B.schFn M.p) (okToOC l K) true j) ε.μ u (per l K).t N ht
    (fun n => (hN (B.schFn M.p) (okToOC l K) ε A n).1 true) y⟩

theorem f_surj (hMain : B.Main l) (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (hM : M.Sm) (j : ℕ) :
    ∃ n : ℕ, ∀ y, ∃ x, (dat Amp).fil a j n x ∧ bβ Amp hC a j x = (per l K).t ^ n • y := by
  obtain ⟨d, ⟨A⟩⟩ := atlas_of hM
  obtain ⟨ε, u, -, ht⟩ := GlueBE.exists_eps_period_t_unit l K
  obtain ⟨N, hN⟩ := hMain d j
  refine ⟨2 * N, fun y => ?_⟩
  obtain ⟨x, hx, hxy⟩ := GlueBL.lim_surj_fil (βS hC (B.schFn M.p) (okToOC l K) false j) ε.μ u (per l K).t N ht
    (fun n r => B.HcFil (B.schFn M.p) (okToOC l K) false n r j)
    (fun n r x hx => hC.smul_fil (B.schFn M.p) (okToOC l K) false n r j ε.μ (ε.μ_mem false (PAlg.base l) n) x hx)
    (fun n x hx => ((hN (B.schFn M.p) (okToOC l K) ε A n).1 false).1 x hx)
    (fun n y => (hN (B.schFn M.p) (okToOC l K) ε A n).2 y) y
  exact ⟨x, hx, hxy⟩

end GlueB'

end CrystallineSemistableComparison
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.EtaleMapFirstChern
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

namespace GlueE

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem kill_acr (P : PAlg l ⥤ Type) (n : ℕ) (T : El P) (x : (CH.modF (AcrEl P n)).obj T) :
    ((l : Acris l) ^ n) • x = 0 :=
  modF_smul (AcrEl P n) _ (fun T => show algebraMap (Acris l) (((elπ P).obj T).Acr n) ((l : Acris l) ^ n) = 0 by
    rw [map_pow, map_natCast]; exact ((elπ P).obj T).pow_l_acr n) T x

theorem kill_MS (P : PAlg l ⥤ Type) (n j : ℕ) (x : (MSys P j).M n) : ((l : Acris l) ^ n) • x = 0 :=
  tower_smul_zero (fun n => CH.modF (AcrEl P n)) (fun n => redEl P n.le_succ) j n _ (fun T y => kill_acr P n T y) x

variable (e : E.EtFam l K) (he : e.Red)

def eMap (M : Model l K) (j : ℕ) : M.T j →+ (M.MS j).lim where
  toFun v := ⟨fun n => e M n j (v.lev n), fun n => (he M n j _).trans (congrArg (e M n j) (v.2 n))⟩
  map_zero' := Subtype.ext (funext fun n => map_zero (e M n j))
  map_add' v w := Subtype.ext (funext fun n => map_add (e M n j) (v.lev n) (w.lev n))

theorem eMap_lin_lev (M : Model l K) (j : ℕ) (f : ℤ_[l] →+* Acris l) (z : ℤ_[l]) (v : M.T j) (n : ℕ) :
    (eMap e he M j (z • v)).1 n = f z • (eMap e he M j v).1 n :=
  ((congrArg (e M n j) (GlobalTheory.EtC.HtL.smul_eq l n n le_rfl M.spc j 0 z (v.1 n))).trans
    (map_nsmul (e M n j) _ _)).trans (padic_smul f n ((eMap e he M j v).1 n) (kill_MS M.P n j _) z).symm

theorem eMap_lin (M : Model l K) (j : ℕ) (f : ℤ_[l] →+* Acris l) (z : ℤ_[l]) (v : M.T j) :
    eMap e he M j (z • v) = f z • eMap e he M j v :=
  lim_ext fun n => (eMap_lin_lev e he M j f z v n).trans (lim_smul_val _ _ _ n).symm

theorem eMap_act (hq : e.Equi) (M : Model l K) (j : ℕ) (σ : Gal(PadicAlgCl l/K)) (v : M.T j) :
    eMap e he M j (GlobalTheory.EtC.galHl l (PadicAlgCl l) M.q j 0 σ v) = (M.galS j σ).lim (eMap e he M j v) :=
  lim_ext fun n => hq M n j σ (v.lev n)

theorem eMap_phi (hp : e.Phi) (M : Model l K) (j : ℕ) (v : M.T j) :
    (M.phiS j).lim (eMap e he M j v) = eMap e he M j v :=
  lim_ext fun n => hp M n j (v.lev n)

theorem eMap_nat (hn : e.Natu) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (j : ℕ) (v : N.T j) :
    eMap e he M j (Model.pullT u hu j v) = (Model.pullS u hu j).lim (eMap e he N j v) :=
  lim_ext fun n => hn M N u hu n j (v.lev n)

theorem eMap_cup (hc : e.Cup) (M : Model l K) {i j : ℕ} (x : M.T i) (y : M.T j) (z : M.T (i + j)) (h : M.CupT x y z)
    (n : ℕ) : (eMap e he M (i + j) z).1 n = (CH.mulP (AcrEl M.P n)).cup rfl ((eMap e he M i x).1 n) ((eMap e he M j y).1 n) :=
  (congrArg (e M n (i + j)) (h n)).trans (hc M n i j (x.lev n) (y.lev n))

theorem eMap_one (ho : e.One) (M : Model l K) : ∃ v : M.T 0, ∀ n, (eMap e he M 0 v).1 n = CH.oneH (AcrEl M.P n) :=
  (ho M).elim fun v hv => ⟨v, hv⟩

theorem etale_map_first_chern (h1 : e.C1) (M : Model l K) (D : E.LineData M.X) (c : Acris l)
    (hc : c = ACris.periodT (untilt_epsilon (p := l))) :
    ∃ v : M.T 2, E.IsFirstChernClassOfLineBundle M.p (okToOC l K) D (c • eMap e he M 2 v).1 := by
  subst hc
  exact (h1 M D).elim fun v hv => ⟨v, by rw [lim_smul_fun]; exact hv⟩

def emap (Amp : ∀ M : Model l K, E.LineData M.X → Prop) (e : E.EtFam l K) (he : e.Good) : EMap Model.Sm (dat Amp) where
  e {M} _ j := eMap e he.red M j
  lin {M} _ _ j z v := eMap_lin e he.red M j (per l K).z z v
  act {M} _ _ j _ v := eMap_act e he.red he.equi M j _ v
  phi {M} _ _ j v := eMap_phi e he.red he.phi M j v
  nat {_ _ u hu _ _} _ _ _ j v := eMap_nat e he.red he.nat u hu j v
  cup {M} _ _ _ _ x y z h := eMap_cup e he.red he.cup M x y z h
  one {M} _ _ := eMap_one e he.red he.one M
  c1 {M} a _ := etale_map_first_chern e he.red he.c1 M a.1 (per l K).t rfl

end GlueE

theorem glueE : GlueE := fun _ _ _ Amp hE => hE.elim fun e he => ⟨GlueE.emap Amp e he⟩

end CrystallineSemistableComparison
end
end
