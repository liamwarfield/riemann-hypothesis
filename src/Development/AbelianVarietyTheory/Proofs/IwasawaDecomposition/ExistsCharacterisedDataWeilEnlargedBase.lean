module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamSubgroupTransposeGramUnitaryDecomposes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormFieldSquareClass
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodCharactersExtendedDataEqMapSmallerData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormGroupsModelsActionsMeasuresBasesCharacterise
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleWeilDatumVectorPolynomialMapEnlarg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProductLevelEqOfLocalAgreement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleRationalFormLiftsAlgebraicEnlarged
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

namespace GlobalTheory.Mem.R3.Rw.RatExt

open Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Mem.R3.Rw.LiftExt

private theorem comb_gen {E E' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E'] (Y : HMod E) (X : HMod E')
    (g : Y.H →ₗ[ℂ] X.H) (hinj : Function.Injective Y.e) (v : Y.H) {n : ℕ} (s : Fin n → ℂ) (u : Fin n → Y.H)
    (hv : HEq (Y.e v) (∑ k, s k • Y.e (u k))) (p : Fin n → X.H) (hp : ∀ k, HEq (p k) (g (u k))) : ∑ k, s k • p k = g v := by
  have e : v = ∑ k, s k • u k := hinj (by rw [eq_of_heq hv, map_sum]; simp only [map_smul])
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [map_smul, eq_of_heq (hp k)]

section Comparison₂

variable {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'}
  {V W : HSp a.D} {V' W' : HSp a'.D} {S : a.D.what₂.Tau → SPar} {S' : a'.D.what₂.Tau → SPar} {M : DSModel W S} {M' : DSModel W' S'}

private theorem comb_of (hP : B'.toPre = B.toPre) (hV : HEq V' V) (hW : HEq W' W) (h : DSTie M' M) {c : CoefA V} {c' : CoefA V'}
    (c1 : HEq c'.W c.W) (c2 : HEq c'.ρ c.ρ) (c3 : HEq c'.nW c.nW) (c4 : HEq c'.iW c.iW)
    {Y : HMod (Bridge.Gf V → c.W)} {Y' : HMod (Bridge.Gf V' → c'.W)} (hY : HEq Y' Y)
    {X : HMod (MMap M)} {X' : HMod (MMap M')} (hX : HEq X' X) {g : Y.H →ₗ[ℂ] X.H} {g' : Y'.H →ₗ[ℂ] X'.H} (hg : HEq g' g)
    (hinj : Function.Injective Y.e) (v : Y'.H) {n : ℕ} (s : Fin n → ℂ) (u : Fin n → Y.H)
    (hv : HEq (Y'.e v) (∑ k, s k • Y.e (u k))) (p : Fin n → X'.H) (hp : ∀ k, HEq (p k) (g (u k))) : ∑ k, s k • p k = g' v := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (W')) ((by with_unfolding_all exact ((W) :))) (W') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (W')) (W') (((W))) (((hW)))).symm : _))
  clear (hW)
  subst e))
  obtain ⟨H', s', l', ε', f', _, _, _, _⟩ := M'
  rename_i n' i' _ _ _ _
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  dsimp only at h1 h2 h3 h4 h5 h6 h7
  ( (
  have e : @Eq (type_of% (H')) ((by with_unfolding_all exact ((M.H) :))) (H') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (H')) (H') (((M.H))) (((h1)))).symm : _))
  clear (h1)
  subst e))
  ( (
  have e : @Eq (type_of% (n')) ((by with_unfolding_all exact ((M.nacg) :))) (n') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (n')) (n') (((M.nacg))) (((h2)))).symm : _))
  clear (h2)
  subst e))
  ( (
  have e : @Eq (type_of% (i')) ((by with_unfolding_all exact ((M.ips) :))) (i') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (i')) (i') (((M.ips))) (((h3)))).symm : _))
  clear (h3)
  subst e))
  ( (
  have e : @Eq (type_of% (s')) ((by with_unfolding_all exact ((M.σ) :))) (s') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (s')) (s') (((M.σ))) (((h4)))).symm : _))
  clear (h4)
  subst e))
  ( (
  have e : @Eq (type_of% (l')) ((by with_unfolding_all exact ((M.lam) :))) (l') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (l')) (l') (((M.lam))) (((h5)))).symm : _))
  clear (h5)
  subst e))
  ( (
  have e : @Eq (type_of% (ε')) ((by with_unfolding_all exact ((M.ε) :))) (ε') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (ε')) (ε') (((M.ε))) (((h6)))).symm : _))
  clear (h6)
  subst e))
  ( (
  have e : @Eq (type_of% (f')) ((by with_unfolding_all exact ((M.fr) :))) (f') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (f')) (f') (((M.fr))) (((h7)))).symm : _))
  clear (h7)
  subst e))
  ( (
  have e : @Eq (type_of% (V')) ((by with_unfolding_all exact ((V) :))) (V') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (V')) (V') (((V))) (((hV)))).symm : _))
  clear (hV)
  subst e))
  obtain ⟨W₁, ρ₁⟩ := c'
  rename_i nW' iW' _
  dsimp only at c1 c2 c3 c4
  ( (
  have e : @Eq (type_of% (W₁)) ((by with_unfolding_all exact ((c.W) :))) (W₁) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (W₁)) (W₁) (((c.W))) (((c1)))).symm : _))
  clear (c1)
  subst e))
  ( (
  have e : @Eq (type_of% (nW')) ((by with_unfolding_all exact ((c.nW) :))) (nW') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (nW')) (nW') (((c.nW))) (((c3)))).symm : _))
  clear (c3)
  subst e))
  ( (
  have e : @Eq (type_of% (iW')) ((by with_unfolding_all exact ((c.iW) :))) (iW') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (iW')) (iW') (((c.iW))) (((c4)))).symm : _))
  clear (c4)
  subst e))
  ( (
  have e : @Eq (type_of% (ρ₁)) ((by with_unfolding_all exact ((c.ρ) :))) (ρ₁) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (ρ₁)) (ρ₁) (((c.ρ))) (((c2)))).symm : _))
  clear (c2)
  subst e))
  ( (
  have e : @Eq (type_of% (Y')) ((by with_unfolding_all exact ((Y) :))) (Y') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (Y')) (Y') (((Y))) (((hY)))).symm : _))
  clear (hY)
  subst e))
  ( (
  have e : @Eq (type_of% (X')) ((by with_unfolding_all exact ((X) :))) (X') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (X')) (X') (((X))) (((hX)))).symm : _))
  clear (hX)
  subst e))
  ( (
  have e : @Eq (type_of% (g')) ((by with_unfolding_all exact ((g) :))) (g') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (g')) (g') (((g))) (((hg)))).symm : _))
  clear (hg)
  subst e))
  exact (by with_unfolding_all exact ((comb_gen Y X g hinj ((v)) s u ((hv)) ((p)) ((hp))) : _))

end Comparison₂

private theorem apply_eq {m m' : ℕ} (hm : m' = m) {F : Fin m → ℕ} {F' : Fin m' → ℕ} (hF : HEq F' F) {i : Fin m} {i' : Fin m'}
    (h : (i : ℕ) = i') : F i = F' i' := by
  subst hm
  obtain rfl := eq_of_heq hF
  obtain rfl : i = i' := Fin.ext h
  rfl

section Fields

variable {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'}
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 T0 Pl0' T0' : Type}
  {A : FamIn a.D.what₂.LL G Pl0 T0 a.D.R.m} {A' : FamIn a'.D.what₂.LL G' Pl0' T0' a'.D.R.m}
  {Ks Ks' : Type} [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' a'.D.what₂.LL]
  {R : RealDat a.D A Ks} {R' : RealDat a'.D A' Ks'}


set_option maxHeartbeats 1000000 in
private theorem rat_of (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i') {t : T0} {t' : T0'}
    (c1 : HEq (R'.cV i').W (R.cV i).W) (c2 : HEq (R'.cV i').ρ (R.cV i).ρ) (c3 : HEq (R'.cV i').nW (R.cV i).nW)
    (c4 : HEq (R'.cV i').iW (R.cV i).iW)
    (hM : DSTie (R'.MW i' a'.D.what₂.embLL) (R.MW i a.D.what₂.embLL)) (hHW : HEq (R'.HW i' a'.D.what₂.embLL) (R.HW i a.D.what₂.embLL))
    (hHV : HEq (R'.HV i' t') (R.HV i t)) (hg : HEq (R'.thG i' t') (R.thG i t)) (hn : HEq R'.nW R.nW)
    (ι : a.D.what₂.LL →+* a'.D.what₂.LL) (hι : ∀ x, a'.D.what₂.embLL (ι x) = a.D.what₂.embLL x)
    (hj : ∀ (σ' : a'.D.what₂.LL →+* ℂ) x x', CrdOver ι x x' → HEq ((R'.FW i').j σ' x') ((R.FW i).j (σ'.comp ι) x))
    (hinj : Function.Injective (R.HV i t).e) (hjV : ∀ x, (R.HV i t).e (R.jV i t x) = R.B.jL i t x) (hr : RatAt R t)
    (x' : A'.fam.amb.FL i' t') {n : ℕ} (b : Fin n → a'.D.what₂.LL) (x : Fin n → A.fam.amb.FL i t)
    (hx : HEq (R'.B.jL i' t' x') (∑ k, a'.D.what₂.embLL (b k) • R.B.jL i t (x k)))
    (v : (R'.HV i' t').H) (hv : (R'.HV i' t').e v = R'.B.jL i' t' x') :
    ∃ y, (R'.FW i').j (sg0 a'.D A') y = R'.thG i' t' v := by
  have s : a.D.what₂.embLL = sg0 a.D A := (sgAt_mk _ R.hv0).symm
  have s' : a'.D.what₂.embLL = sg0 a'.D A' := (sgAt_mk _ R'.hv0).symm
  have hM0 : DSTie (R'.MW i' (sg0 a'.D A')) (R.MW i (sg0 a.D A)) := s ▸ s' ▸ hM
  have hHW0 : HEq (R'.HW i' (sg0 a'.D A')) (R.HW i (sg0 a.D A)) := s ▸ s' ▸ hHW
  have hc : (sg0 a'.D A').comp ι = sg0 a.D A := by
    rw [← s, ← s']; exact RingHom.ext hι
  have hmv : ∀ (σ₁ σ₂ : a.D.what₂.LL →+* ℂ), σ₁ = σ₂ → ∀ y, HEq ((R.FW i).j σ₁ y) ((R.FW i).j σ₂ y) := by
    intro σ₁ σ₂ e y; subst e; exact HEq.rfl
  have hn0 : R.nW i = R'.nW i' := apply_eq (LiftExt.m_eq hP) hn h
  choose y hy using fun k => hr i (x k) (R.jV i t (x k)) (hjV (x k))
  refine ⟨∑ k, b k • GeoFW.crdMap ι hn0 (y k), ?_⟩
  refine ((map_sum _ _ _).trans (Finset.sum_congr rfl fun k _ => LinearMap.map_smulₛₗ _ _ _)).trans ?_
  refine comb_of hP (vc_heq hP h) (wc_heq hP h) hM0 c1 c2 c3 c4 hHV hHW0 hg hinj v (fun k => sg0 a'.D A' (b k))
    (fun k => R.jV i t (x k)) ?_ (fun k => (R'.FW i').j (sg0 a'.D A') (GeoFW.crdMap ι hn0 (y k))) fun k => ?_
  · refine (heq_of_eq hv).trans (hx.trans (heq_of_eq ?_))
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (by with_unfolding_all exact ((congrArg₂ (fun (c : ℂ) (q : Bridge.Gf (Vc a.D i) → (R.cV i).W) => c • q) (DFunLike.congr_fun s' (b k)) (hjV (x k)).symm) :))
  · exact ((hj _ _ _ (GeoFW.crdOver_crdMap ι hn0 (y k))).trans (hmv _ _ hc _)).trans (heq_of_eq (hy k))

end Fields

end GlobalTheory.Mem.R3.Rw.RatExt

set_option maxHeartbeats 4000000 in
theorem _root_.GlobalTheory.T.referenceTuple_rationalForm_lifts_algebraic_enlarged : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → RSide z Wt' R' → JSpan z Wt' R' → RatAt z.R.toRealDat (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) → RatAt R'.toRealDat (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hS hJ hr i' x' v hv
  letI := z.alg
  have hP : B'.toPre = B.toPre := hE.1
  have hm := LiftExt.m_eq (a := Z) (a' := Z') hP
  let i : Fin (w.st Z).toD7.R.m := Fin.cast hm i'
  have h : (i : ℕ) = i' := rfl
  let ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL :=
    (B'.embLL.rangeRestrictFieldEquiv.symm : B'.embLL.fieldRange →+* B'.LL).comp
      (B.embLL.codRestrict B'.embLL.fieldRange fun x => hE.2.2.2 ⟨x, rfl⟩)
  have hι : ∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x := fun x =>
    congrArg Subtype.val (B'.embLL.rangeRestrictFieldEquiv.apply_symm_apply ⟨B.embLL x, hE.2.2.2 ⟨x, rfl⟩⟩)
  obtain ⟨⟨-, -, -, -, -, hn, -, -, -, -, -, -, h1, -⟩, h2⟩ := hS
  obtain ⟨c1, c2, c3, c4, -, -, -, m1, m2, m3, m4, m5, m6, m7, -, hHW, -, -, hWι⟩ := h1 i i' h
  obtain ⟨-, -, hHV, -, hg, -, -⟩ := h2 i i' h
  obtain ⟨n, b, x, hx⟩ := hJ i i' h x'
  have hb := z.pins.char.base.models
  exact RatExt.rat_of (a := Z) (a' := Z') (R := z.R.toRealDat) (R' := R'.toRealDat) hP h c1 c2 c3 c4
    ⟨m1, m2, m3, m4, m5, m6, m7⟩ hHW hHV hg hn ι hι (fun σ' => ((hWι ι hι).1 σ').2.2.2) (hb.HV i _).1 (hb.jV i _) hr x' b x hx v hv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalDefiniteFormsLargerFieldCombinationSmall
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

namespace GlobalTheory.Mem.R3.Rw.JSpanPf

private theorem span_of_bc {K L : Type} [Field K] [NumberField K] [StarRing K] [Field L] [NumberField L] [StarRing L] {ι : K →+* L}
    {S : Formalism.L2.Col.GSD K} {S' : Formalism.L2.Col.GSD L} (b : Formalism.L2.Col.GSDBC ι S S') {M M' : Type} [AddCommGroup M'] [Module L M']
    (r : S.EqFun → M) (r' : S'.EqFun ≃ₗ[L] M') (c : L →+* ℂ) {α α' U U' : Type} (n : NormedAddCommGroup U)
    (n' : NormedAddCommGroup U') (ip : InnerProductSpace ℂ U) (ip' : InnerProductSpace ℂ U') (hα : α' = α) (hU : U' = U)
    (hn : HEq n' n) (hip : HEq ip' ip) (j : M → α → U) (j' : M' →ₛₗ[c] (α' → U'))
    (h : ∀ φ, HEq (j' (r' (b.lift φ))) (j (r φ))) (x' : M') :
    ∃ (m : ℕ) (a : Fin m → L) (x : Fin m → M), HEq (j' x') (∑ k, c (a k) • j (x k)) := by
  subst hα hU
  cases hn
  cases hip
  obtain ⟨F⟩ := Formalism.L2.Col.CoefFrame.nonempty ι
  obtain ⟨φ', rfl⟩ := r'.surjective x'
  obtain ⟨m, a, g, hg⟩ := Submodule.mem_span_set'.1 (b.mem_span_lift F φ')
  choose ψ hψ using fun k => (g k).2
  refine ⟨m, a, fun k => r (ψ k), heq_of_eq ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hg, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, LinearMap.map_smulₛₗ, ← hψ k, eq_of_heq (h (ψ k))]


set_option maxHeartbeats 4000000 in
private theorem exists_bc {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T)
    (w' : ColW B' f' T') (Wt : Set B.places.Pl) (Wt' : Set B'.places.Pl) (hE : Enl0 B B') (hf : HEq f' f) (hpx : HEq w'.px w.px)
    (k k' : ℕ) (hk : k' = k) (φ : B.LL →+* B'.LL) (hφ : ∀ x, B'.embLL (φ x) = B.embLL x) :
    ∃ b : Formalism.L2.Col.GSDBC φ (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 k)
      (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 k'),
      ∀ (ψ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 k).EqFun) d d', HEq d' d →
        HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((b.lift ψ).1 d').1)
          (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (ψ.1 d).1) := by
  subst hk
  obtain ⟨hpre, -, -, -⟩ := hE
  cases B with | mk P₁ =>
  cases B' with | mk P₂ =>
  dsimp only at hpre
  subst hpre
  have hpx' : w'.px = w.px := eq_of_heq hpx
  have hv : (Base.primes (baseOfColW w') w'.px).vGs = (Base.primes (baseOfColW w) w.px).vGs := by
    rw [hpx']
    rfl
  have hφ' : ∀ x, (baseOfColW w').embLL (φ x) = (baseOfColW w).embLL x := hφ
  have hC : w'.I.C = w.I.C := w'.C_eq.trans ((eq_of_heq hf).trans w.C_eq.symm)
  refine GlobalTheory.Mem.R3.DefLatBC.gsdbc_round_reidx (baseOfColW w).fields φ (baseOfColW w').tauLL ?_ _ ?_ _ _ ?_ (baseOfColW w).embLL
    (baseOfColW w').embLL hφ
  · intro τ
    ext x
    apply (baseOfColW w').embLL.injective
    have h1 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w) τ)
    have h2 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w') τ)
    simp only [Formalism.L2.Col.Fields.embC, RingHom.comp_apply] at h1 h2
    exact (hφ' _).trans (h1.trans h2.symm)
  · exact (rowLevelPrimes_colTuples_eq_vGs w' _).trans (hv.trans (rowLevelPrimes_colTuples_eq_vGs w Wt).symm)
  · refine glue_inv_coefMap_of_empty φ (twistRamifiedPrimes_empty_colTuples w Wt) (twistRamifiedPrimes_empty_colTuples w' _) _ _ _ _ ?_
    intro p hp
    refine levKV_coefMap_of φ p.1 (fun s => w.I.Ch.chi s p) (fun s => w'.I.Ch.chi s ⟨p.1, hp⟩) ?_ _ _ _ _
    intro s c
    apply (baseOfColW w').embLL.injective
    rw [hφ']
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (c : 𝓞 (baseOfColW w).fields.E ⧸ p.1.asIdeal)
    have hy0 : ((y : 𝓞 (baseOfColW w).fields.E) : (baseOfColW w).fields.E) ≠ 0 := by
      intro h0
      have h0' : y = 0 := RingOfIntegers.coe_injective (h0.trans (by simp))
      rw [h0', map_zero] at hy
      exact c.ne_zero hy.symm
    have e1 := GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi w' s ⟨p.1, hp⟩ c y (Units.mk0 _ hy0) rfl hy.symm
    have e2 := GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi w s p c y (Units.mk0 _ hy0) rfl hy.symm
    rw [hC] at e1
    exact e1.trans e2.symm


set_option maxHeartbeats 2000000 in
private theorem gf_eq {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
    {w' : ColW B' f' T'} (Z : w.Lt) (Z' : w'.Lt) (h : B'.toPre = B.toPre) (i : Fin (w.st Z).toD7.R.m)
    (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    (↥(Bridge.Gf (Vc (w'.st Z').toD7 i')) : Type) = ↥(Bridge.Gf (Vc (w.st Z).toD7 i)) := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at h
  subst h
  have e0 : i = i' := Fin.ext hi
  subst e0
  rfl

end GlobalTheory.Mem.R3.Rw.JSpanPf

set_option maxHeartbeats 4000000 in
theorem _root_.GlobalTheory.T.rationalDefiniteForms_largerField_combination_smallerField : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq f' f → HEq w'.px w.px → RSideW z Wt' R' → JSpan z Wt' R' := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hf hpx hRS i i' hii x'
  obtain ⟨ι, hι⟩ := exists_iota_comp B.embLL B'.embLL hE.2.2.2
  obtain ⟨b, hb⟩ := GlobalTheory.Mem.R3.Rw.JSpanPf.exists_bc w w' Wt Wt' hE hf hpx ((i : ℕ) + 1) ((i' : ℕ) + 1) (by rw [hii]) ι hι
  have hj := fun φ => hRS.2.2.2.2.2.2.2.2.2.2.2.2.2 i i' hii (Formalism.L2.Col.mtKOk _ _ _ _ hX _) (Formalism.L2.Col.mtKOk _ _ _ _ hX' _) φ
    (b.lift φ) (hb φ)
  have hc := hRS.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hii
  have key := GlobalTheory.Mem.R3.Rw.JSpanPf.span_of_bc b
    (fun φ => (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).res (Formalism.L2.Col.mtKOk _ _ _ _ hX _) φ)
    ((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk _ _ _ _ hX' _))
    B'.embLL (z.R.cV i).nW (R'.cV i').nW (z.R.cV i).iW (R'.cV i').iW (GlobalTheory.Mem.R3.Rw.JSpanPf.gf_eq Z Z' hE.1 i i' hii)
    (eq_of_heq hc.1) hc.2.2.1 hc.2.2.2.1
    (fun x => z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ((by with_unfolding_all exact (x :))))
    ((by with_unfolding_all exact (R'.B.jL i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) :))) ((by with_unfolding_all exact (hj :))) ((by with_unfolding_all exact (x' :)))
  exact (by with_unfolding_all exact (key :))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodIdempotentCoefficientsAgreeEnlargedBase
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodIdempotentCoefficientsAgreeEnlargedBase
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

namespace GlobalTheory.Mem.R3.Rw.WeilExt


set_option maxHeartbeats 2000000 in
theorem idemSame_of_keep : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq f' f → HEq w'.px w.px → GrpTrue Z.N f → GrpTrue Z'.N f' → RSideW z Wt' R' →
  ∀ cG : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd, Keep R'.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).lv2 cG → IdemSame z Xg := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hf hp hG hG' hR cG hK g' g hg
  obtain ⟨-, -, -, -, -, -, -, -, -, hPg, heG, -⟩ := hR
  have hB := hE.1
  cases B
  cases B'
  dsimp only at hB
  subst hB
  cases hf
  have hpx : w'.px = w.px := eq_of_heq hp
  cases w'
  dsimp only at hpx
  subst hpx
  cases hg
  obtain ⟨plg, iso, hpl, hid, -, hbc⟩ := z.pins.keep.grp
  obtain ⟨plg2, iso', hpl', hid', -, hbc'⟩ := hK.grp
  refine (hid' g).trans (Eq.trans ?_ (hid g).symm)
  refine Eq.trans ?_ (TypesTrue.typeIdempotent_coeff_across_layers hG hG' ((z.R.eG.trans z.cG) g))
  congr 1
  funext kv'
  obtain ⟨k, v'⟩ := kv'
  obtain ⟨v, rfl⟩ : ∃ v, v' = plEquiv Z.N.naut Z'.N.naut k v := ⟨_, (Equiv.apply_symm_apply _ v').symm⟩
  show _ = ((z.R.eG.trans z.cG) g) ⟨k, (plEquiv Z.N.naut Z'.N.naut k).symm (plEquiv Z.N.naut Z'.N.naut k v)⟩
  rw [Equiv.symm_apply_apply]
  have hP : R'.Pg = z.R.Pg := eq_of_heq hPg
  have hQ : (plg2 ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩).1 = (plg ⟨k, v⟩).1 := by
    rw [hpl', hpl]
    exact TypesTrue.plGw_plEquiv hG hG' k v
  exact GlobalTheory.Mem.R3.DefLatBC.bc_eq_of_heq hP z.R.eG R'.eG heG g _ _ hQ (iso ⟨k, v⟩)
    (iso' ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩) _ _ (hbc g ⟨k, v⟩) (hbc' g ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩)

end GlobalTheory.Mem.R3.Rw.WeilExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodIdempotentCoefficientsAgreeEnlargedBaseStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodIdempotent_coefficients_agree_enlarged_base : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq f' f → HEq w'.px w.px → GrpTrue Z.N f → GrpTrue Z'.N f' → RSideW z Wt' R' →
  ∀ cG : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd, Keep R'.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).lv2 cG → IdemSame z Xg := by
  first | exact @GlobalTheory.Mem.R3.Rw.WeilExt.idemSame_of_keep | exact GlobalTheory.Mem.R3.Rw.WeilExt.idemSame_of_keep | (intros; apply GlobalTheory.Mem.R3.Rw.WeilExt.idemSame_of_keep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteGroupCharacterEqProductResidualCharactersE
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteGroupCharacterEqProductResidualCharactersE
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

namespace GlobalTheory.Mem.R3.Rw.ChiWExt

section Move

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt}

theorem m_eq (hP : B'.toPre = B.toPre) : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  exact (by with_unfolding_all exact ((Eq.refl (w.st Z).toD7.R.m) :))

theorem gc_eq (hP : B'.toPre = B.toPre) {px : PreX B.toPre} {px' : PreX B'.toPre} (hpx : HEq px' px) : Gc B' px' = Gc B px := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (px')) ((by with_unfolding_all exact ((px) :))) (px') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (px')) (px') (((px))) (((hpx)))).symm : _))
  clear (hpx)
  subst e))
  exact (by with_unfolding_all exact ((Eq.refl (Gc B px)) :))

theorem prod_move (hP : B'.toPre = B.toPre) {px : PreX B.toPre} {px' : PreX B'.toPre} (hpx : HEq px' px)
    {Pg : Finset (Pl (w.st Z).toD7.host.E)} {Pg' : Finset (Pl (w'.st Z').toD7.host.E)} (hPg : HEq Pg' Pg)
    {eG : Gc B px ≃* G0 Pg (w.st Z).toD7.R.r} {eG' : Gc B' px' ≃* G0 Pg' (w'.st Z').toD7.R.r} (heG : HEq eG' eG)
    {χ : ∀ PP : Pl (w.st Z).toD7.host.E, (kP PP)ˣ →* ℂˣ} {χ' : ∀ PP : Pl (w'.st Z').toD7.host.E, (kP PP)ˣ →* ℂˣ}
    (hχ : ∀ PP' PP, HEq PP' PP → PP ∈ Pg → HEq (χ' PP') (χ PP)) {g : Gc B px} {g' : Gc B' px'} (hg : HEq g' g) :
    ∏ PP : Pg', ((χ' PP (Matrix.GeneralLinearGroup.det (eG' g' PP)) : ℂˣ) : ℂ) =
      ∏ PP : Pg, ((χ PP (Matrix.GeneralLinearGroup.det (eG g PP)) : ℂˣ) : ℂ) := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (px')) ((by with_unfolding_all exact ((px) :))) (px') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (px')) (px') (((px))) (((hpx)))).symm : _))
  clear (hpx)
  subst e))
  ( (
  have e : @Eq (type_of% (Pg')) ((by with_unfolding_all exact ((Pg) :))) (Pg') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (Pg')) (Pg') (((Pg))) (((hPg)))).symm : _))
  clear (hPg)
  subst e))
  ( (
  have e : @Eq (type_of% (eG')) ((by with_unfolding_all exact ((eG) :))) (eG') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (eG')) (eG') (((eG))) (((heG)))).symm : _))
  clear (heG)
  subst e))
  ( (
  have e : @Eq (type_of% (g')) ((by with_unfolding_all exact ((g) :))) (g') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (g')) (g') (((g))) (((hg)))).symm : _))
  clear (hg)
  subst e))
  have e : ∀ PP : Pl (w.st Z).toD7.host.E, PP ∈ Pg → HEq (χ' ((by with_unfolding_all exact (PP :)))) (χ PP) :=
    fun PP hm => hχ ((by with_unfolding_all exact (PP :))) PP ((by with_unfolding_all exact ((HEq.refl PP) :))) hm
  refine Finset.prod_congr rfl fun PP _ => ?_
  exact congrArg (fun c : ℂˣ => (c : ℂ)) (DFunLike.congr_fun (eq_of_heq (e PP.1 PP.2)) _)

end Move


set_option maxHeartbeats 1000000 in
theorem grp_chiW_ext : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq w'.px w.px → RSideW z Wt' R' → LevSame z Wt' R' → R'.toRealDat.grp_chiW := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hpx hS hL
  have hc := z.pins.char.base.grp.chiW
  let ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL :=
    (B'.embLL.rangeRestrictFieldEquiv.symm : B'.embLL.fieldRange →+* B'.LL).comp
      (B.embLL.codRestrict B'.embLL.fieldRange fun x => hE.2.2.2 ⟨x, rfl⟩)
  have hι : ∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x := fun x =>
    congrArg Subtype.val (B'.embLL.rangeRestrictFieldEquiv.apply_symm_apply ⟨B.embLL x, hE.2.2.2 ⟨x, rfl⟩⟩)
  intro i' g'
  have hm := m_eq (w := w) (w' := w') (Z := Z) (Z' := Z') hE.1
  let i : Fin (w.st Z).toD7.R.m := ⟨i', by have := i'.2; omega⟩
  have hi : (i : ℕ) = i' := rfl
  let g : Gc B w.px := cast (gc_eq hE.1 hpx) g'
  have hg : HEq g' g := (cast_heq _ _).symm
  have hS' := hS
  obtain ⟨-, -, -, -, -, -, -, -, -, hPg, heG, -, hW, -⟩ := hS'
  have hWi := hW i i' hi
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hWι⟩ := hWi
  have hch := (hWι ι hι).2.2.1 g' g hg
  rw [hch, hι, hc i g]
  exact (prod_move hE.1 hpx hPg heG (fun PP' PP h hm => (hL.1 i i' hi).2 PP' PP h hm) hg).symm

end GlobalTheory.Mem.R3.Rw.ChiWExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteGroupCharacterEqProductResidualCharactersEStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteGroupCharacter_eq_product_residualCharacters_enlarged : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq w'.px w.px → RSideW z Wt' R' → LevSame z Wt' R' → R'.toRealDat.grp_chiW := by
  first | exact @GlobalTheory.Mem.R3.Rw.ChiWExt.grp_chiW_ext | exact GlobalTheory.Mem.R3.Rw.ChiWExt.grp_chiW_ext | (intros; apply GlobalTheory.Mem.R3.Rw.ChiWExt.grp_chiW_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCopiesReferenceObjectsOverEnlargedBase
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

namespace GlobalTheory.Mem.R3.Rw.WeilExt.RefType

private abbrev MM {Tau : Type} {n : ℕ} (H : Tau → Type) (na : ∀ τ, NormedAddCommGroup (H τ)) (ip : ∀ τ, InnerProductSpace ℂ (H τ))
    (σ : ∀ τ, Matrix (Fin n) (Fin n) ℂ → (H τ →L[ℂ] H τ)) (fr : Tau → Matrix (Fin n) (Fin n) ℂ)
    (lie : Tau → Set (Matrix (Fin n) (Fin n) ℂ)) (X : Type) : Type :=
  MultilinearMap (RingHom.id ℂ) (fun τ : Tau => (Submodule.span ℂ {w | SmoothVec (lie τ) (fun g => σ τ (fr τ * g * (fr τ)⁻¹)) w} : Submodule ℂ (H τ)))
    (X → ℂ)

private theorem core {Tau Tau' : Type} {n n' : ℕ} {H : Tau → Type} {na : ∀ τ, NormedAddCommGroup (H τ)} {ip : ∀ τ, InnerProductSpace ℂ (H τ)}
    {σ : ∀ τ, Matrix (Fin n) (Fin n) ℂ → (H τ →L[ℂ] H τ)} {fr : Tau → Matrix (Fin n) (Fin n) ℂ}
    {lie : Tau → Set (Matrix (Fin n) (Fin n) ℂ)} {X : Type}
    {H' : Tau' → Type} {na' : ∀ τ, NormedAddCommGroup (H' τ)} {ip' : ∀ τ, InnerProductSpace ℂ (H' τ)}
    {σ' : ∀ τ, Matrix (Fin n') (Fin n') ℂ → (H' τ →L[ℂ] H' τ)} {fr' : Tau' → Matrix (Fin n') (Fin n') ℂ}
    {lie' : Tau' → Set (Matrix (Fin n') (Fin n') ℂ)} {X' : Type}
    {G G' C C' : Type} {nc : NormedAddCommGroup C} {ic : InnerProductSpace ℂ C} {nc' : NormedAddCommGroup C'} {ic' : InnerProductSpace ℂ C'}
    {HW : HMod (MM H na ip σ fr lie X)} {HW' : HMod (MM H' na' ip' σ' fr' lie' X')}
    (hT : Tau' = Tau) (hn : n' = n) (hlie : HEq lie' lie) (hX : X' = X) (hG : G' = G)
    (hC : HEq C' C) (hnc : HEq nc' nc) (hic : HEq ic' ic)
    (hH : HEq H' H) (hna : HEq na' na) (hip : HEq ip' ip) (hσ : HEq σ' σ) (hfr : HEq fr' fr) (hHW : HEq HW' HW)
    (K : HMod (G → C)) (th : K.H →ₗ[ℂ] MM H na ip σ fr lie X) (g : K.H →ₗ[ℂ] HW.H) :
    ∃ (K' : HMod (G' → C')) (th' : K'.H →ₗ[ℂ] MM H' na' ip' σ' fr' lie' X') (g' : K'.H →ₗ[ℂ] HW'.H),
      HEq K' K ∧ HEq th' th ∧ HEq g' g := by
  subst hT hn hX hG
  cases hlie; cases hC; cases hnc; cases hic; cases hH; cases hna; cases hip; cases hσ; cases hfr; cases hHW
  exact ⟨K, th, g, HEq.rfl, HEq.rfl, HEq.rfl⟩

private theorem mid {D D' : D7} {V W : HSp D} {V' W' : HSp D'} {L L' : Type} {S : L → D.what₂.Tau → SPar} {S' : L' → D'.what₂.Tau → SPar}
    (c : CoefA V) (c' : CoefA V') (M : ∀ s, Formalism.IndefR.Mult.DSModel W (S s)) (M' : ∀ s, Formalism.IndefR.Mult.DSModel W' (S' s))
    (HW : ∀ s, HMod (Formalism.IndefR.Mult.MMap (M s))) (HW' : ∀ s, HMod (Formalism.IndefR.Mult.MMap (M' s)))
    {s t : L} {s' t' : L'} (e : t = s) (e' : t' = s')
    (hT : D'.what₂.Tau = D.what₂.Tau) (hn : W'.rank = W.rank) (hlie : HEq (lieAt W') (lieAt W)) (hX : GA D' W' = GA D W)
    (hG : (Bridge.Gf V' : Type) = Bridge.Gf V)
    (hC : HEq c'.W c.W) (hnc : HEq c'.nW c.nW) (hic : HEq c'.iW c.iW)
    (hH : HEq (M' s').H (M s).H) (hna : HEq (M' s').nacg (M s).nacg) (hip : HEq (M' s').ips (M s).ips) (hσ : HEq (M' s').σ (M s).σ)
    (hfr : HEq (M' s').fr (M s).fr) (hHW : HEq (HW' s') (HW s))
    (K : HMod (Bridge.Gf V → c.W)) (th : K.H →ₗ[ℂ] Formalism.IndefR.Mult.MMap (M t)) (g : K.H →ₗ[ℂ] (HW t).H) :
    ∃ (K' : HMod (Bridge.Gf V' → c'.W)) (th' : K'.H →ₗ[ℂ] Formalism.IndefR.Mult.MMap (M' t')) (g' : K'.H →ₗ[ℂ] (HW' t').H),
      HEq K' K ∧ HEq th' th ∧ HEq g' g := by
  subst e e'
  exact core (lie := lieAt W) (lie' := lieAt W') (X := GA D W) (X' := GA D' W') (HW := HW t) (HW' := HW' t')
    hT hn hlie hX hG hC hnc hic hH hna hip hσ hfr hHW K th g

private theorem types (X X' : Stages) (h : X'.B.toPre = X.B.toPre) (i : Fin X.toD7.R.m) (i' : Fin X'.toD7.R.m) (hi : (i : ℕ) = i') :
    X'.toD7.what₂.Tau = X.toD7.what₂.Tau ∧ (Wc X'.toD7 i').rank = (Wc X.toD7 i).rank ∧ HEq (lieAt (Wc X'.toD7 i')) (lieAt (Wc X.toD7 i)) ∧
    GA X'.toD7 (Wc X'.toD7 i') = GA X.toD7 (Wc X.toD7 i) ∧ (Bridge.Gf (Vc X'.toD7 i') : Type) = Bridge.Gf (Vc X.toD7 i) ∧
    (GA X.toD7 (Vc X.toD7 i) × GA X.toD7 (Wc X.toD7 i) →* Module.End ℂ (Formalism.IndefR.Datum.WO (Vc X.toD7 i) (Wc X.toD7 i) → ℂ)) =
      (GA X'.toD7 (Vc X'.toD7 i') × GA X'.toD7 (Wc X'.toD7 i') →* Module.End ℂ (Formalism.IndefR.Datum.WO (Vc X'.toD7 i') (Wc X'.toD7 i') → ℂ)) ∧
    (Formalism.IndefR.Datum.WO (Vc X.toD7 i) (Wc X.toD7 i) → ℂ) = (Formalism.IndefR.Datum.WO (Vc X'.toD7 i') (Wc X'.toD7 i') → ℂ) ∧
    Measure (GA X.toD7 (Vc X.toD7 i)) = Measure (GA X'.toD7 (Vc X'.toD7 i')) ∧
    Set (GA X.toD7 (Vc X.toD7 i)) = Set (GA X'.toD7 (Vc X'.toD7 i')) := by
  obtain ⟨B, C, W, V, S, N, G⟩ := X
  obtain ⟨B', C', W', V', S', N', G'⟩ := X'
  cases B
  cases B'
  dsimp only at h
  subst h
  obtain ⟨i, hlt⟩ := i
  obtain ⟨i', hlt'⟩ := i'
  dsimp only at hi
  subst hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end GlobalTheory.Mem.R3.Rw.WeilExt.RefType

open GlobalTheory.Mem.R3.Rw.WeilExt.RefType in
set_option maxHeartbeats 4000000 in
theorem _root_.GlobalTheory.T.exists_copies_reference_objects_over_enlarged_base : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → RSideW z Wt' R' → ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
  ∃ (ω : GA (w'.st Z').toD7 (Vc (w'.st Z').toD7 i') × GA (w'.st Z').toD7 (Wc (w'.st Z').toD7 i') →* Module.End ℂ (Formalism.IndefR.Datum.WO (Vc (w'.st Z').toD7 i') (Wc (w'.st Z').toD7 i') → ℂ))
    (v : Formalism.IndefR.Datum.WO (Vc (w'.st Z').toD7 i') (Wc (w'.st Z').toD7 i') → ℂ) (H : HMod (Bridge.Gf (Vc (w'.st Z').toD7 i') → (R'.cV i').W))
    (th : H.H →ₗ[ℂ] Formalism.IndefR.Mult.MMap (R'.MW i' (sg0 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A))) (g : H.H →ₗ[ℂ] (R'.HW i' (sg0 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A)).H)
    (ν : Measure (GA (w'.st Z').toD7 (Vc (w'.st Z').toD7 i'))) (fd : Set (GA (w'.st Z').toD7 (Vc (w'.st Z').toD7 i'))),
    HEq ω (z.R.ωP i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq v (z.R.vP i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq H (z.R.HV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq th (z.R.thF i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq g (z.R.thG i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq ν (z.R.νV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq fd (z.R.fdV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hR i i' hi
  have hR' := hR.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hi
  obtain ⟨hC, -, hnc, hic, -, -, -, hH, hna, hip, hσ, -, -, hfr, -, hHW, -⟩ := hR'
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := types (w.st Z) (w'.st Z') hE.1 i i' hi
  have key := mid (z.R.cV i) (R'.cV i') (z.R.MW i) (R'.MW i') (z.R.HW i) (R'.HW i')
    (sgAt_mk _ z.R.hv0) (sgAt_mk _ R'.hv0) t1 t2 t3 t4 t5 hC hnc hic hH hna hip hσ hfr hHW
    (z.R.HV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) (z.R.thF i _) (z.R.thG i _)
  obtain ⟨K, th, g, h1, h2, h3⟩ := key
  exact ⟨cast t6 (z.R.ωP i _), cast t7 (z.R.vP i _), K, th, g, cast t8 (z.R.νV i _), cast t9 (z.R.fdV i _), cast_heq _ _, cast_heq _ _,
    h1, h2, h3, cast_heq _ _, cast_heq _ _⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharacterisedDataWeilEnlargedBase
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.WeilExt

theorem stepW_host_rank (p : WP) :
    StepW p fun _ B _ _ _ => ∀ X : Stages, X.B.toPre = B.toPre →
      HostHyp X.toD7 ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV :=
  Step.of_evG (((evG_of_ev GlobalTheory.Mem.StdSize.vstd_size_ev).inter (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)).imp
    fun _ _ _ _ _ H _ _ _ hO _ _ _ _ _ X e => ⟨(H.2 X (e ▸ hO)).1, (H.1 X (e ▸ hO)).2⟩)

theorem isIdG_of_heq (X : Stages) {px : PreX X.B.toPre} {Pg Pg' : Finset (Pl X.toD7.host.E)} (e : Gc X.B px ≃* G0 Pg X.toD7.R.r)
    (e' : Gc X.B px ≃* G0 Pg' X.toD7.R.r) (hP : Pg = Pg') (h : HEq e e') (h' : IsPlacewiseIdentity X (px := px) e') : IsPlacewiseIdentity X (px := px) e := by
  subst hP
  obtain rfl := eq_of_heq h
  exact h'

theorem trans_eq_of_heq (X : Stages) {px : PreX X.B.toPre} {Pg Pg' : Finset (Pl X.toD7.host.E)} (e : Gc X.B px ≃* G0 Pg X.toD7.R.r)
    (e' : Gc X.B px ≃* G0 Pg' X.toD7.R.r) (c : G0 Pg X.toD7.R.r ≃* G0g X.toD7.nd) (c' : G0 Pg' X.toD7.R.r ≃* G0g X.toD7.nd)
    (hP : Pg = Pg') (h : HEq e e') (hc : HEq c c') : e.trans c = e'.trans c' := by
  subst hP
  obtain rfl := eq_of_heq h
  obtain rfl := eq_of_heq hc
  rfl

section

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL]
  {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}

theorem m_eq (hE : Enl0 B B') : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m :=
  show B'.toPre.R.m = B.toPre.R.m from congrArg (fun P => P.R.m) hE.1


set_option maxHeartbeats 2000000 in
theorem exists_rSide (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
    (R₀ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) (hE : Enl0 B B') (h : RSideW z Wt' R₀) :
    ∃ HV νV fdV ωP vP thF thG, RSide z Wt' (⟨updM R₀.toRealDat R₀.HX HV R₀.HE R₀.gE R₀.jX (fun _ _ => 0) R₀.νY R₀.fdY R₀.ν0 R₀.fd0
      R₀.νX R₀.fdX νV fdV ωP vP thF thG, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ :
      RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) := by
  have key := fun i' : Fin (w'.st Z').toD7.R.m => GlobalTheory.T.exists_copies_reference_objects_over_enlarged_base z Wt' R₀ hE h (Fin.cast (m_eq hE) i') i' rfl
  choose ω v H th g ν fd k using key
  refine ⟨fun i _ => H i, fun i _ => ν i, fun i _ => fd i, fun i _ => ω i, fun i _ => v i, fun i _ => th i, fun i _ => g i, ?_, ?_⟩
  · exact (by with_unfolding_all exact (h :))
  · intro i i' e
    have e' : i = Fin.cast (m_eq hE) i' := Fin.ext e
    subst e'
    exact (by with_unfolding_all exact (k i' :))

end


set_option maxHeartbeats 8000000 in
theorem exists_pins_rSide : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr₀ : TrI B' w'.px)
        (R₀ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀) core'.Q.c.F)
        (cG : G0 R₀.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R₀.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₀.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R₀.eG.trans cG) Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R₀.mu R₀.twPl ∧
        IdemClass (D := (w'.st Z').toD7) (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).A ∧ R₀.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 ∧ R₀.IsInert ∧ R₀.IsTup ∧
        R₀.AllPlaces ∧ Keep R₀.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 cG ∧ BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀ R₀.toRealDat ∧
        RSideW z {v | B'.places.resChar v ∈ T'.pl} R₀ →
        ∃ (tr : TrI B' w'.px)
        (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr) core'.Q.c.F)
        (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr) cG' ∧
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R'.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R'.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R'.eG.trans cG') Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R'.mu R'.twPl ∧
        BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr R'.toRealDat ∧ R'.toRealDat.ExAt ∧ RSide z {v | B'.places.resChar v ∈ T'.pl} R') := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine (stepW_host_rank Pinned).trans (StepW.of_all ?_)
  intro K B' f' T' w' _ _ H B f T w hE hf _ hpx Z hX Wt z hG _ hFine hHolds Z' hX' hG' _ _ core' alg' _ _ _ _ _ _ _ _
  intro Xg tr₀ R₀ cG hyp
  obtain ⟨hLev, hId, hGood, hMu, hIdem, hPre, hIn, hTup, hAll, hKeep, hBrg, hSide⟩ := hyp
  letI := alg'
  generalize {v | B'.places.resChar v ∈ T'.pl} = Wt' at *
  have hHH := (H (w'.st Z') rfl).1
  have hn := (H (w.st Z) hE.1.symm).2
  obtain ⟨HV, νV, fdV, ωP, vP, thF, thG, hS⟩ := exists_rSide z Wt' R₀ hE hSide
  generalize hR₁ : (⟨updM R₀.toRealDat R₀.HX HV R₀.HE R₀.gE R₀.jX (fun _ _ => 0) R₀.νY R₀.fdY R₀.ν0 R₀.fd0
      R₀.νX R₀.fdX νV fdV ωP vP thF thG, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ :
      RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr₀) core'.Q.c.F) = R₁ at hS
  have move : ∃ cG₁ : G0 R₁.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd,
      LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R₁.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₁.eG ∧
      GoodSet (w'.st Z') (px := w'.px) (R₁.eG.trans cG₁) Xg ∧ MuOf (w'.st Z') w'.I T' Wt' R₁.mu R₁.twPl ∧
      R₁.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr₀).lv2 ∧ R₁.IsInert ∧ R₁.IsTup ∧ R₁.AllPlaces ∧
      Keep R₁.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr₀).lv2 cG₁ ∧
      BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr₀ R₁.toRealDat := by
    subst hR₁
    exact ⟨cG, hLev, hId, hGood, hMu, realDatum_prerequisites_update_models hPre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
      ⟨hIn.tie, hIn.onto, hIn.hR, hIn.hL, hIn.SF⟩, ⟨hTup.mu_off, hTup.mu_used, hTup.mu_ne, hTup.mu_conj, hTup.mu_on⟩, hAll,
      ⟨hKeep.std, hKeep.signs, hKeep.frames, hKeep.beta, hKeep.prX, hKeep.grp, hKeep.psi, hKeep.guard, hKeep.valKs, hKeep.frameKs,
        hKeep.levKs⟩, hBrg⟩
  clear hR₁ hLev hId hGood hMu hPre hIn hTup hAll hKeep hBrg hSide
  obtain ⟨cG₁, hLev, hId, hGood, hMu, hPre, hIn, hTup, hAll, hKeep, hBrg⟩ := move
  have hL := GlobalTheory.T.liftCharacters_agree_over_enlarged_base z Wt' R₁ hE hf hpx hLev
  have hI := GlobalTheory.T.goodIdempotent_coefficients_agree_enlarged_base z Wt' R₁ hE hf hpx hG hG' hS.1 cG₁ hKeep
  have hz := ratAt_of_geo z.R z.F z.pins.char hFine.1 hn z.geo hFine.2.1 hHolds.unif
  obtain ⟨tr, R, cG', hPins, hEx, hLevEq, hEG, hCG, hmu, htw, hBrg', hS', hSame⟩ :=
    charW_keep (w'.st Z') w'.px w'.I hX' (usedOf w'.I T' Wt') Xg tr₀ core'.Q.c.F R₁ cG₁ (GlobalTheory.T.linksAnalyticHypotheses_of_weilRep_harishChandra h5 h6 h7 h3 _) hIdem
      (fun R hP hc ht => GlobalTheory.ExAtAssembly.exAt_holds h1 h2 h3 h4 _ _ _ _ _ _ R hP.1.lev hP.1.fam hP.2 hP.1.record hHH hc ht)
      (fun R => RSideW z Wt' (⟨R, R₁.plI, R₁.SF, R₁.phs, R₁.lam3⟩ :
        RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr₀) core'.Q.c.F))
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s => (by with_unfolding_all exact (s :))) (fun _ _ _ _ _ _ _ _ _ _ _ _ s => (by with_unfolding_all exact (s :)))
      (fun _ _ _ s => (by with_unfolding_all exact (s :))) ((by with_unfolding_all exact (hS.1 :))) hPre hIn hTup hAll hKeep hBrg
      (GlobalTheory.T.finiteGroupCharacter_eq_product_residualCharacters_enlarged z Wt' R₁ hE hpx hS.1 hL) (GlobalTheory.T.modW_of_rSideW z Wt' R₁ hE hpx hS.1) (GlobalTheory.T.referenceTuple_weilDatum_vector_polynomialMap_enlarged z Wt' R₁ hE hFine.1 hS hL)
      (GlobalTheory.T.referenceTuple_hilbertModel_definiteForms_enlarged z Wt' R₁ hE hPre hS hL) (GlobalTheory.T.thetaLift_at_reference_tuple_over_enlarged_base z Wt' R₁ hE hpx hFine.1 hS hI)
      (GlobalTheory.T.referenceTuple_rationalForm_lifts_algebraic_enlarged z Wt' R₁ hE hS (GlobalTheory.T.rationalDefiniteForms_largerField_combination_smallerField z Wt' R₁ hE hf hpx hS.1) hz)
  have hPg : R.Pg = R₁.Pg := congrArg LevCh.Pg hLevEq
  refine ⟨tr, R, cG', hPins, hLevEq ▸ hLev, isIdG_of_heq _ R.eG R₁.eG hPg hEG hId, ?_, ?_, hBrg', hEx, ?_, fun i i' e => ?_⟩
  · rw [trans_eq_of_heq _ R.eG R₁.eG cG' cG₁ hPg hEG hCG]; exact hGood
  · rw [hmu, htw]; exact hMu
  · exact (by with_unfolding_all exact (hS' :))
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hS.2 i i' e
    obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := hSame i'
    exact ⟨(heq_of_eq b1).trans a1, (heq_of_eq b2).trans a2, b3.trans a3, b4.trans a4, b5.trans a5, (heq_of_eq b6).trans a6,
      (heq_of_eq b7).trans a7⟩

end GlobalTheory.Mem.R3.Rw.WeilExt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharacterisedDataWeilEnlargedBaseStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_characterisedData_weil_enlargedBase : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr₀ : TrI B' w'.px)
        (R₀ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀) core'.Q.c.F)
        (cG : G0 R₀.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R₀.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₀.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R₀.eG.trans cG) Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R₀.mu R₀.twPl ∧
        IdemClass (D := (w'.st Z').toD7) (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).A ∧ R₀.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 ∧ R₀.IsInert ∧ R₀.IsTup ∧
        R₀.AllPlaces ∧ Keep R₀.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 cG ∧ BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀ R₀.toRealDat ∧
        RSideW z {v | B'.places.resChar v ∈ T'.pl} R₀ →
        ∃ (tr : TrI B' w'.px)
        (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr) core'.Q.c.F)
        (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr) cG' ∧
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R'.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R'.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R'.eG.trans cG') Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R'.mu R'.twPl ∧
        BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr R'.toRealDat ∧ R'.toRealDat.ExAt ∧ RSide z {v | B'.places.resChar v ∈ T'.pl} R') := by
  exact @GlobalTheory.Mem.R3.Rw.WeilExt.exists_pins_rSide
end
