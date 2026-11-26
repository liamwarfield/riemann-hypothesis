module

public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ActGeneratorZero
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBMapPf
public import Development.WeilBound.CoreStatements.HodgeTatePoints.CdLocal
public import Development.WeilBound.CoreStatements.HodgeTatePoints.CdFrame

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.EqMulInversePow
section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.CompListProd
noncomputable section
namespace PositivityTheory.Xgn.GermSystem.Bc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr

theorem spMap_cp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem comp_listProd {X0 : Scheme.{0}} {G T T' : Over X0} [GrpObj G] (ρ : T' ⟶ T) (l : List (T ⟶ G)) :
    ρ ≫ l.prod = (l.map (ρ ≫ ·)).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [MonObj.comp_mul, ih]

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S S₂ : Type} [CommRing S] [CommRing S₂] (f : S →+* S₂) (x : Sp S ⟶ X0)

theorem comb_iff {V : Type} [AddCommGroup V] [Module S V] (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G x V) {n : ℕ} (b : Fin n → V)
    (a : Fin n → S) (w : Sp (DualNumber S) ⟶ t.G.left) :
    IsCombAtG t x (fun l => (M.pt (b l)).left) a w ↔ (M.pt (∑ i, a i • b i)).left = w := by
  have h0 : M.pt 0 = 1 := by
    have := M.add 0 0
    rw [add_zero] at this
    simpa using this
  let φ : Multiplicative V →* (tEpsG x ⟶ t.G) :=
    { toFun := fun v => M.pt v.toAdd, map_one' := h0, map_mul' := fun u v => M.add _ _ }
  have hs : M.pt (∑ i, a i • b i) = (List.ofFn fun i => M.pt (a i • b i)).prod := by
    have := map_prod φ (fun i => Multiplicative.ofAdd (a i • b i)) Finset.univ
    rw [List.prod_ofFn]
    rw [← ofAdd_sum] at this
    exact this
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : u = fun i => M.pt (a i • b i) := funext fun i => Over.OverMorphism.ext ((hu i).trans (M.smul _ _).symm)
    rw [hs, this]
  · rintro rfl
    exact ⟨fun i => M.pt (a i • b i), fun i => M.smul _ _, by rw [hs]⟩

def epsBC : tEpsG (spMap f ≫ x) ⟶ tEpsG x :=
  Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap f)) (by
    change spMap _ ≫ spMap _ ≫ x = spMap _ ≫ spMap f ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_cp, spMap_cp]
    congr 2
    ext s <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl])

theorem comb_bc {n : ℕ} {v : Fin n → (Sp (DualNumber S) ⟶ t.G.left)} {a : Fin n → S}
    {w : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x v a w) :
    IsCombAtG t (spMap f ≫ x) (fun i => spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ v i) (fun i => f (a i))
      (spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  refine ⟨fun i => epsBC f x ≫ u i, fun i => ?_, ?_⟩
  · change spMap _ ≫ (u i).left = _
    rw [hu, ← Category.assoc, ← Category.assoc, spMap_cp, spMap_cp]
    congr 2
    refine RingHom.ext fun s => ?_
    ext <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, epsMul, GlobalTheory.CompanionTheory.Ar.epsMul, mul_comm]
  · have := comp_listProd (epsBC f x) (List.ofFn u)
    rw [List.map_ofFn] at this
    exact (congrArg (fun q => q.left) this).symm

theorem tan_bc {v : Sp (DualNumber S) ⟶ t.G.left} (h : IsTanAtG t x v) :
    IsTanAtG t (spMap f ≫ x) (spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ v) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h.1]
    exact Over.w (epsBC f x)
  · have e : spMap (TrivSqZeroExt.fstHom S₂ S₂ S₂).toRingHom ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) =
        spMap f ≫ spMap (TrivSqZeroExt.fstHom S S S).toRingHom := by
      rw [spMap_cp, spMap_cp]
      congr 1
      refine RingHom.ext fun s => ?_
      simp [GlobalTheory.CompanionTheory.Ar.dualMap]
    rw [← Category.assoc, e, Category.assoc, h.2]
    exact congrArg (fun q => q.left)
      (MonObj.comp_one (M := t.G) (Over.homMk (spMap f) rfl : Over.mk (spMap f ≫ x) ⟶ Over.mk x))

theorem basis_bc {n : ℕ} {tg : Fin n → (Sp (DualNumber S) ⟶ t.G.left)} (ht : ∀ l, IsTanAtG t x (tg l))
    (hb : ∀ w, IsTanAtG t x w → ∃! a : Fin n → S, IsCombAtG t x tg a w) (w : Sp (DualNumber S₂) ⟶ t.G.left)
    (hw : IsTanAtG t (spMap f ≫ x) w) :
    ∃! a : Fin n → S₂, IsCombAtG t (spMap f ≫ x) (fun i => spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ tg i) a w := by
  letI : Algebra S S₂ := f.toAlgebra
  obtain ⟨V, _, _, ⟨M⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists X0 t.G S x
  obtain ⟨V', _, _, ⟨M'⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists X0 t.G S₂ (spMap f ≫ x)
  obtain ⟨j, hj, -, hbs⟩ := PositivityTheory.HtPt.Htat.lie_bc X0 t.G S S₂ x V V' M M'
  choose b hb' using fun l => M.onto (Over.homMk (tg l) (ht l).1) (ht l).2
  have htg : tg = fun l => (M.pt (b l)).left := funext fun l => by rw [hb']; rfl
  have hu : ∀ v : V, ∃! a : Fin n → S, ∑ i, a i • b i = v := fun v => by
    obtain ⟨a, ha, hau⟩ := hb (M.pt v).left ⟨Over.w (M.pt v), M.tan v⟩
    rw [htg, comb_iff] at ha
    refine ⟨a, M.inj (Over.OverMorphism.ext ha), fun a' ha' => hau a' ?_⟩
    beta_reduce
    rw [htg, comb_iff, ha']
  have hli : LinearIndependent S b := Fintype.linearIndependent_iff.2 fun a ha i =>
    congrFun ((hu 0).unique (y₁ := a) (y₂ := 0) ha (by simp)) i
  have hsp : ⊤ ≤ Submodule.span S (Set.range b) := fun v _ => by
    obtain ⟨a, rfl, -⟩ := hu v
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨hli', hsp'⟩ := hbs t.semi.smooth n (Module.Basis.mk hli hsp)
  simp only [Module.Basis.mk_apply] at hli' hsp'
  have htg' : (fun i => spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ tg i) = fun l => (M'.pt (j (b l))).left :=
    funext fun l => by
      rw [hj, htg]
  obtain ⟨v, hv⟩ := M'.onto (Over.homMk w hw.1) hw.2
  have hvw : (M'.pt v).left = w := by rw [hv]; rfl
  let B := Module.Basis.mk hli' hsp'.ge
  have hB : ∀ i, j (b i) = B i := fun i => by simp [B]
  refine ⟨B.equivFun v, ?_, fun a ha => ?_⟩
  · beta_reduce
    rw [htg', comb_iff]
    simp only [hB, Module.Basis.sum_equivFun, hvw]
  · rw [htg', comb_iff, ← hvw] at ha
    have := M'.inj (Over.OverMorphism.ext ha)
    simp only [hB] at this
    rw [← this, ← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

def cO (κ : Type) (m : ℕ) : overAt (spMap f ≫ x) (Jet S₂ κ m) ⟶ overAt x (Jet S κ m) :=
  Over.homMk (spMap (jetCoef f κ m)) (by
    change spMap _ ≫ spMap _ ≫ x = spMap _ ≫ spMap f ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_cp, spMap_cp, jetCoef_alg])

theorem sq_of {κ κ' : Type} {m m' : ℕ} (α : Jet S κ m →ₐ[S] Jet S κ' m') (β : Jet S₂ κ m →ₐ[S₂] Jet S₂ κ' m')
    (h : (jetCoef f κ' m').comp (α : Jet S κ m →+* Jet S κ' m') =
      (β : Jet S₂ κ m →+* Jet S₂ κ' m').comp (jetCoef f κ m)) :
    homAt (spMap f ≫ x) β ≫ cO f x κ m = cO f x κ' m' ≫ homAt x α := by
  apply Over.OverMorphism.ext
  change spMap _ ≫ spMap _ = spMap _ ≫ spMap _
  rw [spMap_cp, spMap_cp, h]

theorem sq_subst {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (φ' : κ → MvPolynomial κ' S₂)
    (h : ∀ i, φ' i = MvPolynomial.map f (φ i)) :
    homAt (spMap f ≫ x) (jetSubstP m φ') ≫ cO f x κ m = cO f x κ' m ≫ homAt x (jetSubstP m φ) := by
  obtain rfl : φ' = _ := funext h
  apply sq_of
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom, jetSubstP,
      jetMap_mk, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, jetCoef_mk, MvPolynomial.map_C]
  · intro i
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom, jetSubstP,
      jetMap_mk, MvPolynomial.aeval_X, jetCoef_mk, MvPolynomial.map_X]
    rw [map_sub (MvPolynomial.map f), MvPolynomial.map_C, MvPolynomial.constantCoeff_map]

variable {d : ℕ} (y : ∀ m, jOG x d m 1 ⟶ t.G)

def yBC (m : ℕ) : jOG (spMap f ≫ x) d m 1 ⟶ t.G := cO f x _ m ≫ y m

theorem jpt_bc {n : ℕ} (m : ℕ) (i : Fin n) :
    jptG t (spMap f ≫ x) d (yBC t f x y) m i = cO f x _ m ≫ jptG t x d y m i := by
  rw [jptG, jptG, yBC, ← Category.assoc, sq_of f x _ _ (jetCoef_copy f d m n i), Category.assoc]

theorem chart_bc {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
    {tg : Fin d → (Sp (DualNumber S) ⟶ t.G.left)} (h : IsChartG t x d F act tg (fun l j => if l = j then 1 else 0) y) :
    IsChartG t (spMap f ≫ x) d (fun i => MvPowerSeries.map f (F i)) (fun a i => MvPowerSeries.map f (act a i))
      (fun l => spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ tg l) (fun l j => if l = j then 1 else 0) (yBC t f x y) := by
  refine { zero := ?zero, trunc := ?trunc, law := ?law, act := ?act, tan := ?tan, basis := ?basis }
  case zero =>
    intro m
    let ρ : overAt (spMap f ≫ x) S₂ ⟶ overAt x S := Over.homMk (spMap f) (by
      change spMap _ ≫ spMap _ ≫ x = spMap _ ≫ spMap f ≫ x
      rw [spMap_alg_self, spMap_alg_self, Category.id_comp, Category.id_comp])
    have e : homAt (spMap f ≫ x) (jetAug : Jet S₂ (Fin 1 × Fin d) m →ₐ[S₂] S₂) ≫ cO f x _ m =
        ρ ≫ homAt x (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) := by
      apply Over.OverMorphism.ext
      change spMap _ ≫ spMap _ = spMap _ ≫ spMap _
      rw [spMap_cp, spMap_cp, jetCoef_aug]
    rw [yBC, ← Category.assoc, e, Category.assoc, h.zero, MonObj.comp_one]
  case trunc =>
    intro m
    rw [yBC, yBC, ← Category.assoc, sq_of f x _ _ (jetCoef_trunc f _ m).symm, Category.assoc, h.trunc]
  case law =>
    intro m
    rw [jpt_bc, jpt_bc, ← MonObj.comp_mul, ← h.law, yBC, ← Category.assoc,
      sq_subst f x m (fun p : Fin 1 × Fin d => psTrunc m (F p.2)) _ (fun i => psTrunc_map f m _), Category.assoc]
  case act =>
    intro m a
    rw [yBC, Category.assoc, h.act, ← Category.assoc (homAt _ _),
      sq_subst f x m (fun p : Fin 1 × Fin d => psTrunc m (act a p.2)) _ (fun i => psTrunc_map f m _), Category.assoc]
  case tan =>
    intro l
    have := comb_bc t f x (h.tan l)
    convert this using 2 with j j
    · change spMap _ ≫ spMap _ ≫ (y 1).left = spMap _ ≫ spMap _ ≫ (y 1).left
      rw [← Category.assoc, ← Category.assoc, spMap_cp, spMap_cp]
      congr 2
      apply Ideal.Quotient.ringHom_ext
      apply MvPolynomial.ringHom_ext
      · intro r
        change (MvPolynomial.aeval _) (MvPolynomial.map f (MvPolynomial.C r)) =
          GlobalTheory.CompanionTheory.Ar.dualMap f ((MvPolynomial.aeval _) (MvPolynomial.C r))
        ext <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
      · intro i
        change (MvPolynomial.aeval _) (MvPolynomial.map f (MvPolynomial.X i)) =
          GlobalTheory.CompanionTheory.Ar.dualMap f ((MvPolynomial.aeval _) (MvPolynomial.X i))
        rw [MvPolynomial.map_X, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
        split_ifs
        · ext <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap]
        · simp
    · split_ifs <;> simp
  case basis =>
    intro v
    exact ⟨v, fun j => by simp, fun a ha => funext fun j => by simpa using ha j⟩

end

open MvPolynomial (X C)

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S S₂ : Type} [CommRing S] [CommRing S₂] (f : S →+* S₂) (x : Sp S ⟶ X0)
variable {d : ℕ} (y : ∀ m, jOG x d m 1 ⟶ t.G)

theorem psum_pre {T T' : Over X0} (h : T' ⟶ T) {n : ℕ} (a : Fin n → (T ⟶ t.G)) (I : Finset (Fin n)) :
    psum t.G (fun k => h ≫ a k) I = h ≫ psum t.G a I := foldr_padd_pre h a _

theorem cφ_bc (m : ℕ) (I : ULift (Finset (Fin 2))) :
    cφG t ![jptG t (spMap f ≫ x) d (yBC t f x y) m (0 : Fin 2), jptG t (spMap f ≫ x) d (yBC t f x y) m (1 : Fin 2)] I =
      (cO f x _ m).left ≫ cφG t ![jptG t x d y m (0 : Fin 2), jptG t x d y m (1 : Fin 2)] I := by
  rw [cφG, cφG, ← Over.comp_left, ← psum_pre]
  congr 2
  funext k
  fin_cases k <;> exact jpt_bc t f x y m _

theorem val_scale {Y Z : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ} (u : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) {z : Z} {J} (hJ : Good t.PP.L z J) :
    val (scaleGenG t φ ε u g) r z J = gm r z ⊤ u * val g r z J :=
  (map_mul _ _ _).trans (congrArg (· * _) (gm_res r z _ (hJ.mem φ r) _))

theorem gm_unit_bc {Z : Scheme.{0}} {κ : Type} {m : ℕ} (u : (Jet S κ m)ˣ) (r : Z ⟶ Sp (Jet S₂ κ m)) (z : Z) :
    gm r z ⊤ (unitΓ (Units.map (jetCoef f κ m).toMonoidHom u)) =
      gm (r ≫ (cO f x κ m).left) z ⊤ (unitΓ u) := by
  rw [← gm_pull r (cO f x κ m).left z ⊤ trivial]
  congr 1
  apply Units.ext
  exact (congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (jetCoef f κ m))))

theorem coef_psJet {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (F : MvPowerSeries κ S) :
    jetCoef f κ m (psJet m F) = psJet m (MvPowerSeries.map f F) := by
  rw [psJet, psJet, jetCoef_mk, psTrunc_map]

theorem psIn_map {n n' : ℕ} (m : ℕ) (r : Fin n → Fin n') (F : MvPowerSeries (Fin n × Fin d) S) :
    psIn d m r (MvPowerSeries.map f F) = MvPolynomial.map f (psIn d m r F) := by
  rw [psIn, psIn, psTrunc_map, MvPolynomial.map_rename]

variable (e : ∀ m, FrTyG t x d y m) (e₂ : ∀ m, FrTyG t (spMap f ≫ x) d (yBC t f x y) m)

def FrBC : Prop := ∀ (m : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet S₂ (Fin 2 × Fin d) m)) (z : Z) (J), Good t.PP.L z J →
  val (L := t.PP.L) (φ := cφG t ![jptG t (spMap f ≫ x) d (yBC t f x y) m (0 : Fin 2),
    jptG t (spMap f ≫ x) d (yBC t f x y) m (1 : Fin 2)]) (ε := cε 2) (e₂ m) r z J =
  val (L := t.PP.L) (φ := cφG t ![jptG t x d y m (0 : Fin 2), jptG t x d y m (1 : Fin 2)]) (ε := cε 2) (e m)
    (r ≫ (cO f x _ m).left) z J

theorem exists_frBC (he : ∀ m, (e m).IsGen) :
    ∃ e₂ : ∀ m, FrTyG t (spMap f ≫ x) d (yBC t f x y) m, (∀ m, (e₂ m).IsGen) ∧ FrBC t f x y e e₂ := by
  have := fun m => exists_gen t.PP.isLB
    (φ' := cφG t ![jptG t (spMap f ≫ x) d (yBC t f x y) m (0 : Fin 2),
      jptG t (spMap f ≫ x) d (yBC t f x y) m (1 : Fin 2)]) (ε' := cε 2)
    (fun U _ h => Finset.prod_congr rfl fun k _ => by rw [cφ_bc])
    (LB.pullGen t.PP.L (cφG t ![jptG t x d y m (0 : Fin 2), jptG t x d y m (1 : Fin 2)]) (cε 2) (e m) (cO f x _ m).left)
    (DVR.pullGen_isGen_of_isGen _ _ _ (he m) _)
  choose e₂ h1 h2 using this
  exact ⟨e₂, h1, fun m Z r z J hJ => (h2 m Z r z J hJ).trans (val_pull hJ _ _ _)⟩

variable {t f x y e e₂}

theorem FrBC.pull (h : FrBC t f x y e e₂) {m m' : ℕ} {κ : Type} (α : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S κ m')
    (β : Jet S₂ (Fin 2 × Fin d) m →ₐ[S₂] Jet S₂ κ m')
    (hs : homAt (spMap f ≫ x) β ≫ cO f x _ m = cO f x κ m' ≫ homAt x α)
    {Z : Scheme.{0}} (r : Z ⟶ Sp (Jet S₂ κ m')) {z : Z} {J} (hJ : Good t.PP.L z J) :
    val (LB.pullGen t.PP.L (cφG t ![jptG t (spMap f ≫ x) d (yBC t f x y) m (0 : Fin 2),
      jptG t (spMap f ≫ x) d (yBC t f x y) m (1 : Fin 2)]) (cε 2) (e₂ m) (homAt (spMap f ≫ x) β).left) r z J =
    val (LB.pullGen t.PP.L (cφG t ![jptG t x d y m (0 : Fin 2), jptG t x d y m (1 : Fin 2)]) (cε 2) (e m)
      (homAt x α).left) (r ≫ (cO f x κ m').left) z J := by
  refine (val_pull hJ _ _ _).trans ((h m Z _ z J hJ).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
  rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, hs]

theorem FrBC.pe (h : FrBC t f x y e e₂) {m n : ℕ} (a b : Fin d → MvPolynomial (Fin n × Fin d) S)
    (a' b' : Fin d → MvPolynomial (Fin n × Fin d) S₂) (ha : ∀ j, a' j = MvPolynomial.map f (a j))
    (hb : ∀ j, b' j = MvPolynomial.map f (b j))
    {Z : Scheme.{0}} (r : Z ⟶ Sp (Jet S₂ (Fin n × Fin d) m)) {z : Z} {J} (hJ : Good t.PP.L z J) :
    val (peG t (spMap f ≫ x) d (yBC t f x y) e₂ m ![a', b']) r z J =
      val (peG t x d y e m ![a, b]) (r ≫ (cO f x _ m).left) z J :=
  h.pull _ _ (sq_subst f x m _ _ fun ⟨i, j⟩ => by fin_cases i; exacts [ha j, hb j]) r hJ

theorem val_pull_eq {Y Y₁ Y₂ Z : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ}
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (h₁ : Y₁ ⟶ Y) (h₂ : Y₂ ⟶ Y) (c : Y₂ ⟶ Y₁) (hc : h₂ = c ≫ h₁) (r : Z ⟶ Y₂)
    {z : Z} {J} (hJ : Good t.PP.L z J) :
    val (LB.pullGen t.PP.L φ ε g h₂) r z J = val (LB.pullGen t.PP.L φ ε g h₁) (r ≫ c) z J := by
  rw [val_pull hJ, val_pull hJ, hc, Category.assoc]

theorem FrBC.frame (h : FrBC t f x y e e₂) (hg : ∀ m, (e₂ m).IsGen)
    {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
    {ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S} {sy : MvPowerSeries (Fin 2 × Fin d) S}
    {ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S} (hf : IsFrameG t x d y F act ph1 ph2 sy ad e) :
    IsFrameG t (spMap f ≫ x) d (yBC t f x y) (fun i => MvPowerSeries.map f (F i))
      (fun a i => MvPowerSeries.map f (act a i)) (MvPowerSeries.map f ph1) (MvPowerSeries.map f ph2)
      (MvPowerSeries.map f sy) (fun a => MvPowerSeries.map f (ad a)) e₂ := by
  refine { gen := hg, ph1 := ?ph1, ph2 := ?ph2, sy := ?sy, ad := ?ad }
  case ph1 =>
    intro m
    obtain ⟨u, hu, hc⟩ := hf.ph1 m
    refine ⟨Units.map (jetCoef f _ m).toMonoidHom u, by rw [← coef_psJet, ← hu]; rfl,
      corr_of_val t.PP.isLB fun z J hJ => ?_⟩
    refine (val_pull_eq _ _ _ (cO f x _ m).left ?_ _ hJ).trans ((val_corr hJ hc _).trans ?_)
    · rw [← Over.comp_left, comp_lift, comp_lift, jpt_bc, jpt_bc, jpt_bc]
    · rw [val_scale t _ _ _ hJ, val_scale t _ _ _ hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv,
        val_inv, val_inv, gm_unit_bc f x,
        h.pe _ _ _ _ (fun j => psIn_map f m _ _) (fun j => (MvPolynomial.map_X f _).symm) _ hJ,
        h.pe _ _ _ _ (fun j => (MvPolynomial.map_X f _).symm) (fun j => (MvPolynomial.map_X f _).symm) _ hJ,
        h.pe _ _ _ _ (fun j => (MvPolynomial.map_X f _).symm) (fun j => (MvPolynomial.map_X f _).symm) _ hJ]
  case ph2 =>
    intro m
    obtain ⟨u, hu, hc⟩ := hf.ph2 m
    refine ⟨Units.map (jetCoef f _ m).toMonoidHom u, by rw [← coef_psJet, ← hu]; rfl,
      corr_of_val t.PP.isLB fun z J hJ => ?_⟩
    refine (val_pull_eq _ _ _ (cO f x _ m).left ?_ _ hJ).trans ((val_corr hJ hc _).trans ?_)
    · rw [← Over.comp_left, comp_lift, comp_lift, jpt_bc, jpt_bc, jpt_bc]
    · rw [val_scale t _ _ _ hJ, val_scale t _ _ _ hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv,
        val_inv, val_inv, gm_unit_bc f x,
        h.pe _ _ _ _ (fun j => (MvPolynomial.map_X f _).symm) (fun j => psIn_map f m _ _) _ hJ,
        h.pe _ _ _ _ (fun j => (MvPolynomial.map_X f _).symm) (fun j => (MvPolynomial.map_X f _).symm) _ hJ,
        h.pe _ _ _ _ (fun j => (MvPolynomial.map_X f _).symm) (fun j => (MvPolynomial.map_X f _).symm) _ hJ]
  case sy =>
    intro m
    obtain ⟨u, hu, hc⟩ := hf.sy m
    refine ⟨Units.map (jetCoef f _ m).toMonoidHom u, by rw [← coef_psJet, ← hu]; rfl,
      corr_of_val t.PP.isLB fun z J hJ => ?_⟩
    refine (h m _ _ z J hJ).trans ((val_corr hJ hc _).trans ?_)
    rw [val_scale t _ _ _ hJ, val_scale t _ _ _ hJ, ← map_inv, gm_unit_bc f x,
        h.pe _ _ _ _ (fun j => (MvPolynomial.map_X f _).symm) (fun j => (MvPolynomial.map_X f _).symm) _ hJ]
  case ad =>
    intro a
    obtain ⟨wL, hw, hm⟩ := hf.ad a
    refine ⟨wL, hw, fun m => ?_⟩
    obtain ⟨u, hu, hc⟩ := hm m
    refine ⟨Units.map (jetCoef f _ m).toMonoidHom u, by rw [← coef_psJet, ← hu]; rfl,
      corr_of_val t.PP.isLB fun z J hJ => ?_⟩
    have hv := val_corr hJ hc (𝟙 _ ≫ (cO f x _ m).left)
    rw [val_mul hJ, val_scale t _ _ _ hJ] at hv
    rw [val_mul hJ, val_scale t _ _ _ hJ, gm_unit_bc f x,
      h.pe _ _ _ _ (fun j => psIn_map f m _ _) (fun j => (MvPolynomial.map_X f _).symm) _ hJ,
      h.pe _ _ _ _ (fun j => (MvPolynomial.map_X f _).symm) (fun j => psIn_map f m _ _) _ hJ, ← hv,
      val_pull_eq _ (lift (jptG t x d y m (0 : Fin 2)) (jptG t x d y m (1 : Fin 2))).left _ (cO f x _ m).left
        (by rw [← Over.comp_left, comp_lift, jpt_bc, jpt_bc]) _ hJ]

theorem FrBC.trunc (h : FrBC t f x y e e₂) (hf : FrTrunc t x d y e) : FrTrunc t (spMap f ≫ x) d (yBC t f x y) e₂ :=
  fun m => corr_of_val t.PP.isLB fun z J hJ =>
    (h.pull _ _ (sq_of f x _ _ (jetCoef_trunc f _ m).symm) _ hJ).trans
      ((val_corr hJ (hf m) _).trans (h m _ _ z J hJ).symm)

theorem FrBC.axes (h : FrBC t f x y e e₂) (hf : FrAxes t x d y e) : FrAxes t (spMap f ≫ x) d (yBC t f x y) e₂ :=
  fun m => ⟨corr_of_val t.PP.isLB fun z J hJ =>
    (h.pe _ _ _ _ (fun _ => (map_zero _).symm) (fun _ => (MvPolynomial.map_X f _).symm) _ hJ).trans
      ((val_corr hJ (hf m).1 _).trans ((val_one _).trans (val_one _).symm)),
    corr_of_val t.PP.isLB fun z J hJ =>
    (h.pe _ _ _ _ (fun _ => (MvPolynomial.map_X f _).symm) (fun _ => (map_zero _).symm) _ hJ).trans
      ((val_corr hJ (hf m).2 _).trans ((val_one _).trans (val_one _).symm))⟩

end

end PositivityTheory.Xgn.GermSystem.Bc
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace PositivityTheory.Xgn.GermSystem

section Alg
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw comp1)
open PositivityTheory.HtPt.Ca
variable {R R' : Type} [CommRing R] [CommRing R'] {d : ℕ}

theorem lin_inv {φ ψ : Pt R 1 d} (hψ : Z ψ) (h : comp1 φ ψ = pt R (n := 1) d 0) : lin φ 1 * lin ψ 1 = 1 := by
  rw [← lin_comp1 φ hψ, h, lin_pt_eq_one]

theorem transH_comp {φ ψ φ' ψ' : Pt R 1 d} {lam lam' : PS R 2 d} (hφ' : Z φ') (hψ : Z ψ) (hl : AxOne lam)
    (hl' : AxOne lam') (hi : lin φ' 1 * lin ψ' 1 = 1) :
    transH (comp1 φ φ') (comp1 ψ' ψ) (lam' * ev (n := 2) ![comp1 φ' (pt R d 0), comp1 φ' (pt R d 1)] lam) =
      transH φ ψ lam ∘ₗ transH φ' ψ' lam' := by
  refine LinearMap.ext fun y => ?_
  have ht : (lin ψ' 1).transpose * (lin φ' 1).transpose = 1 := by
    rw [← Matrix.transpose_mul, hi, Matrix.transpose_one]
  rw [LinearMap.comp_apply, transH_apply, transH_apply, transH_apply, lin_comp1 φ hφ', lin_comp1 ψ' hψ,
    bil_mul_left hl' (axOne_comp hl hφ' hφ'), bil_comp hl hφ' hφ']
  refine Prod.ext (by simp only [Matrix.mulVec_mulVec]) ?_
  simp only [Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_transpose, Matrix.mulVec_add,
    Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (lin ψ' 1).transpose (lin φ' 1).transpose, ht, Matrix.one_mul, add_assoc]

theorem transH_surj {φ ψ : Pt R 1 d} (lam : PS R 2 d) (hi : lin φ 1 * lin ψ 1 = 1) :
    Function.Surjective (transH φ ψ lam) := fun y => by
  have ht : (lin ψ 1).transpose * (lin φ 1).transpose = 1 := by
    rw [← Matrix.transpose_mul, hi, Matrix.transpose_one]
  refine ⟨((lin ψ 1).mulVec y.1, (lin φ 1).transpose.mulVec y.2 - (bil lam 1 1).transpose.mulVec ((lin ψ 1).mulVec y.1)), ?_⟩
  rw [transH_apply]
  simp only [sub_add_cancel, Matrix.mulVec_mulVec, hi, ht, Matrix.one_mulVec]

theorem transH_map (f : R →+* R') (φ ψ : Pt R 1 d) (lam : PS R 2 d) (y : (Fin d → R) × (Fin d → R)) :
    transH (fun i => MvPowerSeries.map f (φ i)) (fun i => MvPowerSeries.map f (ψ i)) (MvPowerSeries.map f lam)
      (fun i => f (y.1 i), fun i => f (y.2 i)) =
      (fun i => f ((transH φ ψ lam y).1 i), fun i => f ((transH φ ψ lam y).2 i)) := by
  rw [transH_apply, transH_apply]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
    simp [Matrix.mulVec, dotProduct, lin, bil, MvPowerSeries.coeff_map]

theorem stdLat_comp {Ω : Type} [Field Ω] (f : R →+* Ω) {φ ψ : Pt R 1 d} (lam : PS R 2 d)
    (hi : lin φ 1 * lin ψ 1 = 1) (T : ((Fin d → Ω) × (Fin d → Ω)) →ₗ[Ω] (Fin d → Ω) × (Fin d → Ω)) :
    stdLat f.range (T ∘ₗ transH (fun i => MvPowerSeries.map f (φ i)) (fun i => MvPowerSeries.map f (ψ i))
      (MvPowerSeries.map f lam)) = stdLat f.range T := by
  unfold stdLat
  congr 1
  ext y
  constructor
  · rintro ⟨y₀, h, rfl⟩
    choose a ha using fun i => (h i).1
    choose b hb using fun i => (h i).2
    have e : y₀ = (fun i => f ((a, b).1 i), fun i => f ((a, b).2 i)) :=
      Prod.ext (funext fun i => (ha i).symm) (funext fun i => (hb i).symm)
    refine ⟨_, ?_, rfl⟩
    rw [e, transH_map]
    exact fun i => ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  · rintro ⟨y₀, h, rfl⟩
    choose a ha using fun i => (h i).1
    choose b hb using fun i => (h i).2
    obtain ⟨w, hw⟩ := transH_surj lam hi (a, b)
    refine ⟨(fun i => f (w.1 i), fun i => f (w.2 i)), fun i => ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩, ?_⟩
    rw [LinearMap.comp_apply, transH_map, hw]
    exact congrArg T (Prod.ext (funext fun i => (ha i).symm) (funext fun i => (hb i).symm))

theorem isMapOf_cancel {R₂ R₃ O : Type} [CommRing R₂] [CommRing R₃] [CommRing O] [StarRing O]
    {f : R →+* R₂} {g : R₂ →+* R₃} {B : Germ.FB R d O} {B₂ : Germ.FB R₂ d O} {B₃ : Germ.FB R₃ d O}
    (h : IsMapOf f B B₂) (h' : IsMapOf (g.comp f) B B₃) : IsMapOf g B₂ B₃ := by
  exact
    { F := fun i => by simp only [h'.F i, h.F i, MvPowerSeries.map_comp, RingHom.comp_apply]
      act := fun a i => by simp only [h'.act a i, h.act a i, MvPowerSeries.map_comp, RingHom.comp_apply]
      ph1 := by simp only [h'.ph1, h.ph1, MvPowerSeries.map_comp, RingHom.comp_apply]
      ph2 := by simp only [h'.ph2, h.ph2, MvPowerSeries.map_comp, RingHom.comp_apply]
      sy := by simp only [h'.sy, h.sy, MvPowerSeries.map_comp, RingHom.comp_apply]
      ad := fun a => by simp only [h'.ad a, h.ad a, MvPowerSeries.map_comp, RingHom.comp_apply] }

theorem dualMap_comp {R₂ R₃ : Type} [CommRing R₂] [CommRing R₃] (f : R →+* R₂) (g : R₂ →+* R₃) :
    (GlobalTheory.CompanionTheory.Ar.dualMap g).comp (GlobalTheory.CompanionTheory.Ar.dualMap f) = GlobalTheory.CompanionTheory.Ar.dualMap (g.comp f) := by
  ext r <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap]

end Alg

section Geo
open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 PositivityTheory.HtPt.Cd
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.TB.Canon Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdAd
open Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw comp1)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {X0 : Scheme.{0}}
  {t : SAB H X0} {S S₂ S₃ : Type} [CommRing S] [CommRing S₂] [CommRing S₃] {x : Sp S ⟶ X0} {x₂ : Sp S₂ ⟶ X0}
  {x₃ : Sp S₃ ⟶ X0} {d : ℕ}

theorem jetCoef_comp (f : S →+* S₂) (g : S₂ →+* S₃) (κ : Type) (m : ℕ) :
    (jetCoef g κ m).comp (jetCoef f κ m) = jetCoef (g.comp f) κ m := by
  apply Ideal.Quotient.ringHom_ext
  refine RingHom.ext fun p => ?_
  simp only [RingHom.comp_apply, jetCoef_mk, MvPolynomial.map_map]

structure IsBC (f : S →+* S₂) (g : GermAt t x d) (g₂ : GermAt t x₂ d) : Prop where
  map : IsMapOf f g.B g₂.B
  tg : ∀ l, g₂.tg l =
    spMap (_root_.GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ g.tg l
  jet : ∀ m, (g₂.x m).left = spMap (jetCoef f (Fin 1 × Fin d) m) ≫ (g.x m).left
  fr : ∀ m (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet S₂ (Fin 2 × Fin d) m)) (z : Z) (J), Good t.PP.L z J →
    vE g₂ m r z J = vE g m (r ≫ spMap (jetCoef f (Fin 2 × Fin d) m)) z J

theorem exists_bc (f : S →+* S₂) (e : x₂ = spMap f ≫ x) (g : GermAt t x d) : ∃ g₂ : GermAt t x₂ d, IsBC f g g₂ := by
  subst e
  obtain ⟨e₂, h1, h2⟩ := Bc.exists_frBC t f x g.x g.e g.frame.gen
  exact ⟨⟨FBMap.mapFB f g.B, Bc.yBC t f x g.x, e₂,
    fun l => spMap (_root_.GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ g.tg l,
    Bc.chart_bc t f x g.x g.chart, fun l => Bc.tan_bc t f x (g.tan l), Bc.basis_bc t f x g.tan g.basis,
    h2.frame h1 g.frame, h2.trunc g.trunc, h2.axes g.axes⟩,
    ⟨fun _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, fun _ => rfl⟩, fun _ => rfl, fun _ => rfl, h2⟩

theorem IsBC.cancel {f : S →+* S₂} {k : S₂ →+* S₃} {g : GermAt t x d} {g₂ : GermAt t x₂ d} {g₃ : GermAt t x₃ d}
    (h : IsBC f g g₂) (h' : IsBC (k.comp f) g g₃) : IsBC k g₂ g₃ := by
  refine ⟨isMapOf_cancel h.map h'.map, ?_, ?_, ?_⟩
  · intro l
    rw [h'.tg, h.tg, ← Category.assoc, Bc.spMap_cp, dualMap_comp]
  · intro m
    rw [h'.jet, h.jet, ← jetCoef_comp, ← Bc.spMap_cp, Category.assoc]
  · intro m Z r z J hJ
    rw [h'.fr m Z r z J hJ, h.fr m Z _ z J hJ, Category.assoc, Bc.spMap_cp, jetCoef_comp]

theorem IsBC.trans {f : S →+* S₂} {k : S₂ →+* S₃} {g : GermAt t x d} {g₂ : GermAt t x₂ d} {g₃ : GermAt t x₃ d}
    (h : IsBC f g g₂) (h' : IsBC k g₂ g₃) : IsBC (k.comp f) g g₃ := by
  refine ⟨h.map.trans h'.map, ?_, ?_, ?_⟩
  · intro l
    rw [h'.tg, h.tg, ← Category.assoc, Bc.spMap_cp, dualMap_comp]
  · intro m
    rw [h'.jet, h.jet, ← jetCoef_comp, ← Bc.spMap_cp, Category.assoc]
  · intro m Z r z J hJ
    rw [h'.fr m Z r z J hJ, h.fr m Z _ z J hJ, Category.assoc, Bc.spMap_cp, jetCoef_comp]

structure Cmp (g g₂ : GermAt t x d) (φ ψ : Q S d 1) (lam : PS S 2 d) : Prop where
  hφ : ∀ m, g₂.x m = PP m g.x φ
  hψ : ∀ m, g.x m = PP m g₂.x ψ
  hl : LamEq g g₂ φ lam

theorem exists_cmp (g g₂ : GermAt t x d) : ∃ φ ψ lam, Cmp g g₂ φ ψ lam := by
  obtain ⟨φ, hφ⟩ := exists_coord g g₂
  obtain ⟨ψ, hψ⟩ := exists_coord g₂ g
  obtain ⟨lam, h⟩ := exists_lam hφ
  exact ⟨φ, ψ, lam, hφ, hψ, h⟩

def mQ (f : S →+* S₂) {n : ℕ} (u : Q S d n) : Q S₂ d n :=
  ⟨fun i => MvPowerSeries.map f (u.1 i), fun i => by
    rw [MvPowerSeries.constantCoeff_map, u.2 i, map_zero]⟩

theorem mQ_ac (f : S →+* S₂) {n : ℕ} (φ : Q S d 1) (j : Fin n) : mQ f (ac φ (gen j)) = ac (mQ f φ) (gen j) :=
  Subtype.ext (by
    rw [ac_val]
    have := FBMap.mp_comp1 f φ.1 (pt S d j) (gen j : Q S d n).2
    rw [FBMap.mp_pt] at this
    exact (congrArg (FBMap.mp f) (ac_val φ (gen j))).trans this)

theorem coef_jQ' (f : S →+* S₂) {k n : ℕ} (m : ℕ) (b : Fin k → Q S d n) :
    (jQ m (fun j => mQ f (b j)) : Jet S₂ (Fin k × Fin d) m →+* Jet S₂ (Fin n × Fin d) m).comp
      (jetCoef f (Fin k × Fin d) m) =
    (jetCoef f (Fin n × Fin d) m).comp (jQ m b : Jet S (Fin k × Fin d) m →+* Jet S (Fin n × Fin d) m) := by
  have e : (fun s : Fin k × Fin d => psTrunc m ((mQ f (b s.1)).1 s.2)) =
      fun s => MvPolynomial.map f (psTrunc m ((b s.1).1 s.2)) := funext fun s => psTrunc_map f m _
  have h : ∀ s : Fin k × Fin d, MvPolynomial.map f (psTrunc m ((b s.1).1 s.2)) ∈ orig S₂ (Fin n × Fin d) :=
    fun s => congrFun e s ▸ FBIdJet.psTrunc_mem_orig m _ ((mQ f (b s.1)).2 s.2)
  have e₂ : jQ m (fun j => mQ f (b j)) = jetMap _ h := by
    unfold jQ
    congr 1
  rw [e₂]
  exact (jetCoef_map f m _ _ h).symm

theorem coef_jQ (f : S →+* S₂) {k n : ℕ} (m : ℕ) (b : Fin k → Q S d n) (b' : Fin k → Q S₂ d n)
    (h : ∀ j, b' j = mQ f (b j)) :
    (homAt x₂ (jQ m b')).left ≫ spMap (jetCoef f (Fin k × Fin d) m) =
      spMap (jetCoef f (Fin n × Fin d) m) ≫ (homAt x (jQ m b)).left := by
  obtain rfl : b' = fun j => mQ f (b j) := funext h
  exact (Bc.spMap_cp _ _).trans ((congrArg spMap (coef_jQ' f m b)).trans (Bc.spMap_cp _ _).symm)

theorem PP_bc {f : S →+* S₂} {g g₂ : GermAt t x d} {g' g₂' : GermAt t x₂ d} (h : IsBC f g g') (h₂ : IsBC f g₂ g₂')
    {φ : Q S d 1} (hφ : ∀ m, g₂.x m = PP m g.x φ) (m : ℕ) : g₂'.x m = PP m g'.x (mQ f φ) := by
  apply Over.OverMorphism.ext
  rw [h₂.jet, hφ, PP, PP, Over.comp_left, Over.comp_left, h.jet, ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ (g.x m).left) (coef_jQ f m ![φ] ![mQ f φ] fun j => by fin_cases j; rfl).symm

theorem Cmp.bc {f : S →+* S₂} {g g₂ : GermAt t x d} {g' g₂' : GermAt t x₂ d} (h : IsBC f g g') (h₂ : IsBC f g₂ g₂')
    {φ ψ : Q S d 1} {lam : PS S 2 d} (c : Cmp g g₂ φ ψ lam) :
    Cmp g' g₂' (mQ f φ) (mQ f ψ) (MvPowerSeries.map f lam) := by
  refine ⟨PP_bc h h₂ c.hφ, PP_bc h₂ h c.hψ, ?_⟩
  intro m
  obtain ⟨U, hU, k⟩ := c.hl m
  refine ⟨Units.map (jetCoef f _ m).toMonoidHom U, by rw [← Bc.coef_psJet, ← hU]; rfl, fun Z r z J hJ => ?_⟩
  have e := coef_jQ (x := x) (x₂ := x₂) f m (bb φ) (bb (mQ f φ)) fun j => by
    fin_cases j <;> exact (mQ_ac f φ _).symm
  refine (h₂.fr m Z r z J hJ).trans ((k Z _ z J hJ).trans (congrArg₂ (· * ·) (Bc.gm_unit_bc f x U r z).symm ?_))
  refine Eq.trans ?_ (h.fr m Z _ z J hJ).symm
  exact congrArg (fun s => vE g m s z J) ((Category.assoc _ _ _).trans
    ((congrArg (r ≫ ·) e.symm).trans (Category.assoc _ _ _).symm))

theorem Cmp.iso (hs : ∀ a : 𝓞 E, star a = H.bar a) (hp : PowFns t) {g g₂ : GermAt t x d} {φ ψ : Q S d 1}
    {lam : PS S 2 d} (c : Cmp g g₂ φ ψ lam) : GlobalTheory.CompanionTheory.Ar.Conj.IsIso g.B g₂.B φ.1 ψ.1 lam :=
  iso_of_coord c.hφ hs hp c.hψ c.hl

theorem Cmp.trans (hs : ∀ a : 𝓞 E, star a = H.bar a) (hp : PowFns t) {g g₂ g₃ : GermAt t x d}
    {φ ψ φ' ψ' φ'' ψ'' : Q S d 1} {lam lam' lam'' : PS S 2 d} (c : Cmp g g₂ φ ψ lam) (c' : Cmp g₂ g₃ φ' ψ' lam')
    (c'' : Cmp g g₃ φ'' ψ'' lam'') : transH φ''.1 ψ''.1 lam'' = transH φ.1 ψ.1 lam ∘ₗ transH φ'.1 ψ'.1 lam' := by
  have e₁ : φ'' = ac φ φ' := PP_inj g fun m => by rw [← c''.hφ, ← PP_coord c.hφ, ← c'.hφ]
  have e₂ : ψ'' = ac ψ' ψ := PP_inj g₃ fun m => by rw [← c''.hψ, ← PP_coord c'.hψ, ← c.hψ]
  have e₃ : ∀ u : Q S d 2, ac φ'' u = ac φ (ac φ' u) := fun u => PP_inj g fun m => by
    rw [← PP_coord c''.hφ, ← PP_coord c.hφ, ← PP_coord c'.hφ]
  have e₄ : E2 lam'' (gen 0 : Q S d 2) (gen 1) =
      E2 lam' (gen 0) (gen 1) * E2 lam (ac φ' (gen 0)) (ac φ' (gen 1)) :=
    VV_ext (x0 := x) t.PP.isLB fun m y J hJ => by
      rw [VV_mul, c.hl.dL hJ, c'.hl.dL hJ, c''.hl.dL hJ, ← Units.val_mul, e₃, e₃, _root_.mul_assoc,
        inv_mul_cancel_left]
  rw [formalSeriesValueAtTwoPoints_genericPoints, formalSeriesValueAtTwoPoints_genericPoints, formalSeriesValueAtTwoPoints_eq_ev, ac_val, ac_val] at e₄
  rw [e₁, e₂, e₄, ac_val, ac_val]
  exact transH_comp φ'.2 ψ.2 (c.iso hs hp).ax (c'.iso hs hp).ax (lin_inv ψ'.2 (c'.iso hs hp).inv₁)

def lieM (g : GermAt t x d) : GlobalTheory.CompanionTheory.Ar.LieModel t.G x (Fin d → S) where
  pt v := (tanModel t x).pt (gd g v)
  tan v := (tanModel t x).tan _
  inj := (tanModel t x).inj.comp (gd_bij g).1
  onto v hv := by
    obtain ⟨e, he⟩ := (tanModel t x).onto v hv
    obtain ⟨w, rfl⟩ := (gd_bij g).2 e
    exact ⟨w, he⟩
  add v w := by rw [map_add (f := _), (tanModel t x).add]
  smul c v := by rw [map_smul, (tanModel t x).smul]

theorem germ_aff (hs : ∀ a : 𝓞 E, star a = H.bar a) (hp : PowFns t) (z : X0) :
    ∃ (A : Type) (_ : CommRing A) (j : Sp A ⟶ X0) (d : ℕ), IsOpenImmersion j ∧ z ∈ Set.range j ∧
      Nonempty (GermAt t j d) := by
  obtain ⟨S, _, x0, d, G, A, tg, x, c, hj, hz, hc, ht, hb, hU⟩ := chart_affine E H X0 t z
  obtain ⟨e, ph1, ph2, sy, ad, hfr, htr, hfa, had⟩ := frame_affine E H X0 t S x0 d G A tg _ x c hc hU
  obtain ⟨hax, hr⟩ := FBIdAd.fbId E H X0 t hp hs S x0 _ G A _ tg _ x e ph1 ph2 sy ad hc hfr hfa had
  exact ⟨S, _, x0, d, hj, hz, ⟨⟨mkFB G A ph1 ph2 sy ad hax hr, x, e, tg, hc, ht, hb, hfr, htr, hfa⟩⟩⟩

theorem exists_factor {R A : Type} [CommRing R] [IsLocalRing R] [CommRing A] {X : Scheme.{0}} (x : Sp R ⟶ X)
    (j : Sp A ⟶ X) [IsOpenImmersion j] (h : x (IsLocalRing.closedPoint R) ∈ Set.range j) :
    ∃ a : A →+* R, x = spMap a ≫ j := by
  have hr : Set.range x ⊆ Set.range j := by
    rintro _ ⟨q, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint q).map x.continuous).mem_open j.isOpenEmbedding.isOpen_range h
  refine ⟨(Spec.preimage (IsOpenImmersion.lift j x hr)).hom, ?_⟩
  show x = Spec.map (Spec.preimage (IsOpenImmersion.lift j x hr)) ≫ j
  rw [Spec.map_preimage, IsOpenImmersion.lift_fac]

variable {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X0}

abbrev stPt (X0 : Scheme.{0}) (p : X0) : Sp (X0.presheaf.stalk p) ⟶ X0 := X0.fromSpecStalk p

theorem genMap_from (p : Cpt ξ) : ξ = spMap (genMap ξ p) ≫ stPt X0 p.1 := by
  obtain ⟨p, hp⟩ := p
  symm
  show Spec.map (X0.presheaf.stalkSpecializes hp ≫ Scheme.stalkClosedPointTo ξ) ≫ X0.fromSpecStalk p = ξ
  exact (congrArg (· ≫ X0.fromSpecStalk p) (Spec.map_comp _ _)).trans ((Category.assoc _ _ _).trans
    ((congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·)
      (Scheme.SpecMap_stalkSpecializes_fromSpecStalk hp)).trans (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)))

theorem st_spec {p q : X0} (h : q ⤳ p) : stPt X0 q = spMap (X0.presheaf.stalkSpecializes h).hom ≫ stPt X0 p :=
  (Scheme.SpecMap_stalkSpecializes_fromSpecStalk h).symm

theorem genMap_comp (p q : Cpt ξ) (h : q.1 ⤳ p.1) :
    (genMap ξ q).comp (X0.presheaf.stalkSpecializes h).hom = genMap ξ p := by
  have e : spMap ((genMap ξ q).comp (X0.presheaf.stalkSpecializes h).hom) = spMap (genMap ξ p) := by
    haveI : Mono (stPt X0 p.1) := inferInstanceAs (Mono (X0.fromSpecStalk p.1))
    rw [← cancel_mono (stPt X0 p.1), ← Bc.spMap_cp, Category.assoc, ← st_spec h, ← genMap_from p, ← genMap_from q]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem eq_mul_inverse_pow {A : Type} [CommRing A] {j : Sp A ⟶ X0} [Mono j] {gA : GermAt t j d} {k : S →+* S₃} {k' : S₂ →+* S₃}
    {a : A →+* S} {a' : A →+* S₂} (ha : x = spMap a ≫ j) (ha' : x₂ = spMap a' ≫ j) (hk : x₃ = spMap k ≫ x)
    (hk' : x₃ = spMap k' ≫ x₂) {gK : GermAt t x₃ d} (hK : IsBC (k.comp a) gA gK) :
    ∃ g' : GermAt t x₂ d, IsBC k' g' gK := by
  obtain ⟨g', hb'⟩ := exists_bc a' ha' gA
  have e : spMap (k'.comp a') = spMap (k.comp a) := by
    rw [← cancel_mono j, ← Bc.spMap_cp, ← Bc.spMap_cp, Category.assoc, Category.assoc, ← ha, ← ha', ← hk, ← hk']
  have e' : k'.comp a' = k.comp a := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  rw [← e'] at hK
  exact ⟨g', hb'.cancel hK⟩

theorem loc_aux₀ (hs : ∀ a : 𝓞 E, star a = H.bar a) [IsLocalRing S₃] {A : Type} [CommRing A] {j : Sp A ⟶ X0} {d' : ℕ}
    (gA : GermAt t j d') {k : S →+* S₃} {a : A →+* S} (ha : x = spMap a ≫ j) (hk : x₃ = spMap k ≫ x)
    (g₀ : GermAt t x₃ d) : d = d' ∧ ∃ gK : GermAt t x₃ d', IsBC (k.comp a) gA gK := by
  obtain ⟨gK, hK⟩ := exists_bc (x₂ := x₃) (k.comp a) (by rw [← Bc.spMap_cp, Category.assoc, ← ha, ← hk]) gA
  exact ⟨(germ_univ E H hs X0 t S₃ x₃ d g₀).1 d' gK, gK, hK⟩

theorem st_factor {A : Type} [CommRing A] (j : Sp A ⟶ X0) [IsOpenImmersion j] (q : X0) (hq : q ∈ Set.range j) :
    ∃ a : A →+* X0.presheaf.stalk q, stPt X0 q = spMap a ≫ j :=
  exists_factor _ j (by
    have : stPt X0 q (IsLocalRing.closedPoint _) = q := Scheme.fromSpecStalk_closedPoint
    exact this.symm ▸ hq)

theorem exists_loc (hs : ∀ a : 𝓞 E, star a = H.bar a) (hp : PowFns t) (g₀ : GermAt t ξ d) (p : Cpt ξ) :
    ∃ (gK : GermAt t ξ d) (U : X0.Opens), p.1 ∈ U ∧
      ∀ q : Cpt ξ, q.1 ∈ U → ∃ g' : GermAt t (stPt X0 q.1) d, IsBC (genMap ξ q) g' gK := by
  obtain ⟨A, _, j, d', _, hj, ⟨gA⟩⟩ := germ_aff hs hp p.1
  obtain ⟨a, ha⟩ := st_factor j p.1 hj
  obtain ⟨rfl, gK, hK⟩ := loc_aux₀ hs gA ha (genMap_from p) g₀
  refine ⟨gK, j.opensRange, hj, fun q hq => ?_⟩
  obtain ⟨b, hb⟩ := st_factor j q.1 hq
  exact eq_mul_inverse_pow ha hb (genMap_from p) (genMap_from q) hK

theorem key (hs : ∀ a : 𝓞 E, star a = H.bar a) (hp : PowFns t) {f : S →+* S₂} {g g' : GermAt t x d}
    {g₀ gq gp : GermAt t x₂ d} (h : IsBC f g gq) (h' : IsBC f g' gp) {φ ψ φ'' ψ'' : Q S₂ d 1} {lam lam'' : PS S₂ 2 d}
    (c : Cmp g₀ gq φ ψ lam) (c'' : Cmp g₀ gp φ'' ψ'' lam'') :
    ∃ (φ' ψ' : Pt S 1 d) (lam' : PS S 2 d), GlobalTheory.CompanionTheory.Ar.Conj.IsIso g.B g'.B φ' ψ' lam' ∧
      transH φ''.1 ψ''.1 lam'' = transH φ.1 ψ.1 lam ∘ₗ
        transH (fun i => MvPowerSeries.map f (φ' i)) (fun i => MvPowerSeries.map f (ψ' i))
          (MvPowerSeries.map f lam') := by
  obtain ⟨φ', ψ', lam', c'⟩ := exists_cmp g g'
  have k := c.trans hs hp (c'.bc h h') c''
  have e : ∀ u : Q S d 1, (mQ f u).1 = fun i => MvPowerSeries.map f (u.1 i) := fun _ => rfl
  rw [e, e] at k
  exact ⟨φ'.1, ψ'.1, lam', c'.iso hs hp, k⟩

theorem key_gen (hs : ∀ a : 𝓞 E, star a = H.bar a) (hp : PowFns t) {s : S₃ →+* S} (hx : x = spMap s ≫ x₃)
    {f : S →+* S₂} {k : S₃ →+* S₂} (hk : f.comp s = k) {g : GermAt t x d} {g₃ : GermAt t x₃ d}
    {g₀ gq gp : GermAt t x₂ d} (h : IsBC f g gq) (h' : IsBC k g₃ gp) {φ ψ φ'' ψ'' : Q S₂ d 1} {lam lam'' : PS S₂ 2 d}
    (c : Cmp g₀ gq φ ψ lam) (c'' : Cmp g₀ gp φ'' ψ'' lam'') :
    ∃ (B' : Germ.FB S d (𝓞 E)) (φ' ψ' : Pt S 1 d) (lam' : PS S 2 d), IsMapOf s g₃.B B' ∧
      GlobalTheory.CompanionTheory.Ar.Conj.IsIso g.B B' φ' ψ' lam' ∧
      transH φ''.1 ψ''.1 lam'' = transH φ.1 ψ.1 lam ∘ₗ
        transH (fun i => MvPowerSeries.map f (φ' i)) (fun i => MvPowerSeries.map f (ψ' i))
          (MvPowerSeries.map f lam') := by
  subst hk
  obtain ⟨g', hg'⟩ := exists_bc s hx g₃
  obtain ⟨φ', ψ', lam', h1, h2⟩ := key hs hp h (hg'.cancel h') c c''
  exact ⟨g'.B, φ', ψ', lam', hg'.map, h1, h2⟩

theorem key_loc (hs : ∀ a : 𝓞 E, star a = H.bar a) (hp : PowFns t) {f : S →+* Ω} {g g' : GermAt t x d}
    {g₀ gq gp : GermAt t ξ d} (h : IsBC f g gq) (h' : IsBC f g' gp) {φ ψ φ'' ψ'' : Q Ω d 1} {lam lam'' : PS Ω 2 d}
    (c : Cmp g₀ gq φ ψ lam) (c'' : Cmp g₀ gp φ'' ψ'' lam'') :
    stdLat f.range (transH φ''.1 ψ''.1 lam'') = stdLat f.range (transH φ.1 ψ.1 lam) := by
  obtain ⟨φ', ψ', lam', h1, h2⟩ := key hs hp h h' c c''
  rw [h2]
  exact stdLat_comp f lam' (lin_inv h1.c₂ h1.inv₁) _

theorem key_dir {f : S →+* S₂} {g : GermAt t x d} {g₀ gq : GermAt t x₂ d} (h : IsBC f g gq) {φ ψ : Q S₂ d 1}
    {lam : PS S₂ 2 d} (c : Cmp g₀ gq φ ψ lam) (l : Fin d) :
    ((lieM g₀).pt ((lin φ.1 1).mulVec (Pi.single l 1))).left =
      spMap (_root_.GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ g.tg l := by
  have := (comb_iff g₀ _ _).1 (coord_tan c.hφ l)
  have e₂ : (fun j => lin φ.1 1 j l) = (lin φ.1 1).mulVec (Pi.single l 1) := by
    funext j; simp
  rw [e₂, h.tg] at this
  exact this

theorem lieM_dir (g : GermAt t x d) (l : Fin d) : ((lieM g).pt (Pi.single l 1)).left = g.tg l := (tg_eq g l).symm

theorem lieM_act (g : GermAt t x d) (a : 𝓞 E) (v : Fin d → S) :
    (lieM g).pt ((rho g.B a).mulVec v) = (lieM g).pt v ≫ t.act.act a := (gd_act g a v).symm

theorem exists_germ (hs : ∀ a : 𝓞 E, star a = H.bar a) (hp : PowFns t) (ξ : Sp Ω ⟶ X0) :
    ∃ d, Nonempty (GermAt t ξ d) := by
  obtain ⟨A, _, j, d, _, hj, ⟨gA⟩⟩ := germ_aff hs hp (ξ (IsLocalRing.closedPoint Ω))
  obtain ⟨a, ha⟩ := exists_factor ξ j hj
  obtain ⟨g₀, -⟩ := exists_bc a ha gA
  exact ⟨d, ⟨g₀⟩⟩

theorem main (hs : ∀ a : 𝓞 E, star a = H.bar a) (hp : PowFns t) (ξ : Sp Ω ⟶ X0) :
    ∃ (d : ℕ) (M : LieModel t.G ξ (Fin d → Ω)), Nonempty (GermSys t ξ M) := by
  obtain ⟨d, ⟨g₀⟩⟩ := exists_germ hs hp ξ
  choose gK U hU hq using exists_loc hs hp g₀
  choose g hK using fun p => hq p p (hU p)
  choose φ ψ lam hc using fun p => exists_cmp g₀ (gK p)
  exact ⟨d, lieM g₀, ⟨
    { g₀ := g₀
      dir₀ := lieM_dir g₀
      act₀ := lieM_act g₀
      g := g
      BK := fun p => (gK p).B
      mapK := fun p => (hK p).map
      φ := fun p => (φ p).1
      ψ := fun p => (ψ p).1
      lam := lam
      iso := fun p => (hc p).iso hs hp
      dir := fun p l => key_dir (hK p) (hc p) l
      gen := fun p q h => key_gen hs hp (st_spec h) (genMap_comp p q h) (hK q) (hK p) (hc q) (hc p)
      loc := fun p => ⟨U p, hU p, fun q hqU => (hq p q hqU).elim fun _ hg' =>
        key_loc hs hp (hK q) hg' (hc q) (hc p)⟩ }⟩⟩

end Geo

end PositivityTheory.Xgn.GermSystem
end

theorem PositivityTheory.Xgn.germ_system_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) [IsLocallyNoetherian X], PowFns t → IsCptGen ξ → ∃ (d : ℕ) (M : LieModel t.G ξ (Fin d → Ω)), Nonempty (GermSys t ξ M) := by
  intro E _ _ _ H _ hs X t Ω _ _ ξ _ hp _
  exact PositivityTheory.Xgn.GermSystem.main hs hp ξ
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGermSystem
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem germSys_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) [IsLocallyNoetherian X], PowFns t → IsCptGen ξ → ∃ (d : ℕ) (M : LieModel t.G ξ (Fin d → Ω)), Nonempty (GermSys t ξ M) :=
  @PositivityTheory.Xgn.germ_system_exists

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGermSystemStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_germ_system : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) [IsLocallyNoetherian X], PowFns t → IsCptGen ξ → ∃ (d : ℕ) (M : LieModel t.G ξ (Fin d → Ω)), Nonempty (GermSys t ξ M) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.germSys_exists | exact GlobalTheory.CompanionTheory.Ar.Flat.germSys_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.germSys_exists <;> assumption)
end
