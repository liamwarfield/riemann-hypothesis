module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifBijectiveOfParam
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGenericWeilPairing
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Weilfun
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdAd
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Comp1IdentityLeft

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.CdUniv
noncomputable section
namespace PositivityTheory.HtPt.Cd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.ChartCompare GlobalTheory.FrameTangent GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws

section Gen
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {X0 : Scheme.{0}}
  {t : SAB H X0} {S : Type} [CommRing S] {x : Sp S ⟶ X0} {d : ℕ} (g : GermAt t x d)

def jp : JetPts t.G x d := (famEquiv x t.G d).symm g.x

theorem fam_jp : famEquiv x t.G d (jp g) = g.x := Equiv.apply_symm_apply _ _

theorem x_eq (m : ℕ) : g.x m = homAt x (jIn S d m) ≫ jp g m := (congrFun (fam_jp g) m).symm

theorem jp_eq (m : ℕ) : jp g m = homAt x (jOut S d m) ≫ g.x m := rfl

theorem jp_zero (m : ℕ) : algMap x (jetAug : Jet S (Fin d) m →ₐ[S] S) ≫ jp g m = 1 :=
  (zero_iff t x (jp g) m).1 (by rw [fam_jp]; exact g.chart.zero m)

def gd : (Fin d → S) →ₗ[S] TanM x t.G := dif x (jp g 1) (jp_zero g 1)

theorem tg_eq (l : Fin d) : g.tg l = (tv (gd g (Pi.single l 1))).left := by
  have h := (tan_iff t x (jp g) (jp_zero g 1) (g.tg l) (fun j => if l = j then 1 else 0)).2
    (by rw [fam_jp]; exact g.chart.tan l)
  have e : (fun j => if l = j then (1 : S) else 0) = Pi.single l 1 := by
    funext j; simp [Pi.single_apply, eq_comm]
  rw [e] at h
  exact h

theorem comb_iff (a : Fin d → S) (w : Sp (DualNumber S) ⟶ t.G.left) :
    IsCombAtG t x g.tg a w ↔ (tv (gd g a)).left = w := by
  have e : g.tg = fun i => (tv (gd g (Pi.single ((Equiv.refl (Fin d)) i) 1))).left := funext (tg_eq g)
  have e₂ : ∑ i, a i • gd g (Pi.single i 1) = gd g a := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_smul, ← map_sum]
    congr 1
    funext k; simp [Pi.single_apply]
  rw [e, ← e₂]
  exact comb_iff_sum t x (Equiv.refl _) (fun i => gd g (Pi.single i 1)) a w

theorem gd_bij : Function.Bijective (gd g) := by
  rw [Function.bijective_iff_existsUnique]
  intro W
  refine (existsUnique_congr fun a => ?_).1 (g.basis _ (GlobalTheory.FrameTangent.isTanAtG_of _ (tv_zero' W)))
  rw [comb_iff]
  exact ⟨fun h => tv_injective (Over.OverMorphism.ext h), fun h => by rw [h]⟩

theorem jp_param : IsFormalParam t.G x (jp g) :=
  param_of_dif_bijective t.semi.smooth
    (fun m => (trunc_iff t x (jp g) m).1 (by rw [fam_jp]; exact g.chart.trunc m)) (jp_zero g) (gd_bij g)

theorem coord_unique {m : ℕ} {B : Type} [CommRing B] [Algebra S B] (I : Ideal B) (hI : I ^ (m + 1) = ⊥)
    (y : overAt x B ⟶ t.G) (hy : homAt x (Ideal.Quotient.mkₐ S I) ≫ y = 1) :
    ∃! χ : Jet S (Fin 1 × Fin d) m →ₐ[S] B, y = homAt x χ ≫ g.x m := by
  obtain ⟨f, hf, hu⟩ := (jp_param g).2.2 m B I hI y hy
  refine ⟨f.comp (jOut S d m), ?_, fun χ hχ => ?_⟩
  · beta_reduce
    rw [← hcomp, ← jp_eq]; exact hf.symm
  · have := hu (χ.comp (jIn S d m)) (by
      beta_reduce
      rw [algMap_eq, ← hcomp, ← x_eq]; exact hχ.symm)
    rw [← this, AlgHom.comp_assoc, jIn_jOut, AlgHom.comp_id]

theorem coord_aug {m : ℕ} {B : Type} [CommRing B] [Algebra S B] (aug : B →ₐ[S] S)
    (hI : RingHom.ker aug ^ (m + 1) = ⊥) (y : overAt x B ⟶ t.G) (hy : homAt x aug ≫ y = 1) :
    ∃! χ : Jet S (Fin 1 × Fin d) m →ₐ[S] B, aug.comp χ = jetAug ∧ y = homAt x χ ≫ g.x m := by
  have e : Ideal.Quotient.mkₐ S (RingHom.ker aug) = (Algebra.ofId S _).comp aug := by
    refine AlgHom.ext fun r => ?_
    show Ideal.Quotient.mk _ r = Ideal.Quotient.mk _ (algebraMap S B (aug r))
    rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, AlgHom.commutes]
    simp
  obtain ⟨χ, hχ, hu⟩ := coord_unique g _ hI y (by rw [e, ← hcomp, hy, MonObj.comp_one])
  refine ⟨χ, ⟨?_, hχ⟩, fun χ' h => hu χ' h.2⟩
  exact (coord_unique g (m := m) (B := S) ⊥ (Ideal.bot_pow (by omega)) 1 (MonObj.comp_one _)).unique
    (by rw [← hcomp, ← hχ, hy]) (g.chart.zero m).symm

theorem ker_aug_pow (J : Type) (m : ℕ) : RingHom.ker (jetAug : Jet S J m →ₐ[S] S) ^ (m + 1) = ⊥ :=
  Chart.ker_jetAug_pow (R := S) J m

theorem coord_jet (J : Type) (m : ℕ) (y : overAt x (Jet S J m) ⟶ t.G)
    (hy : homAt x (jetAug : Jet S J m →ₐ[S] S) ≫ y = 1) :
    ∃! χ : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S J m,
      (∀ q, (jetAug : Jet S J m →ₐ[S] S) (χ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) ∧ y = homAt x χ ≫ g.x m := by
  refine (existsUnique_congr fun χ => and_congr_left fun _ => ?_).1 (coord_aug g jetAug (ker_aug_pow J m) y hy)
  exact ⟨fun h q => (AlgHom.congr_fun h (z m q)).trans (jetAug_z m q),
    fun h => jext fun q => (h q).trans (jetAug_z m q).symm⟩

theorem aeval_inr {κ : Type} [Fintype κ] [DecidableEq κ] (c : κ → S) (P : MvPolynomial κ S) :
    MvPolynomial.aeval (fun s => (TrivSqZeroExt.inr (c s) : DualNumber S)) P =
      TrivSqZeroExt.inl (MvPolynomial.constantCoeff P) +
        TrivSqZeroExt.inr (∑ s, P.coeff (Finsupp.single s 1) * c s) := by
  induction P using MvPolynomial.induction_on with
  | C r =>
    have : ∀ s : κ, (MvPolynomial.C r : MvPolynomial κ S).coeff (Finsupp.single s 1) = 0 := fun s => by
      rw [MvPolynomial.coeff_C, if_neg (Finsupp.single_ne_zero.2 one_ne_zero).symm]
    simp [this, TrivSqZeroExt.algebraMap_eq_inl]
  | add p q hp hq =>
    rw [map_add (f := _), hp, hq]
    ext <;> simp [add_mul, Finset.sum_add_distrib]
  | mul_X p n hp =>
    have : ∀ s : κ, (p * MvPolynomial.X n).coeff (Finsupp.single s 1) =
        if s = n then MvPolynomial.constantCoeff p else 0 := fun s => by
      rw [MvPolynomial.coeff_mul_X']
      by_cases h : s = n
      · subst h; simp [MvPolynomial.constantCoeff_eq]
      · simp [h, Ne.symm h]
    rw [map_mul, hp, MvPolynomial.aeval_X]
    ext <;> simp [this, mul_comm]

theorem vec_subst (φ : Germ.Pt S 1 d) (c : Fin d → S) :
    ((jetVec c).comp (jOut S d 1)).comp (jetSubstP 1 fun p : Fin 1 × Fin d => psTrunc 1 (φ p.2)) =
      (jetVec ((lin φ 1).mulVec c)).comp (jOut S d 1) := by
  have hT : ∀ (c : Fin d → S) (P : MvPolynomial (Fin 1 × Fin d) S),
      ((jetVec c).comp (jOut S d 1)) (Ideal.Quotient.mk _ P) =
        MvPolynomial.aeval (fun s : Fin 1 × Fin d => (TrivSqZeroExt.inr (c s.2) : DualNumber S)) P := fun c P => by
    have : ((jetVec c).comp (jOut S d 1)).comp (Ideal.Quotient.mkₐ S _) =
        MvPolynomial.aeval (fun s : Fin 1 × Fin d => (TrivSqZeroExt.inr (c s.2) : DualNumber S)) :=
      MvPolynomial.algHom_ext fun s => by
        rw [MvPolynomial.aeval_X]
        refine Eq.trans ?_ (jetVec_z_one c s.2)
        exact congrArg (jetVec c) (jetMap_z (S := S) 1 (fun p : Fin 1 × Fin d => MvPolynomial.X p.2)
          (fun _ => X_mem_orig _) s)
    exact AlgHom.congr_fun this P
  refine jext fun p => ?_
  rw [AlgHom.comp_apply, jetSubstP, jetMap_z, hT, hT, map_sub, aeval_inr, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  have : ∀ s : Fin 1 × Fin d, (psTrunc 1 (φ p.2)).coeff (Finsupp.single s 1) =
      MvPowerSeries.coeff (Finsupp.single s 1) (φ p.2) := fun s => by
    rw [FBIdJet.psTrunc_eq, MvPowerSeries.coeff_truncTotal _ (by simp)]
  simp only [this, Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton]
  ext
  · simp [TrivSqZeroExt.algebraMap_eq_inl]
  · simp [lin, Matrix.mulVec, dotProduct, TrivSqZeroExt.algebraMap_eq_inl]

theorem tv_gd (c : Fin d → S) : tv (gd g c) = homAt x ((jetVec c).comp (jOut S d 1)) ≫ g.x 1 := by
  rw [← hcomp]; rfl

theorem gd_act (a : 𝓞 E) (c : Fin d → S) :
    tv (gd g c) ≫ t.act.act a = tv (gd g ((rho g.B a).mulVec c)) := by
  rw [tv_gd, tv_gd, Category.assoc, g.chart.act 1 a, hcomp, vec_subst]
  rfl

end Gen

theorem germ_univ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] [IsLocalRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d), (∀ (d₂ : ℕ) (_ : GermAt t x d₂), d = d₂) ∧ ∀ (J : Type) [Finite J] (m : ℕ) (y : overAt x (Jet S J m) ⟶ t.G), homAt x (jetAug : Jet S J m →ₐ[S] S) ≫ y = 1 → ∃! χ : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S J m, (∀ q, (jetAug : Jet S J m →ₐ[S] S) (χ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) ∧ y = homAt x χ ≫ g.x m := by
  intro E _ _ _ H _ _ X0 t S _ _ x d g
  refine ⟨fun d₂ g₂ => ?_, fun J _ m y hy => coord_jet g J m y hy⟩
  have e := ((LinearEquiv.ofBijective _ (gd_bij g)).trans (LinearEquiv.ofBijective _ (gd_bij g₂)).symm).finrank_eq
  simpa using e

theorem germ_lie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d) (V : Type) [AddCommGroup V] [Module S V] (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G x V), ∃ e : V ≃ₗ[S] (Fin d → S), (∀ v, IsCombAtG t x g.tg (e v) (M.pt v).left) ∧ ∀ r : 𝓞 E →+* Module.End S V, M.IsActOf t.act.act r → ∀ a v, e (r a v) = (rho g.B a).mulVec (e v) := by
  intro E _ _ _ H _ _ X0 t S _ x d g V _ _ M
  have ht : ∀ v, IsTanAtG t x (M.pt v).left := fun v => ⟨Over.w (M.pt v), M.tan v⟩
  let L : V →ₗ[S] TanM x t.G :=
    { toFun := fun v => mkT (GlobalTheory.FrameTangent.ovT (ht v)) (GlobalTheory.FrameTangent.smT_zero_ovT (ht v))
      map_add' := fun v w => tv_injective (M.add v w)
      map_smul' := fun c v => tv_injective (Over.OverMorphism.ext (M.smul c v)) }
  have hL : ∀ v, tv (L v) = M.pt v := fun v => rfl
  have hb : Function.Bijective L := by
    refine ⟨fun v w h => M.inj ((hL v).symm.trans ((congrArg tv h).trans (hL w))), fun W => ?_⟩
    obtain ⟨v, hv⟩ := M.onto (tv W) (GlobalTheory.FrameTangent.isTanAtG_of _ (tv_zero' W)).2
    exact ⟨v, tv_injective hv⟩
  let e : V ≃ₗ[S] (Fin d → S) := (LinearEquiv.ofBijective L hb).trans (LinearEquiv.ofBijective _ (gd_bij g)).symm
  have he : ∀ v, gd g (e v) = L v := fun v => (LinearEquiv.ofBijective _ (gd_bij g)).apply_symm_apply _
  refine ⟨e, fun v => (comb_iff g _ _).2 (by rw [he, hL]), fun r hr a v => (gd_bij g).1 (tv_injective ?_)⟩
  rw [← gd_act, he, he, hL, hL]
  exact hr a v

end PositivityTheory.HtPt.Cd
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLev
noncomputable section

namespace PositivityTheory.HtPt.Htat

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open GlobalTheory.CompanionTheory.Ar ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace Lev

theorem eq_iff {La Q : Type} [AddCommGroup La] [Group Q] (m : ℕ) (ev : La → Q)
    (hadd : ∀ a b, ev (a + b) = ev a * ev b) (hker : ∀ a, ev a = 1 ↔ ∃ b, a = m • b) (a b : La) :
    ev a = ev b ↔ (Submodule.Quotient.mk a : La ⧸ LinearMap.range (m • (LinearMap.id : La →ₗ[ℤ] La))) =
      Submodule.Quotient.mk b := by
  have h : ev a = ev (a - b) * ev b := by rw [← hadd, sub_add_cancel]
  rw [Submodule.Quotient.eq, h, mul_eq_right, hker]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

theorem onto_of_count {La Q : Type} [AddCommGroup La] [Module.Finite ℤ La] [Group Q] (m : ℕ) (hm : 0 < m)
    (ev ev' : La → Q) (hadd : ∀ a b, ev (a + b) = ev a * ev b) (hker : ∀ a, ev a = 1 ↔ ∃ b, a = m • b)
    (hon : ∀ x, x ^ m = 1 ↔ ∃ a, ev a = x)
    (hadd' : ∀ a b, ev' (a + b) = ev' a * ev' b) (hker' : ∀ a, ev' a = 1 ↔ ∃ b, a = m • b)
    (ht : ∀ a, ev' a ^ m = 1) (x : Q) (hx : x ^ m = 1) : ∃ a, ev' a = x := by
  have : Finite (La ⧸ LinearMap.range (m • (LinearMap.id : La →ₗ[ℤ] La))) := by
    refine Module.finite_of_fg_torsion _ ?_
    intro y
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    refine ⟨⟨(m : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hm.ne')⟩, ?_⟩
    show (m : ℤ) • (Submodule.Quotient.mk a : La ⧸ LinearMap.range (m • (LinearMap.id : La →ₗ[ℤ] La))) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨a, by simp⟩
  choose g hg using fun a => (hon _).1 (ht a)
  choose s hs using Submodule.Quotient.mk_surjective (LinearMap.range (m • (LinearMap.id : La →ₗ[ℤ] La)))
  have hinj : Function.Injective fun y => (Submodule.Quotient.mk (g (s y)) :
      La ⧸ LinearMap.range (m • (LinearMap.id : La →ₗ[ℤ] La))) := by
    intro y y' h
    have h1 := (eq_iff m ev hadd hker _ _).2 h
    rw [hg, hg, eq_iff m ev' hadd' hker', hs, hs] at h1
    exact h1
  obtain ⟨c, rfl⟩ := (hon x).1 hx
  obtain ⟨y, hy⟩ := Finite.surjective_of_injective hinj (Submodule.Quotient.mk c)
  exact ⟨s y, by rw [← hg, eq_iff m ev hadd hker]; exact hy⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)

theorem exists_ef_one (hpq : 0 < D.p + D.q) : ∃ a b, D.EF a b = 1 := by
  have : Module.Projective (𝓞 E) D.La := D.proj
  have : Module.Finite (𝓞 E) D.La := D.fin
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  have : Module.Free ℤ D.La := inferInstance
  have : Nontrivial D.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [D.rank]; exact hpq)
  let B := Module.Free.chooseBasis ℤ D.La
  obtain ⟨i⟩ := B.index_nonempty
  obtain ⟨a, ha⟩ := D.unimod.2 (B.coord i)
  exact ⟨a, B i, by rw [ha]; simp⟩

theorem push {S : Scheme.{0}} (t : SAB H S) {k K : Type} [Field k] [Field K] (j : k →+* K) (q : Sp k ⟶ S)
    (q' : Sp K ⟶ S) (hq : q' = spMap j ≫ q)
    (I : TateIso D k (Over.mk q ⟶ t.G) (fun a g => g ≫ t.act.act a)
      (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)))
    (J : TateIso D K (Over.mk q' ⟶ t.G) (fun a g => g ≫ t.act.act a)
      (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))) :
    ∃ I' : TateIso D K (Over.mk q' ⟶ t.G) (fun a g => g ≫ t.act.act a)
      (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)),
      (∀ n, (I'.ζ n : K) = j (I.ζ n)) ∧ ∀ n a, (I'.ev n a).left = spMap j ≫ (I.ev n a).left := by
  subst hq
  have : Module.Finite (𝓞 E) D.La := D.fin
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : Epi (spMap j) := WeilObj.epi_spMap_field k K j
  let ψ := WeilObj.extPt q j
  have inj : ∀ x x' : Over.mk q ⟶ t.G, ψ ≫ x = ψ ≫ x' → x = x' := fun x x' h => by
    have h' : spMap j ≫ x.left = spMap j ≫ x'.left := congrArg CommaMorphism.left h
    exact Over.OverMorphism.ext ((cancel_epi (spMap j)).1 h')
  have hadd : ∀ n a b, ψ ≫ I.ev n (a + b) = (ψ ≫ I.ev n a) * (ψ ≫ I.ev n b) := fun n a b => by
    rw [I.add, comp_mul]
  have hker : ∀ n, 0 < n → ∀ a, ψ ≫ I.ev n a = 1 ↔ ∃ b, a = n • b := fun n hn a => by
    rw [← I.ker n hn a]
    exact ⟨fun h => inj _ _ (by rw [h, MonObj.comp_one]), fun h => by rw [h, MonObj.comp_one]⟩
  have ht : ∀ n, 0 < n → ∀ a, (ψ ≫ I.ev n a) ^ n = 1 := fun n hn a => by
    rw [← MonObj.comp_pow, (I.onto n hn _).2 ⟨a, rfl⟩, MonObj.comp_one]
  refine ⟨{ ζ := fun n => Units.map j.toMonoidHom (I.ζ n)
            ζ_prim := fun n hn => (I.ζ_prim n hn).map_of_injective (Units.map_injective j.injective)
            ζ_pow := fun n m hn hm => by rw [← map_pow, I.ζ_pow n m hn hm]
            ev := fun n a => ψ ≫ I.ev n a
            add := hadd
            lin := fun n c a => by rw [I.lin, Category.assoc]
            ker := hker
            onto := fun n hn x => ⟨onto_of_count n hn (J.ev n) _ (J.add n) (J.ker n hn) (J.onto n hn) (hadd n)
              (hker n hn) (ht n hn) x, by rintro ⟨a, rfl⟩; exact ht n hn a⟩
            tower := fun n m hn hm a => by rw [← MonObj.comp_pow, I.tower n m hn hm]
            isom := fun n hn a b => ?_ }, fun n => rfl, fun n a => rfl⟩
  obtain ⟨a', ha'⟩ := (J.onto n hn _).1 (ht n hn a)
  obtain ⟨b', hb'⟩ := (J.onto n hn _).1 (ht n hn b)
  have h1 := J.isom n hn a' b'
  rw [ha', hb'] at h1
  have h2 := weilIs_fieldExt t.G t.PP.L t.PP.isLB k K j q _ rfl n _ _ _ _ rfl rfl _ _ (I.isom n hn a b) h1
  rw [h2, map_zpow] at h1
  exact h1

end Lev

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem level_param : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) (t : SAB H S) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ S) (n : ℕ), 1 ≤ n → 0 < D.p + D.q → IsProper (Limits.pullback.snd t.G.hom ξ) → (∀ (k : Type) [Field k] (f : Ω →+* k) (g : Over.mk (spMap f ≫ ξ) ⟶ t.G), g ^ n = 1 → ∃ x : Over.mk ξ ⟶ t.G, g.left = spMap f ≫ x.left) → (∀ (k : Type) [Field k] [IsAlgClosed k] (f : Ω →+* k), Nonempty (TateIso D k (Over.mk (spMap f ≫ ξ) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)))) → ∃ (ev : D.La → (Over.mk ξ ⟶ t.G)) (ζ₀ : Ωˣ), IsPrimitiveRoot ζ₀ n ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (f : Ω →+* k), ∃ I : TateIso D k (Over.mk (spMap f ≫ ξ) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)), (I.ζ n : k) = f ζ₀ ∧ ∀ a, (I.ev n a).left = spMap f ≫ (ev a).left := by
  intro E _ _ _ H D S t Ω _ _ ξ n hn hpq _ hfull hT
  obtain ⟨I⟩ := hT (AlgebraicClosure Ω) (algebraMap Ω _)
  choose ev hev using fun a => hfull (AlgebraicClosure Ω) (algebraMap Ω _) (I.ev n a) ((I.onto n hn _).2 ⟨a, rfl⟩)
  have hζ : ∃ z : Ω, algebraMap Ω (AlgebraicClosure Ω) z = I.ζ n := by
    obtain ⟨a, b, hab⟩ := Lev.exists_ef_one D hpq
    have h0 := I.isom n hn a b
    rw [hab, zpow_one] at h0
    refine (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := Ω) (I.ζ n : AlgebraicClosure Ω)).2 fun σ => ?_
    have hσ : spMap (σ : AlgebraicClosure Ω →+* AlgebraicClosure Ω) ≫ spMap (algebraMap Ω (AlgebraicClosure Ω)) =
        spMap (algebraMap Ω (AlgebraicClosure Ω)) := by
      rw [← WeilObj.spMap_comp_of]
      exact congrArg spMap (RingHom.ext fun x => σ.commutes x)
    have h2 := weilIs_fieldExt t.G t.PP.L t.PP.isLB _ _ (σ : AlgebraicClosure Ω →+* AlgebraicClosure Ω) _ _
      (by rw [← Category.assoc, hσ]) n _ _ _ _ (by rw [hev, ← Category.assoc, hσ])
      (by rw [hev, ← Category.assoc, hσ]) _ _ h0 h0
    exact (congrArg Units.val h2).symm
  obtain ⟨z, hz⟩ := hζ
  have hz0 : z ≠ 0 := fun h => (I.ζ n).ne_zero (by rw [← hz, h, map_zero])
  refine ⟨ev, Units.mk0 z hz0, ?_, fun k _ _ f => ?_⟩
  · refine IsPrimitiveRoot.coe_units_iff.1 ?_
    refine IsPrimitiveRoot.of_map_of_injective (f := algebraMap Ω (AlgebraicClosure Ω)) ?_ (RingHom.injective _)
    rw [Units.val_mk0, hz]
    exact IsPrimitiveRoot.coe_units_iff.2 (I.ζ_prim n hn)
  · let _ : Algebra Ω k := f.toAlgebra
    let j : AlgebraicClosure Ω →ₐ[Ω] k := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    have hj : spMap f = spMap j.toRingHom ≫ spMap (algebraMap Ω (AlgebraicClosure Ω)) := by
      rw [← WeilObj.spMap_comp_of]
      exact congrArg spMap (RingHom.ext fun x => (j.commutes x).symm)
    obtain ⟨J⟩ := hT k f
    obtain ⟨I', h1, h2⟩ := Lev.push D t j.toRingHom _ (spMap f ≫ ξ) (by rw [hj, Category.assoc]) I J
    refine ⟨I', ?_, fun a => ?_⟩
    · rw [h1, ← hz]
      exact j.commutes z
    · rw [h2, hev, ← Category.assoc, ← hj]

end PositivityTheory.HtPt.Htat
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.Weilreg
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace PositivityTheory.HtPt.Weilreg

theorem valAt_top {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (s : Γ(X, ⊤)) :
    GlobalTheory.CompanionTheory.Ar.BT.valAt x ⊤ le_top s = (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (x.appTop.hom s) := by
  rfl

theorem val_unitOn {R : Type} [CommRing R] (u : Rˣ) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((unitOn u : Γ(Sp R, ⊤)ˣ) : Γ(Sp R, ⊤)) = (u : R) := by
  simp [unitOn]

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] {Γ : QFGroup R T} {S : Scheme.{0}}
  {G : Over S} [GrpObj G] {y : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}

def toAmb (h : Γ.IsTorsionAlong G y N i) {Y : Over (Spec (CommRingCat.of R))} (x : Y ⟶ Γ.G) :
    Over.mk (Y.hom ≫ y) ⟶ G :=
  Over.homMk (x.left ≫ i) (by
    change (x.left ≫ i) ≫ G.hom = Y.hom ≫ y
    rw [Category.assoc, h.isOver, ← Category.assoc, Over.w x])

theorem toAmb_pow (h : Γ.IsTorsionAlong G y N i) {Y : Over (Spec (CommRingCat.of R))} (x : Y ⟶ Γ.G) :
    toAmb h x ^ N = 1 :=
  (h.kernel Y _).2 ⟨x, rfl⟩

def overMap (y : Spec (CommRingCat.of R) ⟶ S) {Y Y' : Over (Spec (CommRingCat.of R))} (f : Y' ⟶ Y) :
    Over.mk (Y'.hom ≫ y) ⟶ Over.mk (Y.hom ≫ y) :=
  Over.homMk f.left (by
    change f.left ≫ Y.hom ≫ y = Y'.hom ≫ y
    rw [← Category.assoc, Over.w f])

theorem overMap_toAmb (h : Γ.IsTorsionAlong G y N i) {Y Y' : Over (Spec (CommRingCat.of R))} (f : Y' ⟶ Y)
    (x : Y ⟶ Γ.G) : overMap y f ≫ toAmb h x = toAmb h (f ≫ x) := by
  ext1
  simp [overMap, toAmb]

theorem weil_regular_of_fun (hW : type_of% @PositivityTheory.HtPt.Weilfun.weil_fun) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S) (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsAlgClosed (FractionRing O)] (y : Sp O ⟶ S) (La : Type) [AddCommGroup La] (X : TorsTower p t.G y La) (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ), IsProper (Limits.pullback.snd t.G.hom ((BT.genPt O).hom ≫ y)) → (∀ n (a b : La) (ga gb : Over.mk ((BT.genPt O).hom ≫ y) ⟶ t.G), ga.left = ((X.Γ n).pt (lev p n a)).left ≫ X.i n → gb.left = ((X.Γ n).pt (lev p n b)).left ≫ X.i n → Out.WeilIs t.G t.PP.L ((p ^ n : ℕ) : ℤ) ga gb (unitOn (Units.map (algebraMap O (FractionRing O) : O →* FractionRing O) (ζ n ^ B a b)))) → X.PairingRegular B ζ := by
  intro E _ _ _ H S _ t p _ O _ _ _ y La _ X B ζ hP hWe n
  have hpos : 1 ≤ p ^ n := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  obtain ⟨w, hnat, hval⟩ := hW E H S t (p ^ n) hpos
  let Y : Over (Spec (CommRingCat.of O)) := (X.Γ n).G ⊗ (X.Γ n).G
  let a0 : Over.mk (Y.hom ≫ y) ⟶ t.G := toAmb (X.tors n) (fst (X.Γ n).G (X.Γ n).G)
  let b0 : Over.mk (Y.hom ≫ y) ⟶ t.G := toAmb (X.tors n) (snd (X.Γ n).G (X.Γ n).G)
  refine ⟨(w (Over.mk (Y.hom ≫ y)) a0 b0 (toAmb_pow _ _) (toAmb_pow _ _)).val, ?_⟩
  intro a b
  let q : BT.genPt O ⟶ Y := lift ((X.Γ n).pt (lev p n a)) ((X.Γ n).pt (lev p n b))
  have ha : overMap y q ≫ a0 = toAmb (X.tors n) ((X.Γ n).pt (lev p n a)) := by
    simp only [a0, overMap_toAmb, q, lift_fst]
  have hb : overMap y q ≫ b0 = toAmb (X.tors n) ((X.Γ n).pt (lev p n b)) := by
    simp only [b0, overMap_toAmb, q, lift_snd]
  have key := hnat _ _ (overMap y q) a0 b0 (toAmb_pow _ _) (toAmb_pow _ _)
    (by rw [ha]; exact toAmb_pow _ _) (by rw [hb]; exact toAmb_pow _ _)
  have hw := hval (FractionRing O) ((BT.genPt O).hom ≫ y) hP
    (toAmb (X.tors n) ((X.Γ n).pt (lev p n a))) (toAmb (X.tors n) ((X.Γ n).pt (lev p n b)))
    (toAmb_pow _ _) (toAmb_pow _ _) _ (hWe n a b _ _ rfl rfl)
  rw [valAt_top]
  change (Scheme.ΓSpecIso (CommRingCat.of (FractionRing O))).hom.hom
      ((overMap y q).left.appTop.hom (w (Over.mk (Y.hom ≫ y)) a0 b0 _ _).val) = _
  rw [← key]
  have e : w _ (overMap y q ≫ a0) (overMap y q ≫ b0)
      (by rw [ha]; exact toAmb_pow _ _) (by rw [hb]; exact toAmb_pow _ _) =
      w _ (toAmb (X.tors n) ((X.Γ n).pt (lev p n a))) (toAmb (X.tors n) ((X.Γ n).pt (lev p n b)))
      (toAmb_pow _ _) (toAmb_pow _ _) := by
    congr 1
  rw [e, hw, val_unitOn]
  rfl

end PositivityTheory.HtPt.Weilreg
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.CaNfold
noncomputable section

namespace PositivityTheory.HtPt.Ca

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

section SlopeTestRemainingChoices

open ReciprocityTheory.ChartRestriction.G.TB.Canon Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdAd ReciprocityTheory.ChartRestriction.G.DVR

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}

theorem exists_kappa (t : SAB H X0) (n : ℕ) :
    ∃ κ : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G ^ n, snd t.G t.G]) (cφG t ![fst t.G t.G, snd t.G t.G]))
      (Sum.elim (cε 2) fun I => -((n : ℤ) * cε 2 I))), κ.IsGen ∧
      ∀ (T : Over X0) (p q : T ⟶ t.G) (z : T.left) (J), Good t.PP.L z J →
        val κ (lift p q).left z J = cubN (cubV t.cub z J) n 1 p q := by
  obtain ⟨t₀, ht₀, hv₀⟩ := exists_cubN t.cub (1 : t.G ⊗ t.G ⟶ t.G) (fst t.G t.G) (snd t.G t.G) n
  obtain ⟨κ, hκ, hv⟩ := exists_gen t.PP.isLB
    (φ' := Sum.elim (cφG t ![fst t.G t.G ^ n, snd t.G t.G]) (cφG t ![fst t.G t.G, snd t.G t.G]))
    (ε' := Sum.elim (cε 2) fun I => -((n : ℤ) * cε 2 I)) (fun U _ h => by
      have a := prod_cube₂ (fst t.G t.G ^ n) (snd t.G t.G) h
      have b := prod_cube₂ (fst t.G t.G) (snd t.G t.G) h
      have b' : ∏ I, h (cφG t ![fst t.G t.G, snd t.G t.G] I) ^ (-((n : ℤ) * cε 2 I)) =
          (∏ I, h (cφG t ![fst t.G t.G, snd t.G t.G] I) ^ (cε 2 I)) ^ (-(n : ℤ)) := by
        rw [← Finset.prod_zpow]
        exact Finset.prod_congr rfl fun I _ => by rw [← zpow_mul]; congr 1; ring
      refine Eq.trans ?_ ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) a
        (b'.trans (congrArg (· ^ (-(n : ℤ))) b)))).symm
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_pow]
      module) t₀ ht₀
  refine ⟨κ, hκ, fun T p q z J hJ => (hv _ _ z J hJ).trans ((hv₀ T (lift p q) z J hJ).trans ?_)⟩
  rw [MonObj.comp_one, lift_fst, lift_snd]

variable [StarRing (𝓞 E)] {t : SAB H X0} {S : Type} [CommRing S] {x : Sp S ⟶ X0} {d : ℕ} (g : GermAt t x d) {m k : ℕ}

theorem ac_zero (u : Q S d k) : ac (AQ g.B.A 0) u = 0 :=
  (congrArg (sq ![u]) (show AQ g.B.A 0 = 0 from Subtype.ext (act_zero_eq g.B))).trans (map_zero _)

theorem ac_succ (n : ℕ) (u : Q S d k) :
    ac (AQ g.B.A ((n + 1 : ℕ) : 𝓞 E)) u = op (FQ g.B.G) (ac (AQ g.B.A (n : 𝓞 E)) u) u := by
  rw [Nat.cast_succ, ac_add, ac_one]

theorem PP_nat (n : ℕ) (u : Q S d k) : PP m g.x (ac (AQ g.B.A (n : 𝓞 E)) u) = PP m g.x u ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, ac_zero, PP_zero g.chart, pow_zero]
  | succ n ih => rw [ac_succ, PP_op g.chart, ih, pow_succ]

theorem value_first_power {y : (jOG x d m 2).left} {J : ((jOG x d m 2).left ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L y J)
    (n : ℕ) : VV m y (pow1 g.B n) = (cubN (cubV t.cub y J) n 1 (PP m g.x (gen 0)) (PP m g.x (gen 1)) *
      (ee g.x g.e y J (ac (AQ g.B.A (n : 𝓞 E)) (gen 0)) (gen 1))⁻¹ * ee g.x g.e y J (gen 0) (gen 1) ^ n).val := by
  induction n with
  | zero =>
    rw [pow1, Finset.prod_range_zero, VV_one, Nat.cast_zero, ac_zero, (dict_ax hJ g.axes _).1]
    simp [cubN]
  | succ n ih =>
    have e : pow1 g.B (n + 1) = pow1 g.B n * E3 g.B.ph1 (ac (AQ g.B.A (n : 𝓞 E)) (gen 0)) (gen 0) (gen 1) := by
      simp only [formalSeriesValueAtThreePoints_eq_ev, ac_val, gen_val]
      exact Finset.prod_range_succ _ _
    rw [e, VV_mul, ih, frame_biext_dictionary_first_partial_law hJ g.frame, ← Units.val_mul, ac_succ, PP_nat]
    refine congrArg Units.val (Additive.ofMul.injective ?_)
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul, pow_succ, ofMul_mul, ofMul_inv]
    abel

theorem homAt_gen : (homAt x (jQ m ![(gen 0 : Q S d 2), gen 1])).left = 𝟙 _ := by
  have e : jQ m ![(gen 0 : Q S d 2), gen 1] = AlgHom.id S _ := GermD.jet_hom_ext fun s => by
    obtain ⟨j, s⟩ := s
    rw [jQ_X]
    fin_cases j <;> exact psJet_X m _
  rw [e]
  exact Spec.map_id _

end SlopeTestRemainingChoices


open ReciprocityTheory.ChartRestriction.G.TB.Canon Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdAd in
theorem nfold_law : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (n : ℕ), ∃ κ : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G ^ n, snd t.G t.G]) (cφG t ![fst t.G t.G, snd t.G t.G])) (Sum.elim (cε 2) fun I => -((n : ℤ) * cε 2 I))), κ.IsGen ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ κ (lift (1 : t.G ⟶ t.G) (𝟙 t.G)).left) (LB.oneGen t.PP.L) ∧ ∀ (S : Type) [CommRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d) (m : ℕ), ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (pow1 g.B n) ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ κ (lift (jptG t x d g.x m (0 : Fin 2)) (jptG t x d g.x m (1 : Fin 2))).left) (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x d g.x g.e m ![fun j => psIn d m ![0] (g.B.A.act (n : 𝓞 E) j), fun j => MvPolynomial.X ((1 : Fin 2), j)]) (LB.invGen t.PP.L _ _ (genPowG t _ _ (g.e m) n)))) := by
  intro E _ _ _ H _ _ X0 t n
  obtain ⟨κ, hκ, hv⟩ := exists_kappa t n
  refine ⟨κ, hκ, corr_of_val t.PP.isLB fun y J hJ => ?_, fun S _ x d g m => ?_⟩
  · refine (val_pull hJ _ _ _).trans ?_
    rw [Category.id_comp, val_one, hv _ _ _ y J hJ]
    exact Finset.prod_eq_one fun i _ => (isCub_cubV t.cub hJ).face₂ _ _
  · have hc : MvPowerSeries.constantCoeff (pow1 g.B n) = 1 := by
      rw [← cc_ev ZZa, ((act_zero S d _ g.B).2.2.2 n).1.1, map_one]
    obtain ⟨w, hw⟩ : IsUnit (pow1 g.B n) := MvPowerSeries.isUnit_iff_constantCoeff.2 (hc ▸ isUnit_one)
    let u : (Jet S (Fin 2 × Fin d) m)ˣ := ⟨psJet m w.val, psJet m w.inv,
      by rw [← FBIdJet.psJet_mul, w.val_inv, FBIdJet.psJet_one], by rw [← FBIdJet.psJet_mul, w.inv_val, FBIdJet.psJet_one]⟩
    have hu : (u : Jet S (Fin 2 × Fin d) m) = psJet m (pow1 g.B n) := congrArg (psJet m) hw
    refine ⟨u, hu, corr_of_val t.PP.isLB fun y J hJ => ?_⟩
    refine (val_pull hJ _ _ _).trans ?_
    rw [Category.id_comp, hv _ _ _ y J hJ]
    have h0 := gm_unit (x0 := x) (y := y) u ![gen 0, gen 1] _ hu
    have h1 := val_peG g.x hJ g.e ![gen 0, gen 1]
      ![fun j => psIn d m ![0] (g.B.A.act (n : 𝓞 E) j), fun j => MvPolynomial.X ((1 : Fin 2), j)]
      (ac (AQ g.B.A (n : 𝓞 E)) (gen 0)) (gen 1)
      (by rintro ⟨l, j⟩; fin_cases l; exacts [hA _ 0 j, hX 1 j])
      (by rintro ⟨l, j⟩; fin_cases l; exacts [(FBIdPh.cc_psIn d m _ _).trans (g.B.A.const _ j),
        MvPolynomial.constantCoeff_X _ _])
    rw [sq_ac, sq_gen, sq_gen, homAt_gen] at h1
    have h2 : val (genPowG t _ _ (g.e m) n) (𝟙 _) y J = ee g.x g.e y J (gen 0) (gen 1) ^ n := by
      rw [ee, homAt_gen]; exact map_pow _ _ _
    have h3 : sb ![(gen 0 : Q S d 2), gen 1] (pow1 g.B n) = pow1 g.B n := formalSeriesValueAtTwoPoints_genericPoints _
    rw [h3, value_first_power g hJ, homAt_gen] at h0
    refine Eq.trans ?_ ((val_scale hJ _ _ _).trans (congrArg₂ (· * ·) (Units.ext h0) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) h1 ((val_inv _ _).trans (congrArg (·⁻¹) h2)))))).symm
    rw [PP_gen, PP_gen]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, Matrix.cons_val]
    abel

end PositivityTheory.HtPt.Ca
end
end
