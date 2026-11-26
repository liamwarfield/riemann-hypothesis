module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC

@[expose] public section

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDPf
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

attribute [local instance] Over.cartesianMonoidalCategory

namespace GermD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)

theorem genPowG_isGen {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (hg : g.IsGen) (k : ℕ) : (genPowG t φ ε g k).IsGen := by
  unfold LB.Gen.IsGen at hg ⊢
  intro i j
  simp only [genPowG]
  erw [map_pow, map_pow, hg i j, mul_pow]
  congr 1
  unfold LB.LinComb
  dsimp only
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm]

theorem val_genPowG {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (k : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι) :
    val (genPowG t φ ε g k) r z J = val g r z J ^ k := by
  simp only [genPowG, val]
  exact map_pow _ _ _

variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

abbrev ρT (m : ℕ) : jOG x0 d m 1 ⟶ jOG x0 d (m + 1) 1 :=
  homAt x0 (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m)

theorem jBase_trunc (m : ℕ) : ρT x0 d m ≫ jBaseG x0 d (m + 1) 1 = jBaseG x0 d m 1 := by
  apply Over.OverMorphism.ext
  simp only [ρT, jBaseG, Formalism.L2.Pj.homAt, Over.comp_left, Over.homMk_left]
  rw [spMap_comp_alg]

variable {t x0 d x}
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}

private lemma formEq_eL_lemma (m : ℕ) (g : Fin d → MvPowerSeries (Fin 1 × Fin d) S) :
    (sL m g).comp (jetCopy d m (0 : Fin 2)) = AlgHom.id S _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  fin_cases i
  simp [sL, jetCopy, jetMap, jetSubstP, liftJet, Ideal.Quotient.liftₐ_apply]
  erw [Ideal.Quotient.lift_mk]
  simp

private lemma formEq_eL_lemma_2 (m : ℕ) (g : Fin d → MvPowerSeries (Fin 1 × Fin d) S) :
    (sL m g).comp (jetCopy d m (1 : Fin 2)) = jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (g p.2) := by
  have hq : ∀ q : MvPolynomial (Fin 1 × Fin d) S,
      MvPolynomial.rename (fun p : Fin 1 × Fin d => ((0 : Fin 1), p.2)) q = q := by
    intro q
    rw [show (fun p : Fin 1 × Fin d => ((0 : Fin 1), p.2)) = id from
      funext fun p => Prod.ext (Subsingleton.elim _ _) rfl]
    simp
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  fin_cases i
  simp [sL, jetCopy, jetMap, jetSubstP, liftJet, Ideal.Quotient.liftₐ_apply]
  erw [Ideal.Quotient.lift_mk]
  simp [psIn, hq]
  erw [Ideal.Quotient.lift_mk]
  simp [psIn, hq]

theorem formEq_eL (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) (I : ULift (Finset (Fin 2))) :
    (x m).left ≫ cφG t ![𝟙 t.G, t.act.act H.w0] I =
      (homAt x0 (sL m (act H.w0))).left ≫ cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I := by
  have hp : ∀ {T T' : Over X0} (f : T' ⟶ T) (a b : T ⟶ t.G),
      f ≫ padd t.G a b = padd t.G (f ≫ a) (f ≫ b) := by
    intro T T' f a b
    simp only [padd, ← Category.assoc, comp_lift]
  have nat : ∀ {T T' : Over X0} (f : T' ⟶ T) (xs : Fin 2 → (T ⟶ t.G)) (l : List (Fin 2)),
      f ≫ l.foldr (fun k acc => padd t.G (xs k) acc) (pzero t.G T) =
        l.foldr (fun k acc => padd t.G (f ≫ xs k) acc) (pzero t.G T') := by
    intro T T' f xs l
    induction l with
    | nil => simp only [List.foldr_nil, pzero, ← Category.assoc, comp_toUnit]
    | cons k l ih => simp only [List.foldr_cons, hp, ih]
  have natp : ∀ {T T' : Over X0} (f : T' ⟶ T) (xs : Fin 2 → (T ⟶ t.G)) (J : Finset (Fin 2)),
      f ≫ psum t.G xs J = psum t.G (fun i => f ≫ xs i) J := by
    intro T T' f xs J
    unfold psum
    exact nat f xs _
  simp only [cφG]
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  rw [natp, natp]
  congr 1
  funext i
  fin_cases i
  · simp [jptG, ← Category.assoc, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_comp, formEq_eL_lemma, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_id]
  · simp [jptG, ← Category.assoc, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_comp, formEq_eL_lemma_2, hch.act m H.w0]

theorem val_eL_trunc (hch : IsChartG t x0 d F act tg uvec x) (e : ∀ m, FrTyG t x0 d x m) (wP : PrimTyG t)
    (htr : FrTrunc t x0 d x e) (m : ℕ) (y : (jOG x0 d m 1).left) (J : ((jOG x0 d m 1).left ⟶ t.G.left) → t.PP.L.ι)
    (hJ : Good t.PP.L y J) :
    val (eLG t x0 d x act e wP (m + 1)) (ρT x0 d m).left y J = val (eLG t x0 d x act e wP m) (𝟙 _) y J := by
  have hx : (ρT x0 d m).left ≫ (x (m + 1)).left = (x m).left := by
    rw [← Over.comp_left, hch.trunc m]
  have hs : (ρT x0 d m).left ≫ (homAt x0 (sL (m + 1) (act H.w0))).left =
      (homAt x0 (sL m (act H.w0))).left ≫ (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _)).left := by
    rw [← Over.comp_left, ← Over.comp_left, homAt_comp, homAt_comp, sL_trunc]
  refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) (val_mul hJ _ _ _).symm)
  · exact (val_pull hJ wP _ _).trans ((congrArg (fun r => val wP r y J) (hx.trans (Category.id_comp _).symm)).trans
      (val_pull hJ wP _ _).symm)
  · exact (val_pull hJ (e (m + 1)) _ _).trans ((congrArg (fun r => val (e (m + 1)) r y J) hs).trans
      ((val_pull hJ (e (m + 1)) _ _).symm.trans ((val_corr hJ (htr m) _).trans
        ((congrArg (fun r => val (e m) r y J) (Category.id_comp _).symm).trans (val_pull hJ (e m) _ _).symm))))

theorem ptSec_trunc (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) :
    (ptSecT t.G (x m)).left ≫ (jBaseG x0 d m 1 ▷ t.G).left =
      (ρT x0 d m).left ≫ (ptSecT t.G (x (m + 1))).left ≫ (jBaseG x0 d (m + 1) 1 ▷ t.G).left := by
  unfold ptSecT
  rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left]
  congr 1
  simp only [lift_whiskerRight, comp_lift, Category.id_comp, jBase_trunc]
  rw [show ρT x0 d m ≫ x (m + 1) = x m from hch.trunc m]

end GermD


open GermD in
theorem germSt_holds : GermSt := by
  intro E _ _ _ H X0 t S _ x0 d F act κ _ tg uvec x ph1 ph2 sy ad e wP hch hfr hpr htr k Fs
  have hL := t.PP.isLB
  have heL : ∀ m, (eLG t x0 d x act e wP m).IsGen := fun m =>
    ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen t.PP.L _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen t.PP.L _ _ _ hpr.1 _)
      (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen t.PP.L _ _ _ (hfr.gen m) _)
  have hτ : ∀ m, ∃ τ : LB.Gen (LB.LinComb t.PP.L (Y := (jOG x0 d m 1).left) (K := Fin 1) (fun _ => (x m).left)
      fun _ => (k : ℤ)), τ.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (jOG x0 d m 1).left) (z : Z)
        (J : (Z ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
          val τ r z J = val (genPowG t _ _ (eLG t x0 d x act e wP m) k) r z J := by
    intro m
    refine exists_gen hL ?_ _ (genPowG_isGen t _ _ _ (heL m) k)
    intro U _ hU
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id, _root_.mul_one,
      formEq_eL hch m]
    rw [_root_.mul_assoc, ← Finset.prod_mul_distrib]
    simp only [← zpow_add, _root_.mul_neg, neg_add_cancel, zpow_zero, Finset.prod_const_one, _root_.mul_one]
  choose τ hτg hτv using hτ
  have hcorr : ∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (τ m) (genPowG t _ _ (eLG t x0 d x act e wP m) k) :=
    fun m => corr_of_val hL fun y J hJ => hτv m _ (𝟙 _) y J hJ
  choose F' hF' using fun m =>
    exists_pullSec t.G t.PP.L (k : ℤ) (jBaseG x0 d m 1 ▷ t.G) (whiskerRight_snd _ _) Fs
  choose v hv using fun m => exists_value t.G t.PP.L hL (k : ℤ) (F' m) (x m) (τ m) (hτg m)
  have hvc : ∀ m, v m = (ρT x0 d m).left.appTop.hom (v (m + 1)) := by
    intro m
    refine fn_ext (V := ⊤) fun y _ => ?_
    obtain ⟨i, hi⟩ := exists_chart hL ((x m).left y)
    have hρx : (ρT x0 d m).left ≫ (x (m + 1)).left = (x m).left := by
      rw [← Over.comp_left, hch.trunc m]
    have hm : (𝟙 _ : (jOG x0 d m 1).left ⟶ _) y ∈ LB.wchart t.PP.L (fun _ : Fin 1 => (x m).left) (fun _ => i) :=
      Set.mem_iInter.2 fun _ => hi
    have app_eq : ∀ {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C), f ≫ g = h → ∀ a, g (f a) = h a :=
      fun f g h e a => congrArg (fun q => q a) e
    have hps0 : (𝟙 _ ≫ (ptSecT t.G (x m)).left) ≫ (snd (jOG x0 d m 1) t.G).left = (x m).left := by
      rw [Category.id_comp, ← Over.comp_left, ptSecT, lift_snd]
    have hps1 : ((ρT x0 d m).left ≫ (ptSecT t.G (x (m + 1))).left) ≫ (snd (jOG x0 d (m + 1) 1) t.G).left =
        (x m).left := by
      rw [Category.assoc, ← Over.comp_left, ptSecT, lift_snd, hρx]
    have hm1 : (ρT x0 d m).left y ∈ LB.wchart t.PP.L (fun _ : Fin 1 => (x (m + 1)).left) (fun _ => i) := by
      refine Set.mem_iInter.2 fun _ => ?_
      show (x (m + 1)).left ((ρT x0 d m).left y) ∈ (t.PP.L.U i : Set t.G.left)
      rw [app_eq _ _ _ hρx]
      exact hi
    have mem0 : (𝟙 _ ≫ (ptSecT t.G (x m)).left) y ∈ (LPow t.G t.PP.L (k : ℤ) (jOG x0 d m 1)).U (fun _ => i) := by
      refine Set.mem_iInter.2 fun _ => ?_
      show (snd (jOG x0 d m 1) t.G).left ((𝟙 _ ≫ (ptSecT t.G (x m)).left) y) ∈ (t.PP.L.U i : Set t.G.left)
      rw [app_eq _ _ _ hps0]
      exact hi
    have mem1 : ((ρT x0 d m).left ≫ (ptSecT t.G (x (m + 1))).left) y ∈
        (LPow t.G t.PP.L (k : ℤ) (jOG x0 d (m + 1) 1)).U (fun _ => i) := by
      refine Set.mem_iInter.2 fun _ => ?_
      show (snd (jOG x0 d (m + 1) 1) t.G).left (((ρT x0 d m).left ≫ (ptSecT t.G (x (m + 1))).left) y) ∈
        (t.PP.L.U i : Set t.G.left)
      rw [app_eq _ _ _ hps1]
      exact hi
    have e0 := value_stalk t.G t.PP.L hL (k : ℤ) (hv m) (𝟙 _) y (fun _ => i) hm
    have e1 := value_stalk t.G t.PP.L hL (k : ℤ) (hv (m + 1)) (ρT x0 d m).left y (fun _ => i) hm1
    have l0 := pullSec_stalk t.G t.PP.L (k : ℤ) (hF' m) (𝟙 _ ≫ (ptSecT t.G (x m)).left) y (fun _ => i) mem0
    have l1 := pullSec_stalk t.G t.PP.L (k : ℤ) (hF' (m + 1)) ((ρT x0 d m).left ≫ (ptSecT t.G (x (m + 1))).left) y
      (fun _ => i) mem1
    have hmor : (𝟙 _ ≫ (ptSecT t.G (x m)).left) ≫ (jBaseG x0 d m 1 ▷ t.G).left =
        ((ρT x0 d m).left ≫ (ptSecT t.G (x (m + 1))).left) ≫ (jBaseG x0 d (m + 1) 1 ▷ t.G).left := by
      rw [Category.id_comp, ptSec_trunc hch m, Category.assoc]
    obtain ⟨J, hJ, hJi⟩ := exists_good t.PP.L hL y (fun _ : Fin 1 => (x m).left) (fun _ => i) (fun _ _ _ => rfl)
      (fun _ => hi)
    have hunit : gm (𝟙 _) y (LB.wchart t.PP.L (fun _ : Fin 1 => (x m).left) (fun _ => i)) ((τ m).s (fun _ => i)) =
        gm (ρT x0 d m).left y (LB.wchart t.PP.L (fun _ : Fin 1 => (x (m + 1)).left) (fun _ => i))
          ((τ (m + 1)).s (fun _ => i)) :=
      (val_of (τ m) (𝟙 _) y J (fun _ => i) (fun _ => by rw [Category.id_comp]; exact hJi 0)).symm.trans
        ((hτv m _ (𝟙 _) y J hJ).trans ((val_genPowG t _ _ _ k _ y J).trans
          ((congrArg (· ^ k) (val_eL_trunc hch e wP htr m y J hJ)).symm.trans
            ((val_genPowG t _ _ _ k _ y J).symm.trans ((hτv (m + 1) _ _ y J hJ).symm.trans
              (val_of (τ (m + 1)) _ y J (fun _ => i) (fun _ => by rw [hρx]; exact hJi 0)))))))
    have hmain := e0.symm.trans (l0.trans ((congrArg (fun r => gs r y _ (Fs.f (fun _ => i))) hmor).trans
      (l1.symm.trans e1)))
    have h2 := (Units.mul_left_inj (gm (𝟙 _) y _ ((τ m).s (fun _ => i)))).1
      (hmain.trans (congrArg (fun u => gs (ρT x0 d m).left y ⊤ (v (m + 1)) * (u : (_ : Type)ˣ).val) hunit.symm))
    have h3 := gs_pull (𝟙 _) (ρT x0 d m).left y ⊤ (by trivial) (v (m + 1))
    rw [Category.id_comp] at h3
    exact h2.trans h3.symm
  choose a ha using fun m => (⟨_, congrArg (fun f => CommRingCat.Hom.hom f (v m))
    (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of (Jet S (Fin 1 × Fin d) m))))⟩ :
      ∃ b, toΓ (Jet S (Fin 1 × Fin d) m) b = v m)
  have hac : ∀ m, (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] _) (a (m + 1)) = a m := by
    intro m
    apply toΓ_injective
    rw [ha m, hvc m, ← ha (m + 1)]
    exact congrArg (fun f => CommRingCat.Hom.hom f (a (m + 1)))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ((jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] _) :
        Jet S (Fin 1 × Fin d) (m + 1) →+* Jet S (Fin 1 × Fin d) m)))
  obtain ⟨f, hf⟩ := exists_ps_of_jets a hac
  refine ⟨f, fun m => ⟨F' m, τ m, hF' m, hcorr m, ?_⟩⟩
  rw [hf m, ha m]
  exact hv m

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrC
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := by
  first
  | exact spMap_id R
  | exact spMap_id
  | simp [spMap]
  | unfold spMap

theorem spMap_alg_self (R : Type) [CommRing R] : spMap (algebraMap R R) = 𝟙 (Sp R) := by
  first
  | exact spMap_id' R
  | (rw [Algebra.algebraMap_self]; exact spMap_id' R)

theorem spMap_algHom_alg {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : A →ₐ[R] B) : spMap (φ : A →+* B) ≫ spMap (algebraMap R A) = spMap (algebraMap R B) := by
  first
  | (rw [← spMap_comp]; congr 1; exact φ.comp_algebraMap)
  | (rw [spMap_comp]; congr 1; exact φ.comp_algebraMap)
  | (simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap])
  | unfold spMap

theorem jetCoef_substP {V K : Type} [CommRing V] [CommRing K] (f : V →+* K) {κ κ' : Type} (m : ℕ)
    (φ : κ → MvPolynomial κ' V) :
    (jetCoef f κ' m).comp ((jetSubstP m φ : Jet V κ m →ₐ[V] Jet V κ' m) : Jet V κ m →+* Jet V κ' m) =
      ((jetSubstP m (fun i => MvPolynomial.map f (φ i)) : Jet K κ m →ₐ[K] Jet K κ' m) : Jet K κ m →+* Jet K κ' m).comp
        (jetCoef f κ m) := by
  have keyV : ∀ (ψ : κ → MvPolynomial κ' V) (j : κ),
      (jetSubstP m ψ : Jet V κ m →ₐ[V] Jet V κ' m) (Ideal.Quotient.mk _ (MvPolynomial.X j)) =
        Ideal.Quotient.mk _ (ψ j - MvPolynomial.C (MvPolynomial.constantCoeff (ψ j))) := fun ψ j =>
    congrArg (Ideal.Quotient.mk _) (MvPolynomial.bind₁_X_right _ j)
  have keyK : ∀ (ψ : κ → MvPolynomial κ' K) (j : κ),
      (jetSubstP m ψ : Jet K κ m →ₐ[K] Jet K κ' m) (Ideal.Quotient.mk _ (MvPolynomial.X j)) =
        Ideal.Quotient.mk _ (ψ j - MvPolynomial.C (MvPolynomial.constantCoeff (ψ j))) := fun ψ j =>
    congrArg (Ideal.Quotient.mk _) (MvPolynomial.bind₁_X_right _ j)
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro v
    have e2 : ∀ (κ'' : Type), jetCoef f κ'' m (algebraMap V (Jet V κ'' m) v) =
        algebraMap K (Jet K κ'' m) (f v) := by
      intro κ''
      show jetCoef f κ'' m (Ideal.Quotient.mk _ (MvPolynomial.C v)) = Ideal.Quotient.mk _ (MvPolynomial.C (f v))
      simp [jetCoef]
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom]
    rw [show (Ideal.Quotient.mk (orig V κ ^ (m + 1))) (MvPolynomial.C v) = algebraMap V (Jet V κ m) v from rfl]
    rw [AlgHom.commutes, e2, e2, AlgHom.commutes]
  · intro i
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom]
    rw [keyV φ i]
    have eX : jetCoef f κ m (Ideal.Quotient.mk _ (MvPolynomial.X i)) = Ideal.Quotient.mk _ (MvPolynomial.X i) := by
      simp [jetCoef]
    rw [eX, keyK]
    set_option synthInstance.maxHeartbeats 200000 in
      simp [jetCoef, MvPolynomial.constantCoeff_map]

theorem unit_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : η[G'].left ≫ φ = f ≫ η[G].left := by
  obtain ⟨hpb, hmul⟩ := h
  let x₀ : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G := Over.homMk (η[G'].left ≫ φ) (by
    show (η[G'].left ≫ φ) ≫ G.hom = (𝟙_ (Over S')).hom ≫ f
    rw [Category.assoc, hpb.w, ← Category.assoc, Over.w η[G']])
  have hη : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by
    show toUnit (𝟙_ (Over S')) ≫ η[G'] = η[G']
    first
    | rw [toUnit_unit, Category.id_comp]
    | rw [Subsingleton.elim (toUnit (𝟙_ (Over S'))) (𝟙 _), Category.id_comp]
  have h2 := hmul (𝟙_ (Over S')) η[G'] η[G'] x₀ x₀ rfl rfl
  have hidem : x₀ * x₀ = x₀ := by
    apply Over.OverMorphism.ext
    rw [h2, ← hη, _root_.one_mul]
    rfl
  have h1 : x₀ = 1 := by
    first
    | exact mul_eq_left.1 hidem
    | exact mul_right_eq_self.1 hidem
  have h3 : x₀.left = (toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ f)) ≫ η[G]).left :=
    congrArg (fun g => g.left) h1
  rw [Over.comp_left] at h3
  have h4 : (toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ f))).left = f := by
    first
    | simp
    | simpa using Over.w (toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ f)))
  rw [h4] at h3
  exact h3

section Pt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
variable (I : IntData Xo c T io y.1) {d : ℕ} (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G)

theorem xL_zero (hz : ∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp T.V)) (jetAug : Jet T.V (Fin 1 × Fin d) m →ₐ[T.V] T.V) ≫ xT m = 1)
    (m : ℕ) : spMap ((jetAug : Jet T.Fr (Fin 1 × Fin d) m →ₐ[T.Fr] T.Fr) : Jet T.Fr (Fin 1 × Fin d) m →+* T.Fr) ≫
      xL I xT m = η[I.t'.G].left := by
  apply ext2 I
  · rw [Category.assoc, xL_fst, ← Category.assoc, spMap_comp', jetCoef_aug, ← spMap_comp', Category.assoc,
      unit_push I.m2.cart]
    have e := congrArg CommaMorphism.left (hz m)
    change spMap _ ≫ (xT m).left = (spMap (algebraMap T.V T.V) ≫ 𝟙 _) ≫ η[I.G.G].left at e
    rw [e, spMap_alg_self, Category.id_comp, Category.id_comp]
  · rw [Category.assoc, xL_snd, spMap_algHom_alg, spMap_alg_self, Over.w η[I.t'.G]]
    rfl

theorem xL_trunc (ht : ∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp T.V))
      (jetTrunc : Jet T.V (Fin 1 × Fin d) (m + 1) →ₐ[T.V] Jet T.V (Fin 1 × Fin d) m) ≫ xT (m + 1) = xT m)
    (m : ℕ) : spMap ((jetTrunc : Jet T.Fr (Fin 1 × Fin d) (m + 1) →ₐ[T.Fr] Jet T.Fr (Fin 1 × Fin d) m) :
      Jet T.Fr (Fin 1 × Fin d) (m + 1) →+* Jet T.Fr (Fin 1 × Fin d) m) ≫ xL I xT (m + 1) = xL I xT m := by
  apply ext2 I
  · rw [Category.assoc, xL_fst, xL_fst, ← Category.assoc, spMap_comp', jetCoef_trunc, ← spMap_comp',
      Category.assoc]
    exact congrArg (spMap (jc (d := d) 1 m) ≫ ·) (congrArg CommaMorphism.left (ht m))
  · rw [Category.assoc, xL_snd, xL_snd, spMap_algHom_alg]

theorem xL_act (actT : Fin d → MvPowerSeries (Fin 1 × Fin d) T.V) (a : 𝓞 E) (m : ℕ) (ha : xT m ≫ I.G.act.act a =
      Formalism.L2.Pj.homAt (𝟙 (Sp T.V)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (actT p.2)) ≫ xT m) :
    xL I xT m ≫ (I.t'.act.act a).left =
      spMap ((jetSubstP m fun p : Fin 1 × Fin d => MvPolynomial.map (algebraMap T.V T.Fr) (psTrunc m (actT p.2)) :
        Jet T.Fr (Fin 1 × Fin d) m →ₐ[T.Fr] Jet T.Fr (Fin 1 × Fin d) m) :
          Jet T.Fr (Fin 1 × Fin d) m →+* Jet T.Fr (Fin 1 × Fin d) m) ≫ xL I xT m := by
  apply ext2 I
  · rw [Category.assoc, I.m2.act a, ← Category.assoc, xL_fst, Category.assoc, Category.assoc, xL_fst,
      ← Category.assoc (spMap _) (spMap _), spMap_comp', ← jetCoef_substP, ← spMap_comp', Category.assoc]
    exact congrArg (spMap (jc (d := d) 1 m) ≫ ·) (congrArg CommaMorphism.left ha)
  · rw [Category.assoc, Over.w (I.t'.act.act a), Category.assoc, xL_snd, spMap_algHom_alg]

end Pt

end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GPowSt
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

def PowOActSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t)
    (n : ℕ) (D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre P.D.toPre n),
    letI := H.starRing
    ∃ M : Module (𝓞 E) D'.toPre.X,
      letI := M
      ∃ oD' : D'.toPre.OAct (𝓞 E),
        (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) ∧
        ∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.BoxTuple
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)
open IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

namespace BoxTuple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

def BoxTup (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (Q : P.D.toPre.X → ℤ)
    (F : Type) [Field F] [Algebra T.Fr F] [Algebra T.V F] (v : AddValuation F (WithTop ℚ)) (g g' : ℕ) (π : 𝓞 E)
    {n : ℕ} {D' : DegData T.V (maximalIdeal T.V)} {A' : PolAV (Spec (CommRingCat.of T.Fr))} {G' : Over (Sp T.V)}
    [GrpObj G'] [IsCommMonObj G'] {pD : IsPowDeg D'.toPre P.D.toPre n} {pA : IsPowPolAV A' P.A n}
    (pG : IsPowGrp G' C.I.G.G n) {U' : Unif (maximalIdeal T.V) D' A' G'} (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E))
    (s : Fam D'.toPre F g') (s₂ : Fam D'.toPre F (g' * g)) (p : QkPt D'.toPre F (g' * g))
    (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (g' * g))))
    (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (g' * g))
    (σ' : U'.toUnifPre.SecGF F (g' * g)) (h : PS F n (chD C.ch)) : Prop :=
  NuGe D' (sumQ pD.xe Q) F v g' s 0 ∧
  PullAl D' F oD' (star π) g' g s s₂ ∧
  (w.IsGen ∧ ζ ≠ 0 ∧ FinOrd D' F (g' * g) p w ζ) ∧
  QkToAkU U'.toUnifPre F (g' * g) p x ∧ (∀ i, x ≫ pA.pr i ≫ P.oA.act π = 1) ∧
  PhiRel D'.toPre F (g' * g) p w s₂ t₀ ∧ Fam.IsSmul D'.toPre F ζ t₀ t ∧
  U'.toUnifPre.ExpandsG F (g' * g) σ' t ∧
  IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (g' * g) σ' h

end BoxTuple

open BoxTuple

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetSubSt
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def ChartJetTanSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (d : ℕ)
    (FT : Fin d → Germ.PS T.V 2 d) (actT : 𝓞 E → Fin d → Germ.PS T.V 1 d)
    (tgT : Fin d → (Sp (DualNumber T.V) ⟶ I.G.G.left)) (uvecT : Lt1 Dw → Fin d → T.V)
    (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G),
    ((∀ j, IsTanAtG I.G (𝟙 (Sp T.V)) (tgT j)) ∧
      ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w → ∃! a : Fin d → T.V, IsCombAtG I.G (𝟙 (Sp T.V)) tgT a w) →
    IsChartG I.G (𝟙 (Sp T.V)) d FT actT tgT (fun j : Fin d => Pi.single j (1 : T.V)) xT →
    (∀ ℓ : Lt1 Dw, IsCombAtG I.G (𝟙 (Sp T.V))
      (fun j : Fin d => (Formalism.L2.Pj.homAt (𝟙 (Sp T.V))
        (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin d) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left)
      (uvecT ℓ) (I.ub ℓ.1 ℓ.2).left) →
    letI := io.toAlgebra
    ∀ ℓ : Lt1 Dw, IsCombAt y.1.x
      (fun j : Fin d => (Formalism.L2.Pj.homAt y.1.x
        (jetTan ((0 : Fin 1), j) : Jet T.Fr (Fin 1 × Fin d) (0 + 1) →ₐ[T.Fr] DualNumber T.Fr) ≫ JetTr.xU I xT 1).left)
      (fun i => algebraMap T.V T.Fr (uvecT ℓ i)) (y.1.u ℓ.1 ℓ.2)

def ChartJetBasisSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (d : ℕ)
    (FT : Fin d → Germ.PS T.V 2 d) (actT : 𝓞 E → Fin d → Germ.PS T.V 1 d)
    (tgT : Fin d → (Sp (DualNumber T.V) ⟶ I.G.G.left)) (uvecT : Lt1 Dw → Fin d → T.V)
    (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G),
    ((∀ j, IsTanAtG I.G (𝟙 (Sp T.V)) (tgT j)) ∧
      ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w → ∃! a : Fin d → T.V, IsCombAtG I.G (𝟙 (Sp T.V)) tgT a w) →
    IsChartG I.G (𝟙 (Sp T.V)) d FT actT tgT (fun j : Fin d => Pi.single j (1 : T.V)) xT →
    (∀ ℓ : Lt1 Dw, IsCombAtG I.G (𝟙 (Sp T.V))
      (fun j : Fin d => (Formalism.L2.Pj.homAt (𝟙 (Sp T.V))
        (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin d) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left)
      (uvecT ℓ) (I.ub ℓ.1 ℓ.2).left) →
    ∀ v : Fin d → T.Fr, ∃! a : Lt1 Dw → T.Fr, ∀ j, ∑ ℓ, a ℓ * algebraMap T.V T.Fr (uvecT ℓ j) = v j

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBFr
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

attribute [local instance] Over.cartesianMonoidalCategory

section Pt

variable {S Idx : Type} [CommRing S]

instance jetAug_isLocalHom (m : ℕ) : IsLocalHom ((jetAug : Jet S Idx m →ₐ[S] S) : Jet S Idx m →+* S) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨c, hc⟩ := @jet_exists_nil S Idx _ m a
  have hn : IsNilpotent ((jetAug : Jet S Idx m →ₐ[S] S) (a - algebraMap S _ c)) := hc.map _
  rw [map_sub, AlgHom.commutes] at hn
  have hcu : IsUnit c := by
    have := hn.neg.isUnit_add_left_of_commute ha (Commute.all _ _)
    simpa using this
  have := hc.isUnit_add_left_of_commute (hcu.map (algebraMap S (Jet S Idx m))) (Commute.all _ _)
  simpa using this

theorem pre_top [IsLocalRing S] (m : ℕ) {X : Scheme.{0}} (U : X.Opens) (ψ : Sp (Jet S Idx m) ⟶ X) (e : Sp S ⟶ X)
    (he : spMap ((jetAug : Jet S Idx m →ₐ[S] S) : Jet S Idx m →+* S) ≫ ψ = e) (hU : e ⁻¹ᵁ U = ⊤) : ψ ⁻¹ᵁ U = ⊤ := by
  apply ReciprocityTheory.ChartRestriction.G.DVR.eq_top_of_closedPoint_mem
  have h1 : (IsLocalRing.closedPoint S : Sp S) ∈ e ⁻¹ᵁ U := by rw [hU]; trivial
  have h2 : (spMap ((jetAug : Jet S Idx m →ₐ[S] S) : Jet S Idx m →+* S)).base (IsLocalRing.closedPoint S) =
      IsLocalRing.closedPoint (Jet S Idx m) :=
    IsLocalRing.comap_closedPoint ((jetAug : Jet S Idx m →ₐ[S] S) : Jet S Idx m →+* S)
  rw [← he] at h1
  show ψ.base (IsLocalRing.closedPoint (Jet S Idx m)) ∈ U
  rw [← h2]
  exact h1

theorem psum_one {X0 : Scheme.{0}} (G : Over X0) [GrpObj G] [IsCommMonObj G] {T : Over X0} {n : ℕ}
    (I : Finset (Fin n)) : psum G (fun _ => (1 : T ⟶ G)) I = 1 := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => rfl
  | cons k l ih => exact (congrArg (padd G 1) ih).trans (_root_.one_mul (1 : T ⟶ G))

theorem aug_copy {d n : ℕ} (m : ℕ) (i : Fin n) :
    (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S).comp (jetCopy d m i) = jetAug := by
  apply jet_hom_ext
  intro p
  show MvPolynomial.aeval (fun _ => (0 : S))
      (MvPolynomial.aeval (fun q : Fin 1 × Fin d => (MvPolynomial.X (i, q.2) : MvPolynomial (Fin n × Fin d) S))
        (MvPolynomial.X p)) = MvPolynomial.aeval (fun _ => (0 : S)) (MvPolynomial.X p)
  simp

end Pt

section Axes

theorem prod_cube2 {X0 : Scheme.{0}} (G : Over X0) [GrpObj G] [IsCommMonObj G] {T : Over X0} {M : Type} [CommGroup M]
    (h : (T ⟶ G) → M) (xs : Fin 2 → (T ⟶ G)) :
    ∏ I : ULift (Finset (Fin 2)), h (psum G xs I.down) ^ cε 2 I =
      h 1 * (h (xs 0 * 1))⁻¹ * (h (xs 1 * 1))⁻¹ * h (xs 0 * (xs 1 * 1)) := by
  refine (Fintype.prod_equiv Equiv.ulift _ (fun I : Finset (Fin 2) => h (psum G xs I) ^ cε 2 ⟨I⟩) (fun _ => rfl)).trans ?_
  have hu : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [hu, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have c0 : cε 2 ⟨(∅ : Finset (Fin 2))⟩ = 1 := rfl
  have c1 : cε 2 ⟨({0} : Finset (Fin 2))⟩ = -1 := rfl
  have c2 : cε 2 ⟨({1} : Finset (Fin 2))⟩ = -1 := rfl
  have c3 : cε 2 ⟨({0, 1} : Finset (Fin 2))⟩ = 1 := rfl
  have p0 : psum G xs ∅ = 1 := rfl
  have p1 : psum G xs {0} = xs 0 * 1 := rfl
  have p2 : psum G xs {1} = xs 1 * 1 := rfl
  have p3 : psum G xs {0, 1} = xs 0 * (xs 1 * 1) := rfl
  rw [c0, c1, c2, c3, p0, p1, p2, p3]
  simp only [zpow_one, zpow_neg, _root_.mul_assoc]

variable {S : Type} [CommRing S]

theorem jetAug_X {Idx : Type} (m : ℕ) (q : Idx) :
    (jetAug : Jet S Idx m →ₐ[S] S) (Ideal.Quotient.mk _ (MvPolynomial.X q)) = 0 := by
  show MvPolynomial.aeval (fun _ => (0 : S)) (MvPolynomial.X q) = 0
  simp

variable (d : ℕ)

abbrev axis0 (m : ℕ) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2

abbrev axis1 (m : ℕ) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun _ => 0] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2

theorem first_axis_at_first_copy (m : ℕ) : (axis0 (S := S) d m).comp (jetCopy d m (0 : Fin 2)) =
    (Algebra.ofId S (Jet S (Fin 1 × Fin d) m)).comp jetAug := by
  apply jet_hom_ext
  rintro ⟨i, j⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [jetSubstP, jetCopy, jetMap_mk, jetAug_X]

theorem first_axis_at_second_copy (m : ℕ) : (axis0 (S := S) d m).comp (jetCopy d m (1 : Fin 2)) = AlgHom.id S _ := by
  apply jet_hom_ext
  rintro ⟨i, j⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [jetSubstP, jetCopy, jetMap_mk]

theorem second_axis_at_first_copy (m : ℕ) : (axis1 (S := S) d m).comp (jetCopy d m (0 : Fin 2)) = AlgHom.id S _ := by
  apply jet_hom_ext
  rintro ⟨i, j⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [jetSubstP, jetCopy, jetMap_mk]

theorem second_axis_at_second_copy (m : ℕ) : (axis1 (S := S) d m).comp (jetCopy d m (1 : Fin 2)) =
    (Algebra.ofId S (Jet S (Fin 1 × Fin d) m)).comp jetAug := by
  apply jet_hom_ext
  rintro ⟨i, j⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [jetSubstP, jetCopy, jetMap_mk, jetAug_X]

end Axes

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] [IsLocalRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

abbrev e0 : Sp S ⟶ t.G.left := (1 : overAt x0 S ⟶ t.G).left

theorem exists_chart_covering_index : ∃ i0 : t.PP.L.ι, (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤ := by
  obtain ⟨j, hj⟩ := ReciprocityTheory.ChartRestriction.G.DVR.exists_chart_top (V := S) t.PP.L t.PP.isLB (fun _ : Fin 1 => e0 t x0)
    (fun _ => 1)
  exact ⟨j 0, top_unique (by rw [← hj]; exact LB.wchart_le _ _ j 0)⟩

theorem vec2 {α : Type*} (f : Fin 2 → α) : (![f 0, f 1] : Fin 2 → α) = f := by
  funext i
  fin_cases i <;> rfl

variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}

variable {t x0 d x} in
theorem jpt_aug (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) {n : ℕ} (i : Fin n) :
    homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S) ≫ jptG t x0 d x m i = 1 := by
  rw [jptG, ← Category.assoc, homAt_comp, aug_copy, hch.zero m]

variable {t x0 d x} in
theorem jpt_trunc (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) {n : ℕ} (i : Fin n) :
    homAt x0 (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] _) ≫ jptG t x0 d x (m + 1) i = jptG t x0 d x m i := by
  have hc : (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] _).comp (jetCopy d (m + 1) i) =
      (jetCopy d m i).comp (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] _) := by
    apply jet_hom_ext
    intro p
    rfl
  rw [jptG, jptG, ← Category.assoc, homAt_comp, hc, ← homAt_comp, Category.assoc, hch.trunc m]

theorem psum_aug {m n : ℕ} (xs : Fin n → (jOG x0 d m n ⟶ t.G))
    (hxs : ∀ i, homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S) ≫ xs i = 1) (I : Finset (Fin n)) :
    homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S) ≫ psum t.G xs I = 1 :=
  (psum_hom (preHom (homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S))) xs I).trans
    ((congrArg (fun f => psum t.G f I) (funext hxs)).trans (psum_one t.G I))

theorem wchart_top (i0 : t.PP.L.ι) (hi0 : (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤) {m n : ℕ}
    (xs : Fin n → (jOG x0 d m n ⟶ t.G))
    (hxs : ∀ i, homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S) ≫ xs i = 1) :
    LB.wchart t.PP.L (cφG t xs) (fun _ => i0) = ⊤ := by
  refine top_unique fun y _ => Set.mem_iInter.2 fun I => ?_
  have h := pre_top m (t.PP.L.U i0) (cφG t xs I) (e0 t x0)
    (congrArg Over.Hom.left (psum_aug t x0 d xs hxs I.down)) hi0
  have : y ∈ (cφG t xs I) ⁻¹ᵁ t.PP.L.U i0 := by rw [h]; trivial
  exact this


variable {t x0 d x} in
def fr (hch : IsChartG t x0 d F act tg uvec x) (i0 : t.PP.L.ι) (hi0 : (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤) (m : ℕ) :
    LB.Gen (LB.LinComb t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2)) :=
  cgen t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (fun _ => i0)
    (wchart_top t x0 d i0 hi0 _ fun i => by rw [vec2 (fun i => jptG t x0 d x m i)]; exact jpt_aug hch m i)

variable {t x0 d x} in
theorem fr_trunc (hch : IsChartG t x0 d F act tg uvec x) (i0 : t.PP.L.ι) (hi0 : (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤) :
    FrTrunc t x0 d x (fr hch i0 hi0) := fun m => corr_of_val t.PP.isLB fun y J hJ => by
  have hmor : ∀ I : ULift (Finset (Fin 2)),
      (𝟙 _ ≫ (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _)).left) ≫
        cφG t ![jptG t x0 d x (m + 1) (0 : Fin 2), jptG t x0 d x (m + 1) (1 : Fin 2)] I =
      𝟙 _ ≫ cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I := by
    intro I
    rw [Category.id_comp, Category.id_comp, vec2 (fun i => jptG t x0 d x (m + 1) i),
      vec2 (fun i => jptG t x0 d x m i)]
    simp only [cφG, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    exact congrArg (fun f => psum t.G f I.down) (funext fun i => jpt_trunc hch m i)
  exact (val_pull hJ _ _ _).trans ((val_cgen _ _ _ _ _ _ y J hJ).trans
    (Eq.trans (Finset.prod_congr rfl fun I _ => congrArg (fun ψ => cv t.PP.L i0 y J ψ ^ cε 2 I) (hmor I))
      (val_cgen _ _ _ _ _ _ y J hJ).symm))

variable {t x0 d x} in
theorem fr_axes (hch : IsChartG t x0 d F act tg uvec x) (i0 : t.PP.L.ι) (hi0 : (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤) :
    FrAxes t x0 d x (fr hch i0 hi0) := by
  have hL := t.PP.isLB
  have key : ∀ (m : ℕ) (σ : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 1 × Fin d) m) (a b : jOG x0 d m 1 ⟶ t.G),
      homAt x0 σ ≫ jptG t x0 d x m (0 : Fin 2) = a → homAt x0 σ ≫ jptG t x0 d x m (1 : Fin 2) = b → (a = 1 ∨ b = 1) →
      LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)])
        (cε 2) (fr hch i0 hi0 m) (homAt x0 σ).left) (LB.oneGen t.PP.L) := by
    intro m σ a b ha hb hab
    refine corr_of_val hL fun y J hJ => ?_
    refine (val_pull hJ _ _ _).trans ((val_cgen _ _ _ _ _ _ y J hJ).trans (Eq.trans ?_ (val_one _).symm))
    have hI : ∀ I : ULift (Finset (Fin 2)), (𝟙 _ ≫ (homAt x0 σ).left) ≫
        cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I = (psum t.G ![a, b] I.down).left := by
      intro I
      rw [Category.id_comp]
      simp only [cφG, ← Over.comp_left]
      refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
      refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
      fin_cases i
      · exact ha
      · exact hb
    rw [Finset.prod_congr rfl fun I _ => congrArg (fun ψ => cv t.PP.L i0 y J ψ ^ cε 2 I) (hI I)]
    have hc := prod_cube2 t.G (fun p : jOG x0 d m 1 ⟶ t.G => cv t.PP.L i0 y J p.left) ![a, b]
    rw [hc]
    rcases hab with rfl | rfl <;> simp
  intro m
  refine ⟨key m (axis0 d m) 1 (x m) ?_ ?_ (Or.inl rfl), key m (axis1 d m) (x m) 1 ?_ ?_ (Or.inr rfl)⟩
  · rw [jptG, ← Category.assoc, homAt_comp, first_axis_at_first_copy, ← homAt_comp, Category.assoc, hch.zero m]
    exact map_one (preHom (homAt x0 (Algebra.ofId S (Jet S (Fin 1 × Fin d) m))))
  · rw [jptG, ← Category.assoc, homAt_comp, first_axis_at_second_copy, homAt_id, Category.id_comp]
  · rw [jptG, ← Category.assoc, homAt_comp, second_axis_at_first_copy, homAt_id, Category.id_comp]
  · rw [jptG, ← Category.assoc, homAt_comp, second_axis_at_second_copy, ← homAt_comp, Category.assoc, hch.zero m]
    exact map_one (preHom (homAt x0 (Algebra.ofId S (Jet S (Fin 1 × Fin d) m))))

end Frames

end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
end
end
