module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GSplit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeRatio

@[expose] public section

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

section Jet

variable {S ι : Type} [CommRing S]

theorem jet_exists_nil (m : ℕ) (a : Jet S ι m) : ∃ c : S, IsNilpotent (a - algebraMap S (Jet S ι m) c) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨MvPolynomial.constantCoeff p, m + 1, ?_⟩
  have h : Ideal.Quotient.mk (orig S ι ^ (m + 1)) p - algebraMap S (Jet S ι m) (MvPolynomial.constantCoeff p) =
      Ideal.Quotient.mk _ (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) := by
    rw [map_sub]
    rfl
  rw [h, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow (sub_const_mem_orig p) _

instance jet_isLocalRing [IsLocalRing S] (m : ℕ) : IsLocalRing (Jet S ι m) := by
  have : Nontrivial (Jet S ι m) := (jetAug : Jet S ι m →ₐ[S] S).toRingHom.domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  obtain ⟨c, hc⟩ := jet_exists_nil (ι := ι) m a
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self c with h | h
  · left
    have := hc.isUnit_add_left_of_commute (h.map (algebraMap S (Jet S ι m))) (Commute.all _ _)
    simpa using this
  · right
    have := hc.neg.isUnit_add_left_of_commute (h.map (algebraMap S (Jet S ι m))) (Commute.all _ _)
    convert this using 1
    rw [map_sub, map_one]
    ring

end Jet

section Gen

variable {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']

def cgen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (j0 : K → L.ι) (h0 : LB.wchart L φ j0 = ⊤) : LB.Gen (LB.LinComb L φ ε) :=
  ⟨fun j => res (le_inf le_rfl (by rw [h0]; exact le_top) : LB.wchart L φ j ≤ LB.wchart L φ j ⊓ LB.wchart L φ j0)
    ((LB.LinComb L φ ε).g j j0)⟩

theorem cgen_isGen (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (j0 : K → L.ι) (h0 : LB.wchart L φ j0 = ⊤) :
    (cgen L φ ε j0 h0).IsGen := fun i j => unit_ext fun y hy => by
  have h0y : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ j0 := by rw [h0]; trivial
  refine (gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans ((gm_linComb L φ ε (𝟙 _) y i j0 hy.1 h0y).trans ?_))
  refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 _) y i j hy.1 hy.2)
    ((gm_res _ y _ hy _).trans ((gm_res _ y _ hy.2 _).trans (gm_linComb L φ ε (𝟙 _) y j j0 hy.2 h0y))))).symm
  exact (trF_trans hL φ ε (𝟙 _) y hy.1 hy.2 h0y).symm

def cv {Z : Scheme.{0}} (i0 : L.ι) (z : Z) (J : (Z ⟶ X) → L.ι) (ψ : Z ⟶ X) : (Z.presheaf.stalk z)ˣ :=
  gm ψ z (L.U (J ψ) ⊓ L.U i0) (L.g (J ψ) i0)

theorem val_cgen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (i0 : L.ι) (h0 : LB.wchart L φ (fun _ => i0) = ⊤) {Z : Scheme.{0}}
    (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    val (cgen L φ ε (fun _ => i0) h0) r z J = ∏ k, cv L i0 z J (r ≫ φ k) ^ ε k :=
  (gm_res r z _ (hJ.mem φ r) _).trans (gm_linComb L φ ε r z _ _ (hJ.mem φ r) (by rw [h0]; trivial))

theorem exists_ratio (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (h : FormEq φ ε φ' ε') (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (ht' : t'.IsGen) : ∃ u : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      val t r z J = gm r z ⊤ u * val t' r z J := by
  obtain ⟨s, -, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ hU => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [h U hU]
      simp only [zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ t')) (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ ht
      (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ ht'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (s.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  have e1 := hv Z r z J hJ
  rw [val_mul hJ, val_inv, val_of s r z J PEmpty.elim (fun k => k.elim)] at e1
  have e2 := (gm_res r z le trivial (s.s PEmpty.elim)).trans e1
  exact mul_inv_eq_iff_eq_mul.1 e2.symm

def divLin (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (w : LB.Gen (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε'))) :
    LB.Gen (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε fun k => -ε' k)) :=
  ⟨fun j => res (fun _ hy => ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k),
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)⟩ :
    LB.wchart L (Sum.elim φ φ') j ≤ (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U (j ∘ Sum.inl, j ∘ Sum.inr))
    (w.s (j ∘ Sum.inl, j ∘ Sum.inr))⟩

theorem gm_divLC (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (p q : (K → L.ι) × (K' → L.ι)) (y : Y) (hp : (𝟙 Y : Y ⟶ Y) y ∈ (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U p)
    (hq : (𝟙 Y : Y ⟶ Y) y ∈ (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U q) :
    gm (𝟙 Y) y _ ((LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).g p q) =
      trF φ ε (𝟙 Y) y p.1 q.1 * (trF φ' ε' (𝟙 Y) y p.2 q.2)⁻¹ := by
  have hpq : (𝟙 Y : Y ⟶ Y) y ∈ (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U p ⊓
      (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U q := ⟨hp, hq⟩
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ y _ hpq _).trans
    (gm_linComb L φ ε (𝟙 _) y p.1 q.1 hp.1 hq.1)) ((map_inv _ _).trans (congrArg _ ((gm_res _ y _ hpq _).trans
      (gm_linComb L φ' ε' (𝟙 _) y p.2 q.2 hp.2 hq.2)))))

theorem divLin_isGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (w : LB.Gen (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε'))) (hw : w.IsGen) :
    (divLin L φ ε φ' ε' w).IsGen := fun i j => unit_ext fun y hy => by
  have le : ∀ j : K ⊕ K' → L.ι, LB.wchart L (Sum.elim φ φ') j ≤
      (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U (j ∘ Sum.inl, j ∘ Sum.inr) := fun _ _ hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k), Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)⟩
  have hi := le i hy.1
  have hj := le j hy.2
  have hij : (𝟙 Y : Y ⟶ Y) y ∈ (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U (i ∘ Sum.inl, i ∘ Sum.inr) ⊓
      (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U (j ∘ Sum.inl, j ∘ Sum.inr) := ⟨hi, hj⟩
  have hw' := (gm_res (𝟙 Y) y _ hij _).symm.trans ((congrArg (gm (𝟙 Y) y _) (hw (i ∘ Sum.inl, i ∘ Sum.inr)
    (j ∘ Sum.inl, j ∘ Sum.inr))).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res (𝟙 Y) y _ hij _))))
  refine (gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans (hw'.trans ?_))
  refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _)))).symm
  refine congrArg₂ (· * ·) ((gm_divLC L φ ε φ' ε' _ _ y hi hj).trans ?_) rfl
  refine Eq.trans ?_ (gm_linComb L _ _ (𝟙 _) y i j hy.1 hy.2).symm
  rw [Fintype.prod_sum_type]
  simp only [trF, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rfl

end Gen

end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDVal
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left)

theorem exists_pullSec (a : ℤ) {T T' : Over S0} (h : T' ⊗ A ⟶ T ⊗ A) (hh : h ≫ snd T A = snd T' A)
    (s : LB.Sec (LPow A L a T)) : ∃ s', IsPullSec A L a h hh s s' := by
  have hl : ∀ j, (LPow A L a T').U j ≤ h.left ⁻¹ᵁ (LPow A L a T).U j := fun j => chart_le_res A L h hh a j
  have hc : h.left ≫ (snd T A).left = (snd T' A).left := by
    rw [← Over.comp_left, hh]
  refine ⟨⟨fun j => ((T' ⊗ A).left.presheaf.map (homOfLE (hl j)).op).hom ((h.left.app _).hom (s.f j)), ?_⟩,
    fun j => rfl⟩
  intro j j'
  apply fn_ext
  intro y hy
  have v : ∀ j, y ∈ (LPow A L a T').U j →
      gs (𝟙 _) y _ (((T' ⊗ A).left.presheaf.map (homOfLE (hl j)).op).hom ((h.left.app _).hom (s.f j))) =
        gs (𝟙 _ ≫ h.left) y ((LPow A L a T).U j) (s.f j) :=
    fun j hj => (gs_res _ y _ hj _).trans (gs_pull _ h.left y _ (hl j hj) _)
  refine ((gs_res (𝟙 _) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 _) y _ hy _ _).trans
    (congrArg₂ (· * ·) ((gs_unit (𝟙 _) y _ hy _).trans
      (congrArg Units.val (gm_linComb L _ _ (𝟙 _) y j j' hy.1 hy.2))) ((gs_res (𝟙 _) y _ hy _).trans (v j' hy.2)))).symm)
  refine (sec_trans (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (𝟙 _ ≫ h.left) y
    (hl j hy.1) (hl j' hy.2)).trans ?_
  simp only [trF, Category.assoc, hc]
  try rfl

theorem exists_value (hL : L.IsLB) (a : ℤ) {T : Over S0} (s : LB.Sec (LPow A L a T)) (z : T ⟶ A)
    (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))) (hτ : τ.IsGen) :
    ∃ v, IsValueAt A L a s z τ v := by
  have hpz : (ptSecT A z).left ≫ (snd T A).left = z.left := by
    rw [← Over.comp_left]
    simp [ptSecT]
  obtain ⟨w, hw⟩ : ∃ w : ∀ j : Fin 1 → L.ι, Γ(T.left, LB.wchart L (fun _ : Fin 1 => z.left) j),
      ∀ j, w j = (T.left.presheaf.map (homOfLE (val_le A L z j)).op).hom (((ptSecT A z).left.app _).hom (s.f j)) *
        (show Γ(T.left, LB.wchart L (fun _ : Fin 1 => z.left) j) from ((τ.s j)⁻¹).val) := ⟨_, fun _ => rfl⟩
  have loc : ∀ j x, x ∈ LB.wchart L (fun _ : Fin 1 => z.left) j →
      gs (𝟙 _) x _ (w j) = gs (𝟙 _ ≫ (ptSecT A z).left) x _ (s.f j) * ((gm (𝟙 _) x _ (τ.s j))⁻¹).val := by
    intro j x hx
    rw [hw j]
    refine (gs_mul _ x _ hx _ _).trans (congrArg₂ (· * ·) ((gs_res (𝟙 _) x (val_le A L z j) hx _).trans
      (gs_pull (𝟙 _) (ptSecT A z).left x _ (val_le A L z j hx) _)) ?_)
    exact (gs_unit (𝟙 _) x _ hx ((τ.s j)⁻¹)).trans (congrArg Units.val (map_inv _ _))
  have hcompat : TopCat.Presheaf.IsCompatible T.left.sheaf.obj (fun j : Fin 1 → L.ι => LB.wchart L (fun _ : Fin 1 => z.left) j) w := by
    intro j j'
    apply fn_ext
    intro x hx
    change gs (𝟙 _) x _ ((T.left.presheaf.map (homOfLE inf_le_left).op).hom (w j)) =
      gs (𝟙 _) x _ ((T.left.presheaf.map (homOfLE inf_le_right).op).hom (w j'))
    rw [gs_res _ x _ hx, gs_res _ x _ hx, loc j x hx.1, loc j' x hx.2]
    rw [show gs (𝟙 _ ≫ (ptSecT A z).left) x ((LPow A L a T).U j) (s.f j) = _ from
      sec_trans (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s _ x
        (val_le A L z j hx.1) (val_le A L z j' hx.2)]
    rw [show gm (𝟙 _) x ((LB.LinComb L (fun _ : Fin 1 => z.left) fun _ => a).U j) (τ.s j) = _ from
      gen_trans hτ (𝟙 _) x hx.1 hx.2]
    have ht : trF (L := L) (fun _ : Fin 1 => (snd T A).left) (fun _ => a) (𝟙 _ ≫ (ptSecT A z).left) x j j' =
        trF (L := L) (fun _ : Fin 1 => z.left) (fun _ => a) (𝟙 _) x j j' := by
      simp only [trF, Category.assoc, hpz]
    rw [ht, mul_inv_rev, Units.val_mul]
    have key : ∀ (t G : (T.left.presheaf.stalk x)ˣ) (P : T.left.presheaf.stalk x),
        (t : T.left.presheaf.stalk x) * P * (((G⁻¹ : (T.left.presheaf.stalk x)ˣ) : T.left.presheaf.stalk x) *
          ((t⁻¹ : (T.left.presheaf.stalk x)ˣ) : T.left.presheaf.stalk x)) =
          P * ((G⁻¹ : (T.left.presheaf.stalk x)ˣ) : T.left.presheaf.stalk x) := by
      intro t G P
      linear_combination (P * ((G⁻¹ : (T.left.presheaf.stalk x)ˣ) : T.left.presheaf.stalk x)) * Units.mul_inv t
    exact key _ _ _
  have hcov : (⊤ : T.left.Opens) ≤ ⨆ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => z.left) j := by
    intro x _
    have hx : z.left x ∈ (⨆ i, L.U i) := by
      rw [hL.cover]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, Set.mem_iInter.2 fun _ => hi⟩
  obtain ⟨v, hv, -⟩ := TopCat.Sheaf.existsUnique_gluing' T.left.sheaf
    (fun j : Fin 1 → L.ι => LB.wchart L (fun _ : Fin 1 => z.left) j) ⊤ (fun j => homOfLE le_top) hcov w hcompat
  refine ⟨v, fun j => ?_⟩
  have e : (T.left.presheaf.map (homOfLE le_top).op).hom v = w j := hv j
  have key : ∀ (R : Type) [CommRing R] (p : R) (t : Rˣ), p = p * ((t⁻¹ : Rˣ) : R) * (t : R) := by
    intro R _ p t
    rw [mul_assoc, Units.inv_mul, mul_one]
  rw [e, hw j]
  exact key _ _ (τ.s j)

theorem value_stalk (hL : L.IsLB) (a : ℤ) {T : Over S0} {s : LB.Sec (LPow A L a T)} {z : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (hv : IsValueAt A L a s z τ v) {Z : Scheme.{0}} (r : Z ⟶ T.left) (y : Z) (j : Fin 1 → L.ι)
    (hy : r y ∈ LB.wchart L (fun _ : Fin 1 => z.left) j) :
    gs (r ≫ (ptSecT A z).left) y _ (s.f j) = gs r y ⊤ v * (gm r y _ (τ.s j)).val := by
  have h1 := congrArg (gs r y (LB.wchart L (fun _ : Fin 1 => z.left) j)) (hv j)
  refine ((gs_pull r (ptSecT A z).left y _ (val_le A L z j hy) _).symm.trans
    ((gs_res r y (val_le A L z j) hy _).symm.trans h1)).trans ?_
  exact (gs_mul r y _ hy _ _).trans (congrArg₂ (· * ·) (gs_res r y le_top hy v) (gs_unit r y _ hy _))

theorem pullSec_stalk (a : ℤ) {T T' : Over S0} {h : T' ⊗ A ⟶ T ⊗ A} {hh : h ≫ snd T A = snd T' A}
    {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')} (hs : IsPullSec A L a h hh s s') {Z : Scheme.{0}}
    (r : Z ⟶ (T' ⊗ A).left) (y : Z) (j : Fin 1 → L.ι) (hy : r y ∈ (LPow A L a T').U j) :
    gs r y _ (s'.f j) = gs (r ≫ h.left) y _ (s.f j) := by
  rw [hs j]
  exact (gs_res r y (chart_le_res A L h hh a j) hy _).trans (gs_pull r h.left y _ (chart_le_res A L h hh a j hy) _)

end Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.LemmaBStatement
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)
open IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GSt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def leadMinor (Dw : Datum H) {n : ℕ} (K : Type) [CommRing K] (τ : E →+* ℂ) (s : ℕ) (hs : s ≤ Dw.mult τ) (cop : Fin s → Fin n) :
    MvPolynomial (LtN Dw n) K :=
  Matrix.det (Matrix.of fun (a i : Fin s) =>
    (MvPolynomial.X (⟨τ, (Fin.castLE hs a, cop i)⟩ : LtN Dw n) : MvPolynomial (LtN Dw n) K))

def minorProd (Dw : Datum H) {n : ℕ} (K : Type) [CommRing K] (typ : (E →+* ℂ) → Prop) (m : (E →+* ℂ) → ℕ → ℕ) (nb : ℕ)
    (cop : Fin nb → Fin n) : MvPolynomial (LtN Dw n) K :=
  open Classical in
  ∏ τ : E →+* ℂ, if typ τ then
    ∏ s ∈ Finset.range (Dw.mult τ + 1),
      (if h : s ≤ Dw.mult τ ∧ s ≤ nb then
        leadMinor Dw K τ s h.1 (fun i => cop (Fin.castLE h.2 i)) else 1) ^ m τ s
  else 1

def degOf (Dw : Datum H) (m : (E →+* ℂ) → ℕ → ℕ) : ℕ :=
  ∑ τ : E →+* ℂ, ∑ s ∈ Finset.range (Dw.mult τ + 1), s * m τ s

end GSt

open GSt

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqPf
section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqD
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GaugeR

def gam (A : Type) [CommRing A] : Γ(Sp A, ⊤) →+* A := (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom

theorem gam_toΓ (A : Type) [CommRing A] (a : A) : gam A (toΓ A a) = a := by
  simp [gam, toΓ]

theorem gam_pull {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : Γ(Sp A, ⊤)) :
    gam B (((spMap f).app ⊤).hom x) = f (gam A x) := by
  have h := congrArg (fun g => g.hom x) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  simp only [gam, spMap]
  exact h

theorem gam_pullUnit {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Γ(Sp A, ⊤)ˣ) :
    gam B (pullUnit (spMap f) u : Γ(Sp B, ⊤)) = f (gam A u) := by
  simp only [pullUnit, pullU, Units.coe_map, MonoidHom.coe_coe]
  exact gam_pull f (u : Γ(Sp A, ⊤))

theorem scaled_genPow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {Y : Scheme.{0}} {K : Type} [Fintype K]
    (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ) {u : Γ(Y, ⊤)ˣ}
    {t t' : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)} (h : IsScaled u t t') (k : ℕ) :
    IsScaled (u ^ k) (genPow φ ε t k) (genPow φ ε t' k) := by
  unfold IsScaled at h ⊢
  intro j
  show t'.s j ^ k = _ * t.s j ^ k
  rw [h j, mul_pow, map_pow]
  rfl

theorem value_scaled {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (hL : L.IsLB) (a : ℤ)
    {T : Over S0} (s : LB.Sec (LPow A L a T)) (z : T ⟶ A)
    (τ τ' : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)))
    (v v' : Γ(T.left, ⊤)) (U : Γ(T.left, ⊤)ˣ) (h : IsValueAt A L a s z τ v) (h' : IsValueAt A L a s z τ' v')
    (hs : IsScaled U τ τ') : v = (U : Γ(T.left, ⊤)) * v' := by
  unfold IsValueAt at h h'
  unfold IsScaled at hs
  have key : ∀ j, (T.left.presheaf.map
      (homOfLE (le_top : (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)).U j ≤ ⊤)).op).hom v =
      (T.left.presheaf.map
      (homOfLE (le_top : (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)).U j ≤ ⊤)).op).hom ((U : Γ(T.left, ⊤)) * v') := by
    intro j
    have e := (h j).symm.trans (h' j)
    have e2 := congrArg Units.val (hs j)
    simp only [res, Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at e2
    simp only [e2] at e
    rw [map_mul]
    refine (Units.mul_left_inj (τ.s j)).mp ?_
    calc _ = _ := e
      _ = _ := mul_left_comm _ _ _
      _ = _ := (mul_assoc _ _ _).symm
  have hcov : (⊤ : T.left.Opens) ≤ ⨆ j, (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)).U j := by
    intro x _
    have hx : z.left.base x ∈ (⊤ : A.left.Opens) := trivial
    rw [← hL.cover] at hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨fun _ => i, ?_⟩
    show x ∈ L.wchart (fun _ => z.left) (fun _ => i)
    unfold LB.wchart
    exact Set.mem_iInter.mpr fun _ => hi
  exact T.left.sheaf.eq_of_locally_eq' _ ⊤ (fun j => homOfLE le_top) hcov v ((U : Γ(T.left, ⊤)) * v') key

end GaugeR

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeExpPow
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR

open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

theorem cc_smul_q {S σ : Type} [CommRing S] {q : MvPowerSeries σ S} (hq : MvPowerSeries.constantCoeff q = 0)
    (r : S) : MvPowerSeries.constantCoeff (r • q) = 0 := by
  rw [MvPowerSeries.smul_eq_C_mul, map_mul, hq, mul_zero]

theorem exp_pow_eq {S σ : Type} [CommRing S] [Algebra ℚ S] (q : MvPowerSeries σ S)
    (hq : MvPowerSeries.constantCoeff q = 0) : ∀ k : ℕ,
    PowerSeries.subst q (PowerSeries.exp S) ^ k = PowerSeries.subst ((k : S) • q) (PowerSeries.exp S)
  | 0 => by rw [pow_zero, Nat.cast_zero, zero_smul, exp_zero]
  | k + 1 => by
    rw [pow_succ, exp_pow_eq q hq k, ← exp_add (ha := cc_smul_q hq (k : S)) (hb := hq), Nat.cast_succ, add_smul,
      one_smul]

theorem exp_pow_mul_exp_neg {S σ : Type} [CommRing S] [Algebra ℚ S] (q : MvPowerSeries σ S)
    (hq : MvPowerSeries.constantCoeff q = 0) (k : ℕ) :
    PowerSeries.subst q (PowerSeries.exp S) ^ k * PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S) = 1 := by
  have hneg : MvPowerSeries.constantCoeff (-((k : S) • q)) = 0 := by
    rw [map_neg, cc_smul_q hq, neg_zero]
  rw [exp_pow_eq q hq k, ← exp_add (cc_smul_q hq _) hneg, add_neg_cancel, exp_zero]

end Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
end
end

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB

attribute [local instance] Over.cartesianMonoidalCategory

namespace GaugeR

def ExpPowSt : Prop :=
  ∀ (S σ : Type) [CommRing S] [Algebra ℚ S] (q : MvPowerSeries σ S), MvPowerSeries.constantCoeff q = 0 →
    ∀ k : ℕ, PowerSeries.subst q (PowerSeries.exp S) ^ k * PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S) = 1

theorem gaugeUniq_of' (hB : BetaUniqSt) (hR : GaugeRatioSt) (hP : ExpPowSt) : GaugeUniqSt := by
  intro E _ _ _ H Dw l Xo c S _ _ _ y x hx e e' he he'
  have hL := Xo.univ.t.PP.isLB
  choose u hu using fun m => ratio_of_gen Xo.univ.t.PP.L hL (fun _ : Fin 1 => (x m).left) (fun _ => (1 : ℤ))
    (e m) (e' m) (he.gen m) (he'.gen m)
  let g : ∀ m, Jet S (Fin 1 × Fin (dL Dw)) m := fun m => gam (Jet S (Fin 1 × Fin (dL Dw)) m) (u m).val
  have hpull : ∀ (m : ℕ) (B : Type) [CommRing B] [Algebra S B] (f : Jet S (Fin 1 × Fin (dL Dw)) m →ₐ[S] B),
      gam B (pullUnit (homAt y.x f).left (u m)).val = f (g m) := fun m B _ _ f =>
    gam_pullUnit (f : Jet S (Fin 1 × Fin (dL Dw)) m →+* B) (u m)
  have htr : ∀ m, jetTrunc (g (m + 1)) = g m := by
    intro m
    have h1 := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] _)).left (hu (m + 1))
    have hU := corr_scaled Xo.univ.t.PP.L hL _ _ _ _ _ _ _ _ _ _ h1 (hu m) (he.trunc m) (he'.trunc m)
    have h2 := congrArg (fun v => gam (Jet S (Fin 1 × Fin (dL Dw)) m) (Units.val v)) hU
    exact (hpull (m + 1) _ jetTrunc).symm.trans h2
  obtain ⟨r, hr⟩ := exists_ps_of_compat g htr
  have hrig : MvPowerSeries.constantCoeff r = 1 := by
    have h1 := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left (hu 0)
    have hU := corr_scaled Xo.univ.t.PP.L hL _ _ _ _ _ _ _ _ _ _ h1 (scaled_one _) he.rig he'.rig
    have h2 := congrArg (fun v => gam S (Units.val v)) hU
    simp only [Units.val_one, map_one] at h2
    rw [← jetAug_psJet 0 r, hr 0]
    exact (hpull 0 S jetAug).symm.trans h2
  have hid : ∀ a : 𝓞 E, MvPowerSeries.rescale (sc (Dw := Dw) c S (1 + a * H.bar a)) r =
      MvPowerSeries.rescale (sc (Dw := Dw) c S a) r ^ 2 * r *
        MvPowerSeries.rescale (sc (Dw := Dw) c S (a * H.bar a)) r := by
    intro a
    obtain ⟨β, hβg, hβr, hβc⟩ := he.coc a
    obtain ⟨β', hβ'g, hβ'r, hβ'c⟩ := he'.coc a
    obtain rfl := hB E H Dw l Xo a β β' hβg hβ'g hβr hβ'r
    refine GermFun.psJet_inj fun m => ?_
    have s1 := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c (1 + a * H.bar a)))).left (hu m)
    have sa := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c a))).left (hu m)
    have sb := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c (a * H.bar a)))).left (hu m)
    have srhs := scaled_mul Xo.univ.t.PP.L _ _ _ _ (scaled_one (LB.pullGen Xo.univ.t.PP.L _ _ β (x m).left))
      (scaled_mul Xo.univ.t.PP.L _ _ _ _ (scaled_genPow _ _ sa 2) (scaled_mul Xo.univ.t.PP.L _ _ _ _ (hu m) sb))
    have hU := corr_scaled Xo.univ.t.PP.L hL _ _ _ _ _ _ _ _ _ _ s1 srhs (hβc m) (hβ'c m)
    have hv := congrArg (fun v => gam (Jet S (Fin 1 × Fin (dL Dw)) m) (Units.val v)) hU
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, one_mul] at hv
    rw [hpull, hpull, hpull] at hv
    have hv' : jetSubstP m (fun i => MvPolynomial.C (sc (Dw := Dw) c S (1 + a * H.bar a) i) * MvPolynomial.X i) (g m) =
        jetSubstP m (fun i => MvPolynomial.C (sc (Dw := Dw) c S a i) * MvPolynomial.X i) (g m) ^ 2 *
          (g m * jetSubstP m (fun i => MvPolynomial.C (sc (Dw := Dw) c S (a * H.bar a) i) * MvPolynomial.X i) (g m)) :=
      hv
    rw [psJet_mul, psJet_mul, psJet_pow, ← jetSubstP_scale, ← jetSubstP_scale, ← jetSubstP_scale, hr m, hv']
    ring
  obtain ⟨q, hq0, hdeg, hpair, hexp⟩ := ratio_exp hR c S r hrig hid
  refine ⟨q, hq0, hdeg, hpair, fun k F f f' hf hf' => ?_⟩
  refine GermFun.psJet_inj fun m => ?_
  obtain ⟨F₁, τ₁, hP₁, hC₁, hV₁⟩ := hf m
  obtain ⟨F₂, τ₂, hP₂, hC₂, hV₂⟩ := hf' m
  have hF := GermFun.pull_unique _ _ _ _ _ _ _ _ hP₁ hP₂
  subst hF
  have sg := scaled_genPow (fun _ : Fin 1 => (x m).left) (fun _ => (1 : ℤ)) (hu m) k
  have sτ := corr_scaled_left Xo.univ.t.PP.L hL (x m).left (k : ℤ) _ _ τ₁ τ₂ _ _ _ sg hC₁ hC₂
  have hval := value_scaled Xo.univ.t.G Xo.univ.t.PP.L hL (k : ℤ) _ (x m) τ₁ τ₂ _ _ _ hV₁ hV₂ sτ
  have hg := congrArg (gam (Jet S (Fin 1 × Fin (dL Dw)) m)) hval
  rw [gam_toΓ, map_mul, gam_toΓ, Units.val_pow_eq_pow_val, map_pow] at hg
  have hpow := congrArg (psJet m) (hP S _ q hq0 k)
  rw [psJet_mul, psJet_pow, ← hexp, hr m, psJet_one] at hpow
  rw [psJet_mul, hg]
  calc psJet m f' = psJet m f' * (g m ^ k * psJet m (PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S))) := by
        rw [hpow, mul_one]
    _ = _ := by ring

end GaugeR

theorem gaugeUniq_of (hB : BetaUniqSt) : GaugeUniqSt :=
  GaugeR.gaugeUniq_of' hB GRPf.gaugeRatio fun _ _ _ _ q hq k => GaugeR.exp_pow_mul_exp_neg q hq k

theorem gaugeUniq_of_global (hG : GlobalFnsSt) : GaugeUniqSt :=
  gaugeUniq_of (betaUniq_of_global hG)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartFrameTrA
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

theorem glue_units {X : Scheme.{0}} {κ : Type} (U : κ → X.Opens) (hcov : ∀ x : X, ∃ i, x ∈ U i)
    (r : ∀ i, Γ(X, U i)ˣ)
    (hr : ∀ i j, res (inf_le_left : U i ⊓ U j ≤ U i) (r i) = res (inf_le_right : U i ⊓ U j ≤ U j) (r j)) :
    ∃ u : Γ(X, ⊤)ˣ, ∀ i, res (le_top : U i ≤ ⊤) u = r i := by
  simp only [res] at hr ⊢
  have hc : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    obtain ⟨i, hi⟩ := hcov x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  obtain ⟨s, hs, -⟩ : ∃! s : Γ(X, ⊤), ∀ i,
      (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom s = (r i : Γ(X, U i)) :=
    X.sheaf.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top) hc
    (fun i => ((r i : Γ(X, U i)))) (fun i j => by
      have h1 := congrArg Units.val (hr i j)
      simp only [Units.coe_map, MonoidHom.coe_coe] at h1
      exact h1)
  obtain ⟨t, ht, -⟩ : ∃! t : Γ(X, ⊤), ∀ i,
      (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom t = (((r i)⁻¹ : Γ(X, U i)ˣ) : Γ(X, U i)) :=
    X.sheaf.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top) hc
    (fun i => (((r i)⁻¹ : Γ(X, U i)ˣ) : Γ(X, U i))) (fun i j => by
      have h1 := congrArg (fun v => ((v⁻¹ : Γ(X, U i ⊓ U j)ˣ) : Γ(X, U i ⊓ U j))) (hr i j)
      simp only [← map_inv, Units.coe_map, MonoidHom.coe_coe] at h1
      exact h1)
  have hs' : ∀ i, (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom s = (r i : Γ(X, U i)) :=
    fun i => hs i
  have ht' : ∀ i, (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom t =
      (((r i)⁻¹ : Γ(X, U i)ˣ) : Γ(X, U i)) := fun i => ht i
  have hst : s * t = 1 := by
    apply X.sheaf.eq_of_locally_eq' U ⊤ (fun i => homOfLE le_top) hc
    intro i
    show (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom (s * t) =
      (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom 1
    rw [map_mul, map_one, hs' i, ht' i, Units.mul_inv]
  refine ⟨⟨s, t, hst, by rw [mul_comm]; exact hst⟩, fun i => ?_⟩
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_mk]
  exact hs' i

theorem exists_ratio_gen {X : Scheme.{0}} {M : LB X} (hcov : ∀ x : X, ∃ i, x ∈ M.U i) {g₁ g₂ : LB.Gen M}
    (h₁ : g₁.IsGen) (h₂ : g₂.IsGen) : ∃ u : Γ(X, ⊤)ˣ, ∀ i, g₁.s i = res (le_top : M.U i ≤ ⊤) u * g₂.s i := by
  unfold LB.Gen.IsGen at h₁ h₂
  obtain ⟨u, hu⟩ := glue_units M.U hcov (fun i => g₁.s i / g₂.s i) (fun i j => by
    rw [map_div, map_div, h₁ i j, h₂ i j, mul_div_mul_left_eq_div])
  exact ⟨u, fun i => by rw [hu i, div_mul_cancel]⟩

theorem unit_eq_one_of_eSec (hGF : GlobalFnsSt) {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A)
    (u : Γ(A.left, ⊤)ˣ) (h : (eSec A).appTop.hom u.val = 1) : u = 1 := by
  unfold GlobalFnsSt at hGF
  have hsec : eSec A ≫ A.hom = 𝟙 S := by
    unfold eSec
    rw [Over.w]
    rfl
  obtain ⟨s, hs⟩ := (hGF S A hA).2 u.val
  have h2 : (Scheme.Hom.appTop (eSec A ≫ A.hom)).hom s = s := by
    rw [hsec]
    simp
  have hs1 : s = 1 := by
    calc s = (Scheme.Hom.appTop (eSec A ≫ A.hom)).hom s := h2.symm
      _ = (Scheme.Hom.appTop (eSec A)).hom ((Scheme.Hom.appTop A.hom).hom s) := rfl
      _ = 1 := by rw [hs, h]
  ext
  rw [← hs, hs1, map_one]
  rfl

end Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrB
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  simp only [spMap]
  rw [← Spec.map_comp]
  rfl

section Pt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
variable (I : IntData Xo c T io y.1) {d : ℕ} (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G)

abbrev jc (n m : ℕ) : Jet T.V (Fin n × Fin d) m →+* Jet T.Fr (Fin n × Fin d) m :=
  jetCoef (algebraMap T.V T.Fr) (Fin n × Fin d) m

theorem xL_w (m : ℕ) : (spMap (jc (d := d) 1 m) ≫ (xT m).left) ≫ I.G.G.hom =
    spMap (algebraMap T.Fr (Jet T.Fr (Fin 1 × Fin d) m)) ≫ spMap (algebraMap T.V T.Fr) := by
  rw [Category.assoc, Over.w]
  simp only [spMap_comp']
  simp only [jOG, Over.mk_hom, Category.comp_id, spMap_comp']
  congr 1
  ext r
  simp only [jc, jetCoef, RingHom.comp_apply]
  erw [Ideal.Quotient.lift_mk]
  simp only [RingHom.comp_apply, MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
  rfl

def xL (m : ℕ) : Sp (Jet T.Fr (Fin 1 × Fin d) m) ⟶ I.t'.G.left :=
  I.m2.cart.1.lift (spMap (jc (d := d) 1 m) ≫ (xT m).left) (spMap (algebraMap T.Fr (Jet T.Fr (Fin 1 × Fin d) m)))
    (xL_w I xT m)

theorem xL_fst (m : ℕ) : xL I xT m ≫ I.m2.φ = spMap (jc (d := d) 1 m) ≫ (xT m).left := I.m2.cart.1.lift_fst _ _ _

theorem xL_snd (m : ℕ) : xL I xT m ≫ I.t'.G.hom = spMap (algebraMap T.Fr (Jet T.Fr (Fin 1 × Fin d) m)) := I.m2.cart.1.lift_snd _ _ _

def xP (m : ℕ) : jOG (𝟙 (Sp T.Fr)) d m 1 ⟶ I.t'.G :=
  Over.homMk (xL I xT m) (by
    show xL I xT m ≫ I.t'.G.hom = spMap _ ≫ 𝟙 _
    rw [xL_snd, Category.comp_id])

def xU (m : ℕ) : (letI := io.toAlgebra; jO y.1 d m 1) ⟶ Xo.univ.t.G :=
  letI := io.toAlgebra
  Over.homMk (xL I xT m ≫ I.m1.φ) (by
    show (xL I xT m ≫ I.m1.φ) ≫ Xo.univ.t.G.hom = spMap _ ≫ y.1.x
    rw [Category.assoc, I.m1.cart.1.w, ← Category.assoc, xL_snd])

theorem ext2 {Z : Scheme.{0}} {a b : Z ⟶ I.t'.G.left} (h1 : a ≫ I.m2.φ = b ≫ I.m2.φ)
    (h2 : a ≫ I.t'.G.hom = b ≫ I.t'.G.hom) : a = b := I.m2.cart.1.hom_ext h1 h2

end Pt

end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.LBPull
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField

attribute [local instance] Over.cartesianMonoidalCategory

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {Y Z : Scheme.{0}} {K : Type} [Fintype K]

end Gen

section GenX

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {Y Z : Scheme.{0}} {K : Type} [Fintype K]

end GenX

section Sec

variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (a : ℤ)

theorem isPullSec_congr {T T' : Over S0} {h₁ h₂ : T' ⊗ A ⟶ T ⊗ A} (e : h₁ = h₂)
    (hh₁ : h₁ ≫ snd T A = snd T' A) (hh₂ : h₂ ≫ snd T A = snd T' A)
    (s : LB.Sec (LPow A L a T)) (s' : LB.Sec (LPow A L a T')) :
    IsPullSec A L a h₁ hh₁ s s' ↔ IsPullSec A L a h₂ hh₂ s s' := by
  subst e
  exact Iff.rfl

theorem isPullSec_unique {T T' : Over S0} {h : T' ⊗ A ⟶ T ⊗ A} {hh : h ≫ snd T A = snd T' A}
    {s : LB.Sec (LPow A L a T)} {s' s'' : LB.Sec (LPow A L a T')}
    (h' : IsPullSec A L a h hh s s') (h'' : IsPullSec A L a h hh s s'') : s' = s'' := by
  obtain ⟨f1, c1⟩ := s'
  obtain ⟨f2, c2⟩ := s''
  have hf : f1 = f2 := funext fun j => (h' j).trans (h'' j).symm
  subst hf
  rfl

end Sec

section Val

variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (a : ℤ)

theorem ptSecT_whisker {T T' : Over S0} (g : T' ⟶ T) (z : T ⟶ A) :
    (ptSecT A (g ≫ z)).left ≫ (g ▷ A).left = g.left ≫ (ptSecT A z).left := by
  have e : ptSecT A (g ≫ z) ≫ (g ▷ A) = g ≫ ptSecT A z := by
    unfold ptSecT
    ext <;> simp
  have e' := congrArg CommaMorphism.left e
  simpa using e'

theorem isValueAt_pull {T T' : Over S0} (g : T' ⟶ T) (z : T ⟶ A) {s : LB.Sec (LPow A L a T)}
    {s' : LB.Sec (LPow A L a T')} (hs : IsPullSec A L a (g ▷ A) (whiskerRight_snd g A) s s')
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (hv : IsValueAt A L a s z τ v) :
    IsValueAt A L a s' (g ≫ z) (LB.pullGen L (fun _ => z.left) (fun _ => a) τ g.left) (g.left.appTop.hom v) := by
  intro j
  have hW : ∀ x ∈ LB.wchart L (fun _ : Fin 1 => (g ≫ z).left) j,
      g.left x ∈ LB.wchart L (fun _ : Fin 1 => z.left) j := fun x hx =>
    Set.mem_iInter.2 fun k => by
      have h1 := Set.mem_iInter.1 hx k
      simpa [Over.comp_left, Scheme.Hom.comp_base] using h1
  apply fn_ext
  intro x hx
  have hx' := hW x hx
  have hPz := val_le A L z j hx'
  have hPgz := val_le A L (g ≫ z) j hx

  erw [gs_res _ x _ hx, gs_pull (𝟙 _) _ x _ hPgz, Category.id_comp, hs j,
    gs_res _ x _ hPgz, gs_pull (ptSecT A (g ≫ z)).left (g ▷ A).left x ((LPow A L a T).U j)
      (chart_le_res A L (g ▷ A) (whiskerRight_snd g A) a j
        (show (ptSecT A (g ≫ z)).left x ∈ (LPow A L a T').U j from hPgz)),
    ptSecT_whisker, ← gs_pull g.left (ptSecT A z).left x _ hPz, ← gs_res _ x (val_le A L z j) hx',
    hv j, gs_mul _ x _ hx', gs_res _ x le_top hx']

  erw [gs_mul _ x _ hx, gs_res _ x le_top hx, gs_pull (𝟙 T'.left) g.left x ⊤ (by simp), Category.id_comp]
  congr 1
  dsimp only
  show gs g.left x (LB.wchart L (fun _ : Fin 1 => z.left) j) (τ.s j).val =
    gs (𝟙 _) x _ (((T'.left.presheaf.map (homOfLE _).op).hom ((g.left.app _).hom (τ.s j).val)))
  erw [gs_res _ x _ hx, gs_pull (𝟙 _) g.left x _ hx', Category.id_comp]

end Val

section Rig

private theorem res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)ˣ) :
    res h2 (res h1 x) = res (h2.trans h1) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem shape_rig {X T T' : Scheme.{0}} (g : T' ⟶ T) (f : T ⟶ X) (f' : T' ⟶ X) (hf : g ≫ f = f')
    {U : X.Opens} {W : T.Opens} (hW : W ≤ f ⁻¹ᵁ U) {V : T'.Opens} (hV : V ≤ g ⁻¹ᵁ W) {V' : T'.Opens}
    (hV' : V' ≤ f' ⁻¹ᵁ U) {O : T'.Opens} (o1 : O ≤ V) (o2 : O ≤ V') (x : Γ(X, U)ˣ) (k : ℤ) :
    res o1 (res hV (pullU g W ((res hW (pullU f U x)) ^ k))) = res o2 ((res hV' (pullU f' U x)) ^ k) := by
  subst hf
  have hA : V ≤ (g ≫ f) ⁻¹ᵁ U := fun y hy => hW (hV hy)
  simp only [map_zpow]
  congr 1
  rw [← DVR.res_pullU_comp' g f hW hV hA x, res_res_lemma, res_res_lemma]

variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left)

theorem corr_rigT_pull (rig : LB.Gen (L.pull (eSec A))) {T T' : Over S0} (g : T' ⟶ T) (k : ℤ) :
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ (rigT A L rig T k) g.left) (rigT A L rig T' k) := by
  unfold LB.Gen.Corr
  intro j j' _ _ hjj
  have hj : j = j' := funext fun i => by
    fin_cases i
    exact hjj 0 0 (by rw [← Category.assoc, Over.w g])
  subst hj
  exact shape_rig g.left T.hom T'.hom (Over.w g) _ _ _ _ _ _ k

end Rig

section SecComp

variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (a : ℤ)

theorem isPullSec_comp {T T' T'' : Over S0} {h : T' ⊗ A ⟶ T ⊗ A} {hh : h ≫ snd T A = snd T' A}
    {h' : T'' ⊗ A ⟶ T' ⊗ A} {hh' : h' ≫ snd T' A = snd T'' A}
    {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')} {s'' : LB.Sec (LPow A L a T'')}
    (h1 : IsPullSec A L a h hh s s') (h2 : IsPullSec A L a h' hh' s' s'') :
    IsPullSec A L a (h' ≫ h) (by rw [Category.assoc, hh, hh']) s s'' := by
  intro j
  rw [h2 j, h1 j]
  simp only [Over.comp_left, Scheme.Hom.comp_app, Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply,
    Category.assoc, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE_map_assoc, Scheme.Hom.appLE_comp_appLE_assoc]

end SecComp

end Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.BidegreeTwoJet
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

namespace BidegreeTwoJet

section Jets

variable {V : Type} [CommRing V] {G' G : Over (Sp V)} [GrpObj G'] [GrpObj G] {n d : ℕ}

def zV (pG : IsPowGrp G' G n) (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (m : ℕ) : jOG (𝟙 (Sp V)) d m n ⟶ G' :=
  pG.lim.lift (Fan.mk _ fun i => homAt (𝟙 (Sp V)) (jetCopy (S := V) d m i) ≫ xT m)

end Jets

section Coord

variable {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {D' : DegData V I}
  {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G' G : Over (Sp V)} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
  {n d : ℕ}

end Coord


end BidegreeTwoJet
end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end
