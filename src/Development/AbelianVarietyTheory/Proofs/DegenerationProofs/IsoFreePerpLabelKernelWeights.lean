module

public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.TorusPerp

section Pairing
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.UT.TorusWeight GlobalTheory.TorusExt

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem weilQkIs_tor (hG : GlobalFnsSt) {k : ℕ} (p p' : QkPt D F k) {τ : Multiplicative D.X →* Fˣ} (hy : p.y = 0)
    (hτ : IsTor τ p.g) : WeilQkIs D F k p p' (τ (Multiplicative.ofAdd p'.y)).val := by
  intro w w' hw hw' s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄
  rw [phiRel_iff hG _ _ hw'] at h₁ h₄
  rw [phiRel_iff hG _ _ hw] at h₂ h₃
  have tr : DegPre.trPt D F p.g.b = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.id_comp]; exact tr_fst D F _
    · rw [Category.id_comp]
      refine (tr_pr D F _).trans ?_
      rw [hτ.1, MonObj.comp_one, _root_.mul_one]
  have v : ∀ (α : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J), Good D.P.L z J →
      (uVal D F k α p.g.b ρ z J * val (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) (ρ ≫ fst _ _).left z J).val =
        gs (ρ ≫ fst _ _).left z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (τ (Multiplicative.ofAdd α)).val) *
          (val w (ρ ≫ fst _ _).left z J).val := by
    intro α T ρ z J hJ
    have C : IsCub (th D z J) := isCub_cubV D.cub hJ
    have hu : uVal D F k α p.g.b ρ z J = 1 := by
      rw [uVal, hτ.1]
      simp only [MonObj.comp_one]
      unfold cubN
      simp only [C.face₃, C.face₂, Finset.prod_const_one, inv_one, _root_.mul_one]
    have e := val_const (p.g.s α) _ (hτ.2 α) (ρ ≫ fst _ _).left z hJ
    rw [hu, _root_.one_mul, val_mul hJ, Units.val_mul, e]
  intro β
  obtain ⟨α, rfl⟩ : ∃ α, α + p'.y = β := ⟨β - p'.y, sub_add_cancel _ _⟩
  refine (sval_const _ _ _ _).2 fun T ρ z J hJ => ?_
  have e₁ := h₁ α _ rfl T ρ z J hJ
  have e₂ := h₂ (α + p'.y) (α + p'.y) (by rw [hy, add_zero]) T ρ z J hJ
  have e₃ := h₃ α α (by rw [hy, add_zero]) T (ρ ≫ DegPre.trPt D F p'.g.b) z J hJ
  have e₄ := h₄ α _ rfl T ρ z J hJ
  rw [v _ T _ z J hJ, tr, Category.comp_id] at e₂ e₃
  rw [Category.assoc, tr_fst] at e₃
  rw [e₂, e₄, e₃, e₁, ofAdd_add, map_mul, Units.val_mul (τ _), map_mul, gs_mul _ _ ⊤ trivial]
  ring


attribute [local instance] gtGroup in
theorem exists_qkPt_tor (hB : D.TauBimult) {k : ℕ} (τ : Multiplicative D.X →* Fˣ) (h : τ ^ k = 1) :
    ∃ p : QkPt D F k, p.y = 0 ∧ IsTor τ p.g :=
  ⟨qkMk hB 0 (torusPt D F (Additive.ofMul τ)) (by rw [← map_nsmul, ← ofMul_pow, h, ofMul_one, map_zero, map_zero]),
    rfl, (isTor_iff _ _).2 (isTorusPtF_torusPt τ)⟩

end Pairing

section Algebra

theorem eStd_add_left (g n : ℕ) (a a' b : Fin g ⊕ Fin g → ZMod n) :
    eStd g n (a + a') b = eStd g n a b + eStd g n a' b := by
  simp only [eStd, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem eStd_add_right (g n : ℕ) (a b b' : Fin g ⊕ Fin g → ZMod n) :
    eStd g n a (b + b') = eStd g n a b + eStd g n a b' := by
  simp only [eStd, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem eq_zero_of_eStd (g n : ℕ) (a : Fin g ⊕ Fin g → ZMod n) (h : ∀ b, eStd g n a b = 0) : a = 0 := by
  funext j
  rcases j with i | i
  · simpa [eStd, Pi.single_apply] using h (Pi.single (.inr i) 1)
  · simpa [eStd, Pi.single_apply] using h (Pi.single (.inl i) 1)

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)

theorem isoFree_perp_ker {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (yy : S.Gam →+ X ⧸ (nsmulAddMonoidHom (S.r * S.N) : X →+ X).range) (hs : Function.Surjective yy)
    (H : ∀ l : X →+ ZMod (S.r * S.N), ∃ a ∈ yy.ker, ∀ b α, yy b = QuotientAddGroup.mk α → eStd S.g _ a b = l α) :
    S.IsoFree (S.perp yy.ker) ∧ ∃ wt : X →+ (S.perp yy.ker →+ ZMod S.N), ∀ (x : S.Gam) (α : X),
      yy x = QuotientAddGroup.mk α → ∀ t : S.perp yy.ker,
        wt α t = ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (eStd S.g _ t x) := by
  choose σ hσ using fun α : X => hs (QuotientAddGroup.mk α)
  have ind : ∀ (t : S.perp yy.ker) (b b' : S.Gam), yy b = yy b' → eStd S.g _ t b = eStd S.g _ t b' := by
    intro t b b' e
    have h0 : eStd S.g _ t (b - b') = 0 := t.2 _ (by rw [AddMonoidHom.mem_ker, map_sub, e, sub_self])
    rw [← sub_add_cancel b b', eStd_add_right, h0, zero_add]
  let Λ : S.perp yy.ker →+ X →+ ZMod (S.r * S.N) := AddMonoidHom.mk'
    (fun t => AddMonoidHom.mk' (fun α => eStd S.g _ t (σ α)) fun α β => by
      rw [← eStd_add_right]
      exact ind t _ _ (by rw [map_add (f := _), hσ, hσ, hσ, QuotientAddGroup.mk_add]))
    fun t t' => AddMonoidHom.ext fun α => eStd_add_left _ _ _ _ _
  have hΛ : ∀ (t : S.perp yy.ker) b α, yy b = QuotientAddGroup.mk α → Λ t α = eStd S.g _ t b :=
    fun t b α e => ind t _ _ ((hσ α).trans e.symm)
  have hbij : Function.Bijective Λ := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun t ht => Subtype.ext (eq_zero_of_eStd _ _ _ fun b => ?_), fun l => ?_⟩
    · obtain ⟨α, e⟩ := QuotientAddGroup.mk_surjective (yy b)
      rw [← hΛ t b α e.symm, ht, AddMonoidHom.zero_apply]
    · obtain ⟨a, -, ha⟩ := H l
      exact ⟨⟨a, fun h hh => (ha h 0 hh).trans (map_zero l)⟩, AddMonoidHom.ext fun α => ha _ _ (hσ α)⟩
  refine ⟨⟨fun s hs t ht => ?_, Module.finrank ℤ X, ⟨(AddEquiv.ofBijective Λ hbij).trans
    ((addMonoidHomLequivInt ℤ).toAddEquiv.trans ((Module.finBasis ℤ X).constr ℤ).symm.toAddEquiv)⟩⟩,
    Λ.flip.compr₂ (ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N)).toAddMonoidHom, fun x α e t => ?_⟩
  · obtain ⟨a, ha, hl⟩ := H (Λ ⟨s, hs⟩)
    obtain ⟨α, e⟩ := QuotientAddGroup.mk_surjective (yy t)
    rw [← hΛ ⟨s, hs⟩ t α e.symm, ← hl t α e.symm, GlobalTheory.ThetaProj.eStd_swap, ht a ha, neg_zero]
  · rw [← hΛ t x α e]; rfl

end Algebra

section Points

def ptHom {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (T : Over S') : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G) :=
  MonoidHom.mk' (fun x => toBase h.1.w x) fun x y => Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm

theorem ptHom_bijective {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') : Function.Bijective (ptHom h T) :=
  ⟨fun x y e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) ((Over.w x).trans (Over.w y).symm)),
    fun z => ⟨Over.homMk (h.1.lift z.left T.hom (Over.w z)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩⟩

theorem map_unitOn {A B : Type} [CommRing A] [CommRing B] (β : A →+* B) (c : Aˣ) :
    Units.map (spMap β).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map β.toMonoidHom c) :=
  Units.ext (congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm

theorem unitOn_injective {K : Type} [CommRing K] : Function.Injective (unitOn (R := K)) := fun _ _ h =>
  Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1 (congrArg Units.val h))

end Points

theorem isoFree_perp_and_weights : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (yy : S.Gam →+ u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range), Function.Surjective yy → (∀ (a : S.Gam) (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk x → x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left → yy a = QuotientAddGroup.mk pk.y) → S.IsoFree (S.perp yy.ker) ∧ ∃ wt : u.D.toPre.X →+ (S.perp yy.ker →+ ZMod S.N), ∀ (x : S.Gam) (α : u.D.toPre.X), yy x = QuotientAddGroup.mk α → ∀ t : S.perp yy.ker, wt α t = ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (eStd S.g _ t x) := by
  intro hL _ hT o Ω _ _ _ hA S ρ p _ y₀ u yy hs hyy
  have hG := hL.globalFns
  have hN := S.N_ge
  have hr := S.r_pos
  have hn : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : IsDomain o := hA.inj.isDomain _
  have : CharZero u.V := RingHom.charZero
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  have := ρ.P.isAb.comm
  obtain ⟨f, f₁, f₂, -, -, f₅⟩ := hT u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) hn.pos

  have hζ : IsPrimitiveRoot (S.ζ ^ (S.r * S.N)) (S.r * S.N) := S.prim.pow (pow_pos hn.pos 2) (pow_two _)
  let c₀ : (S.R)ˣ := Units.map (algebraMap o S.R).toMonoidHom (hζ.isUnit hn.ne).unit
  let ω : (PadicAlgCl p)ˣ := Units.map y₀.toMonoidHom c₀
  have hω : IsPrimitiveRoot ω (S.r * S.N) := by
    have : NeZero ((S.r * S.N : ℕ) : PadicAlgCl p) := ⟨Nat.cast_ne_zero.2 hn.ne⟩
    rw [← IsPrimitiveRoot.coe_units_iff, ← Polynomial.isRoot_cyclotomic_iff,
      ← Polynomial.map_cyclotomic _ (y₀.comp (algebraMap o S.R))]
    exact (hζ.isRoot_cyclotomic hn.pos).map (y₀.comp (algebraMap o S.R))

  have hy : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK = spMap y₀ :=
    (Spec.map_comp _ _).symm.trans (congrArg spMap u.fac)
  let h : Over.mk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK) ⟶ baseOver (Sp S.R) :=
    Over.homMk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK) (by simp)
  have hh : h.left = spMap y₀ := hy
  let Φ := ptHom u.cart (TFK (R := u.V) (PadicAlgCl p))
  have hΦ : Function.Bijective Φ := ptHom_bijective _ _
  have lab : ∀ a q, Φ (f q) = h ≫ ρ.pt a → yy a = QuotientAddGroup.mk q.y := fun a q e =>
    hyy a q _ ((f₁ _ _).2 rfl) ((congrArg (fun z => z.left) e).trans (by rw [← hh]; rfl))
  let pt : Multiplicative S.Gam →* (baseOver (Sp S.R) ⟶ ρ.P.A) := MonoidHom.mk' (fun a => ρ.pt a.toAdd) fun _ _ => ρ.pt_add _ _
  have onto : ∀ b, ∃ q, Φ (f q) = h ≫ ρ.pt b := fun b => by
    obtain ⟨x, hx⟩ := hΦ.2 (h ≫ ρ.pt b)
    obtain ⟨q, rfl⟩ := f₂ x (hΦ.1 (by
      have e : ρ.pt b ^ (S.r * S.N) = 1 := by
        refine (map_pow pt (Multiplicative.ofAdd b) _).symm.trans ?_
        rw [← ofAdd_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (S.r * S.N)), ZMod.natCast_self, zero_smul, ofAdd_zero, map_one]
      rw [map_pow, hx, map_one, ← MonObj.comp_pow, e, MonObj.comp_one]))
    exact ⟨q, hx⟩
  have weil : ∀ a b q q', Φ (f q) = h ≫ ρ.pt a → Φ (f q') = h ≫ ρ.pt b →
      WeilIs u.A.A u.A.L (S.r * S.N : ℕ) (f q) (f q') (unitOn (ω ^ (eStd S.g _ a b).val)) := fun a b q q' e e' => by
    have w := GlobalTheory.CommPairing.weilIs_pull hG ρ.P.isAb ρ.P.isLB h (ρ.weil a b (c₀ ^ (eStd S.g _ a b).val) (by
      rw [pow_mul, map_pow]; rfl))
    rw [← e, ← e'] at w
    refine (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ _ _ _ _ ρ.P.isLB u.A.isLB u.cart u.lb _ _ _ _
      (Φ (f q)) (Φ (f q')) _ rfl rfl).2 ?_
    convert w using 1
    rw [← map_pow, ← map_unitOn, ← hh]
  refine isoFree_perp_ker S yy hs fun l => ?_
  let χ := AddChar.zmodChar (S.r * S.N) hω.pow_eq_one
  let τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ := χ.toMonoidHom.comp l.toMultiplicative
  have hτ : ∀ α, τ (Multiplicative.ofAdd α) = ω ^ (l α).val := fun _ => rfl
  obtain ⟨q, hq, hqτ⟩ := exists_qkPt_tor (F := PadicAlgCl p) (k := S.r * S.N) u.D.tau_bimult τ (MonoidHom.ext fun α => by
    show (ω ^ (l α.toAdd).val) ^ (S.r * S.N) = 1
    rw [pow_right_comm, hω.pow_eq_one, one_pow])
  have hq1 : f q ^ (S.r * S.N) = 1 := by
    obtain ⟨w, hw⟩ := u.U.ext
    exact ((f₁ _ _).2 rfl w hw).1
  obtain ⟨a, ha, -⟩ := ρ.pt_bij (PadicAlgCl p) _ (Φ (f q)) (by rw [← map_pow, hq1, map_one])
  refine ⟨a, (lab a q ha.symm).trans (by rw [hq]; rfl), fun b α e => ?_⟩
  obtain ⟨q', hq'⟩ := onto b
  have e₁ := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG u.A.isAb u.A.isLB (weil a b q q' ha.symm hq')
    ((f₅ q q' _).1 (weilQkIs_tor hG q q' hq hqτ)))
  rw [hτ] at e₁
  rw [ZMod.val_injective _ (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e₁)]
  obtain ⟨z, hz⟩ := QuotientAddGroup.eq.1 ((lab b q' hq').symm.trans e)
  have hz' : (S.r * S.N) • z = -q'.y + α := hz
  have := congrArg l hz'
  rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_add (f := _), map_neg] at this
  exact neg_add_eq_zero.1 this.symm

end GlobalTheory.ZH.TorusPerp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeightsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isoFree_perp_labelKernel_weights : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (yy : S.Gam →+ u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range), Function.Surjective yy → (∀ (a : S.Gam) (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk x → x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left → yy a = QuotientAddGroup.mk pk.y) → S.IsoFree (S.perp yy.ker) ∧ ∃ wt : u.D.toPre.X →+ (S.perp yy.ker →+ ZMod S.N), ∀ (x : S.Gam) (α : u.D.toPre.X), yy x = QuotientAddGroup.mk α → ∀ t : S.perp yy.ker, wt α t = ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (eStd S.g _ t x) := by
  first | exact @GlobalTheory.ZH.TorusPerp.isoFree_perp_and_weights | exact GlobalTheory.ZH.TorusPerp.isoFree_perp_and_weights | (intros; apply GlobalTheory.ZH.TorusPerp.isoFree_perp_and_weights <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrameUnit
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.ZHPre
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
variable {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

abbrev LOne : LB Q.G.left := LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => 1)

abbrev SecFam (N : M.Z.Opens) : Type := ∀ j, Γ(Q.G.left, Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j)

abbrev ThMul (c : Ω) (N : M.Z.Opens) (σ : Q.SecFam N) : Prop :=
  GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w 1 (fun _ : Unit => ρ.th₁) (fun _ => c) _ σ

abbrev FibNe (N : M.Z.Opens) (σ : Q.SecFam N) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M.Z), Set.range x ⊆ N →
    ∃ (g : Sp K ⟶ Q.G.left) (j : _), g ≫ Q.G.hom = x ∧ valF g _ (σ j) ≠ 0

abbrev ExtPt (a : S.Gam) (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left) : Prop :=
  h ≫ Q.G.hom = W.ι ∧
  ∀ (x : Sp Ω ⟶ W.toScheme) (x' : Sp Ω ⟶ pullback ρ.P.A.hom Q.u₀), x ≫ W.ι = M.pt → x' ≫ Q.φ ≫ Q.G.hom = M.pt →
    x' ≫ pullback.fst _ _ = spMap S.R.val.toRingHom ≫ (ρ.pt a).left → x ≫ h = x' ≫ Q.φ

def MulRel (n : ℕ)
    (α : LB.Gen (LB.LinComb ρ.P.L (K := Fin 2) ![𝟙 ρ.P.A.left, (mulA ρ.P.A n).left] ![(n : ℤ) ^ 2, -1]))
    (κ : LB.Gen (LB.LinComb Q.L.L (K := Fin 2) ![𝟙 Q.G.left, (mulA Q.G n).left] ![(n : ℤ) ^ 2, -1])) : Prop :=
  ∀ (K : Type) [Field K] (g g' : Sp K ⟶ pullback ρ.P.A.hom Q.u₀) (jP jP' : ρ.P.L.ι) (jL jL' : Q.L.L.ι),
    g' ≫ pullback.fst _ _ = g ≫ pullback.fst _ _ ≫ (mulA ρ.P.A n).left →
    g' ≫ pullback.snd _ _ = g ≫ pullback.snd _ _ →
    Set.range (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⊆ ρ.P.L.U jP → Set.range (g ≫ Q.φ) ⊆ Q.L.L.U jL →
    Set.range (g' ≫ pullback.fst ρ.P.A.hom Q.u₀) ⊆ ρ.P.L.U jP' → Set.range (g' ≫ Q.φ) ⊆ Q.L.L.U jL' →
    valF (g ≫ pullback.fst ρ.P.A.hom Q.u₀) _ (α.s ![jP, jP']).val *
        valF g' _ (Q.w.s (fun _ => jP', fun _ => jL')).val =
      valF g _ (Q.w.s (fun _ => jP, fun _ => jL)).val ^ (n ^ 2) * valF (g ≫ Q.φ) _ (κ.s ![jL, jL']).val

def FrameUnit (a : S.Gam) (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left) (w : W.toScheme) : Prop :=
  ∀ (jP : ρ.P.L.ι) (jL : Q.L.L.ι) (x' : Sp Ω ⟶ pullback ρ.P.A.hom Q.u₀) (e : Ω), h w ∈ Q.L.L.U jL →
    x' ≫ Q.φ ≫ Q.G.hom = M.pt → x' ≫ pullback.fst _ _ = spMap S.R.val.toRingHom ≫ (ρ.pt a).left →
    Set.range (x' ≫ pullback.fst ρ.P.A.hom Q.u₀) ⊆ ρ.P.L.U jP →
    e = valF (X := (baseOver (Sp S.R)).left) (spMap S.R.val.toRingHom) _ ((ρ.fr a).s fun _ => jP).val /
      valF x' _ (Q.w.s (fun _ => jP, fun _ => jL)).val →
    e ≠ 0 ∧ e ∈ M.O (W.ι w) ∧ e⁻¹ ∈ M.O (W.ι w)

def TestFac {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)
    (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme) : Prop :=
  (∀ x, (jV x : PadicAlgCl p) = algebraMap (FractionRing u.V) _ (algebraMap u.V (FractionRing u.V) x)) ∧
    spMap jV ≫ yV = y ∧ yK ≫ U₀.ι = jK u.V ≫ yV ∧ yK ≫ Q.u₀ = spMap u.yK

def TestMap {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)
    (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme) (F : u.G.left ⟶ Q.G.left)
    (ψ : pullback u.G.hom (jK u.V) ⟶ pullback ρ.P.A.hom Q.u₀) : Prop :=
  IsGrpPullback u.G Q.G yV F ∧ ψ ≫ pullback.fst _ _ = u.U.gen.hom.left ≫ u.φ ∧
    ψ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ yK ∧ ψ ≫ Q.φ = pullback.fst _ _ ≫ F

end GlobalTheory.ZH.ZHPre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsHomOpenPart
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem isLocallyNoetherian [IsNoetherianRing o] : IsLocallyNoetherian M.Z :=
  have := M.lft
  LocallyOfFiniteType.isLocallyNoetherian M.s

def ptOpen (V : M.Z.Opens) (hV : (V : Set M.Z).Nonempty) : Sp Ω ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι M.pt (by
    rw [Scheme.Opens.range_ι]
    exact (top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hV))

theorem ptOpen_ι (V : M.Z.Opens) (hV : (V : Set M.Z).Nonempty) : M.ptOpen V hV ≫ V.ι = M.pt :=
  IsOpenImmersion.lift_fac _ _ _

def openPart [IsNoetherianRing o] (V : M.Z.Opens) (hV : (V : Set M.Z).Nonempty) : RatModel o Ω :=
  haveI : Nonempty V.toScheme := ⟨⟨hV.some, hV.some_mem⟩⟩
  haveI : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  { Z := V.toScheme
    s := V.ι ≫ M.s
    sep := have := M.sep; inferInstance
    lft := have := M.lft; inferInstance
    qc := have := M.qc; have := M.isLocallyNoetherian; inferInstance
    pt := M.ptOpen V hV
    pt_s := by rw [← Category.assoc, ptOpen_ι, M.pt_s]
    gen := by
      have h : ∀ w : Sp Ω, M.ptOpen V hV w = genericPoint V.toScheme := fun w => by
        apply V.ι.isOpenEmbedding.injective
        rw [genericPoint_eq_of_isOpenImmersion, ← M.pt_apply w, ← M.ptOpen_ι V hV]
        rfl
      exact Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, h (IsLocalRing.closedPoint Ω)⟩, by
        rintro _ ⟨w, rfl⟩
        exact h w⟩
    onto := fun x => by
      obtain ⟨U, f, hU, rfl⟩ := M.onto x
      obtain ⟨z, hz, hz'⟩ := M.nonempty_inf hU hV
      refine ⟨V.ι ⁻¹ᵁ U, V.ι.app U f, ⟨⟨z, hz'⟩, hz⟩, ?_⟩
      refine (valR_comp _ _ U f).symm.trans ?_
      rw [ptOpen_ι]
      rfl }

theorem isHom_openPart [IsNoetherianRing o] (V : M.Z.Opens) (hV : (V : Set M.Z).Nonempty) :
    M.IsHom (M.openPart V hV) (AlgHom.id o Ω) V.ι :=
  (M.ptOpen_ι V hV).trans ((Category.id_comp _).symm.trans (congrArg (· ≫ M.pt) (Spec.map_id _).symm))

variable {M}

theorem IsHom.O_eq {N : RatModel o Ω} {j : N.Z ⟶ M.Z} (h : M.IsHom N (AlgHom.id o Ω) j) [IsOpenImmersion j]
    (z : N.Z) : N.O z = M.O (j z) := by
  refine le_antisymm ?_ fun x hx => h.map_mem_O hx
  rintro _ ⟨U, g, hz, rfl⟩
  have hz' : j z ∈ j ''ᵁ U := ⟨z, hz, rfl⟩
  refine ⟨j ''ᵁ U, (j.appIso U).inv g, hz', ?_⟩
  refine (h.valF_app ⟨_, hz'⟩ _).symm.trans ?_
  have e := congrArg (fun φ => φ.hom g) (j.appIso_inv_app U)
  refine (congrArg _ e).trans ?_
  exact N.valF_resG (j.preimage_image_eq U).le ⟨z, hz'⟩ g

variable (M)

structure GenTriv (H : LB M.Z) (d : H.ι → Ω) : Prop where
  ne : ∀ k, d k ≠ 0
  g_eq : ∀ k k', ((H.U k ⊓ H.U k' : M.Z.Opens) : Set M.Z).Nonempty →
    valF M.pt (H.U k ⊓ H.U k') (H.g k k' : Γ(M.Z, H.U k ⊓ H.U k')) = d k' / d k

def HasVal {H : LB M.Z} (d : H.ι → Ω) (σ : H.Sec) (x : Ω) : Prop :=
  ∀ k, (H.U k : Set M.Z).Nonempty → valF M.pt (H.U k) (σ.f k) = x / d k

def ProjChart {Ω' : Type} [Field Ω'] [Algebra o Ω'] (N : RatModel o Ω') (φ : Ω →ₐ[o] Ω') (q : N.Z ⟶ M.Z)
    (W : M.Z.Opens) {J : Type} (t : J → Ω') : Prop :=
  (∀ z', q z' ∈ W → ∃ i, N.Div t i z') ∧ ∀ i, t i ≠ 0 → ∃ U : N.Z.Opens, IsAffineOpen U ∧
    (U : Set N.Z) = {z' | q z' ∈ W ∧ N.Div t i z'} ∧
    N.ringOn U = Algebra.adjoin o (φ '' (M.ringOn W : Set Ω) ∪ Set.range fun j => t j / t i)

end GlobalTheory.ZH.RatModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionValuesCoordsOperatorPermute
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionValuesCoordsOperatorPermute
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.EvCrd
open GlobalTheory.ThetaCompare

theorem defect_eq_one {G U : Type} [CommGroup G] [CommGroup U] (f b n : G → U) (X : G) (N M Q : ℕ) (hN : Odd N)
    (hX : X ^ N = 1) (hM : X ^ M = 1)
    (h₁ : ∀ z, f z ^ Q * (b (X * z) * (b z)⁻¹) = f 1 ^ Q * (b (X * 1) * (b 1)⁻¹))
    (h₂ : ∀ z, b z * (b z⁻¹)⁻¹ * (n z ^ Q)⁻¹ * n (z ^ M) = b 1 * (b 1⁻¹)⁻¹ * (n 1 ^ Q)⁻¹ * n (1 ^ M))
    (hp : ∏ j ∈ Finset.range N, f (X ^ j) = 1) (hs : f X⁻¹ * n 1 * (f 1 * (n X⁻¹)⁻¹) = 1) (z : G) :
    f z ^ Q * (b (X * z) * (b z)⁻¹) = 1 := by
  set κ := f 1 ^ Q * (b (X * 1) * (b 1)⁻¹) with hκ
  have e₁ : κ ^ N = 1 := by
    have : ∀ j ∈ Finset.range N, κ = f (X ^ j) ^ Q * (b (X ^ (j + 1)) / b (X ^ j)) := fun j _ => by
      rw [← h₁ (X ^ j), pow_succ' X j, div_eq_mul_inv]
    rw [show κ ^ N = ∏ _j ∈ Finset.range N, κ by rw [Finset.prod_const, Finset.card_range],
      Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_pow, hp,
      Finset.prod_range_div (fun j => b (X ^ j)) N, hX, pow_zero, div_self', one_pow, _root_.one_mul]
  have e₂ : κ ^ 2 = 1 := by
    have a₁ := h₁ X⁻¹
    have a₂ := h₂ X⁻¹
    have a₃ := congrArg (· ^ Q) hs
    rw [inv_pow, hM, inv_inv, inv_one, one_pow] at a₂
    rw [mul_inv_cancel] at a₁
    rw [_root_.mul_one] at hκ
    simp only [one_pow, mul_pow, inv_pow] at a₃
    rw [sq]
    nth_rewrite 1 [← a₁]
    rw [hκ]
    apply Additive.ofMul.injective
    replace a₂ := congrArg Additive.ofMul a₂
    replace a₃ := congrArg Additive.ofMul a₃
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one] at a₂ a₃ ⊢
    linear_combination (norm := module) a₃ - a₂
  obtain ⟨l, rfl⟩ := hN
  rw [pow_succ, pow_mul, e₂, one_pow, _root_.one_mul] at e₁
  exact (h₁ z).trans e₁

variable {S : Scheme.{0}}


open CommPairing GlobalLift in
theorem lift_pow (hG : GlobalFnsSt) (P : PolAV S) {T : Over S} {N M : ℕ} (hN : Odd N)
    {α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ M).left] ![(M : ℤ) ^ 2, -1])}
    (hα : α.IsGen) {x : T ⟶ P.A} (hx : x ^ N = 1) (hM : x ^ M = 1) {θ : ThetaGrp P.A P.L N T}
    (H : SymLift P.A P.L N N x θ) {y : T.left} {J} (hJ : Good P.L y J) (z : T ⟶ P.A) :
    tval θ (ptSecT P.A z).left y J ^ (M ^ 2) *
        (val α (ptSecT P.A (x * z)).left y J ^ N * (val α (ptSecT P.A z).left y J ^ N)⁻¹) = 1 := by
  have := P.isAb.comm
  obtain ⟨rfl, hp, ν, hν, hs⟩ := H
  have rα := Reg.two (y := y) (J := J) α hα (snd T P.A) (snd T P.A ^ M) rfl rfl
  have rb := rα.pow hJ N
  have rf := Reg.two (y := y) (J := J) (φ := ![(snd T P.A).left, (translPt P.A θ.pt).left]) θ.φ θ.isGen
    (snd T P.A) (translPt P.A θ.pt) rfl rfl
  have rn := Reg.two (y := y) (J := J) (φ := ![(snd T P.A).left, (snd T P.A ≫ (GrpObj.inv : P.A ⟶ P.A)).left]) ν hν
    (snd T P.A) (snd T P.A)⁻¹ rfl rfl
  have c₁ := ((rf.pow hJ (M ^ 2)).mul hJ ((rb.pull hJ (translPt P.A θ.pt)).mul hJ rb.inv)).const hG P.isAb P.isLB hJ
    (fun U _ h => by
      have q : translPt P.A θ.pt ^ M = snd T P.A ^ M := by
        rw [show translPt P.A θ.pt = (fst T P.A ≫ θ.pt) * snd T P.A from rfl, mul_pow, ← SymLiftOdd.comp_pow', hM,
          MonObj.comp_one, _root_.one_mul]
      simp only [SymLiftOdd.comp_pow', lift_snd, q]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one]
      module)
  have c₂ := (((rb.mul hJ (rb.pull hJ (snd T P.A)⁻¹).inv).mul hJ (rn.pow hJ (M ^ 2)).inv).mul hJ
    (rn.pull hJ (snd T P.A ^ M))).const hG P.isAb P.isLB hJ (fun U _ h => by
      simp only [SymLiftOdd.comp_pow', SymLiftOdd.comp_inv', lift_snd, inv_pow]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one]
      module)
  simp only [pt_translPt, SymLiftOdd.comp_pow', SymLiftOdd.comp_inv', pt_snd] at c₁ c₂
  have q₁ := val_corr hJ hp (ptSecT P.A 1).left
  have q₂ := val_corr hJ hs (ptSecT P.A 1).left
  rw [GlobalLift.val_powGen _ _ _ hJ, val_one] at q₁
  rw [GlobalLift.val_symGen _ _ _ hJ, val_one, pt_translT, pt_negT, _root_.mul_one, inv_one] at q₂
  simp only [pt_translT, _root_.mul_one] at q₁
  exact defect_eq_one (fun z => tval θ (ptSecT P.A z).left y J)
    (fun z => val α (ptSecT P.A z).left y J ^ N)
    (fun z => nval ν (ptSecT P.A z).left y J) θ.pt N M (M ^ 2) hN hx hM
    (fun z => c₁ z 1) (fun z => c₂ z 1) ((Finset.prod_range _).trans q₁) q₂ z

theorem sval_sum {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {a : ℤ} {I : Type} [Fintype I]
    {s : I → LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T)} {c : I → Γ(T.left, ⊤)}
    (H : ∀ j, s'.f j = ∑ l, liftFun A _ (c l) * (s l).f j) (x : T ⟶ A) {z : T.left} {J} (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (ptSecT A x).left z J =
      ∑ l, gs (𝟙 _) z ⊤ (c l) *
        sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) (s l) (ptSecT A x).left z J := by
  have hy := hJ.mem (fun _ : Fin 1 => (snd T A).left) (ptSecT A x).left
  refine (congrArg (gs _ z _) (H _)).trans ?_
  have hs : ∀ (W : (T ⊗ A).left.Opens) (_ : (ptSecT A x).left z ∈ W) (u : I → Γ((T ⊗ A).left, W)),
      gs (ptSecT A x).left z W (∑ l, u l) = ∑ l, gs (ptSecT A x).left z W (u l) := fun W hW u => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [gs_eq _ z W hW, map_sum]
  refine (hs _ hy _).trans (Finset.sum_congr rfl fun l _ => (gs_mul _ z _ hy _ _).trans (congrArg (· * _) ?_))
  refine (gs_res _ z _ hy _).trans ((gs_pull _ (fst T A).left z ⊤ trivial _).trans ?_)
  rw [← Over.comp_left, ptSecT, lift_fst]; rfl


open CommPairing in
theorem exists_root_stalk (hG : GlobalFnsSt) (P : PolAV S) {T : Over S} {N M : ℕ} (hN : Odd N)
    {rig : LB.Gen (P.L.pull (eSec P.A))} {x h w : T ⟶ P.A} (hx : x ^ N = 1) (hM : x ^ M = 1) (hw : w = x * h)
    {θ : ThetaGrp P.A P.L N T} (H : SymLift P.A P.L N N x θ) {τ τ'} (hτ : IsTorsFrame P rig M h τ)
    (hτ' : IsTorsFrame P rig M w τ') (y : T.left) :
    ∃ ξ : (T.left.presheaf.stalk y)ˣ, ξ ^ (M ^ 2) = 1 ∧
      ∀ (I : Type) [Fintype I] (s : I → LB.Sec (LPow P.A P.L N T)) (t : LB.Sec (LPow P.A P.L N T))
        (c v : I → Γ(T.left, ⊤)) (v' : Γ(T.left, ⊤)),
        (∀ σ, IsActOf P.A P.L N θ t σ → ∀ j, σ.f j = ∑ l, liftFun P.A _ (c l) * (s l).f j) →
        (∀ l, IsValueAt P.A P.L N (s l) h (powFrame P.A P.L h τ N) (v l)) →
        IsValueAt P.A P.L N t w (powFrame P.A P.L w τ' N) v' →
        ∑ l, gs (𝟙 _) y ⊤ (c l) * gs (𝟙 _) y ⊤ (v l) = ξ.val * gs (𝟙 _) y ⊤ v' := by
  subst hw
  choose J hJ using fun χ : T.left ⟶ P.A.left => exists_chart P.isLB (χ y)
  replace hJ : Good P.L y J := hJ
  obtain ⟨β, hβ, -⟩ := hτ.2.2
  obtain ⟨α, hα, -⟩ := VVRank.exists_gen_pullTo (φ' := ![(snd T P.A).left, (snd T P.A ^ M).left]) β hβ
    (snd T P.A).left (fun k => by
      fin_cases k
      · exact Category.comp_id _
      · change (snd T P.A).left ≫ (mulA P.A M).left = (snd T P.A ^ M).left
        rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id])
  have a₁ := lift_pow hG P hN hα hx hM H hJ h
  have a₂ := torsFrame_pow hG P hα hτ hJ
  have a₃ := torsFrame_pow hG P hα hτ' hJ
  refine ⟨tval θ (ptSecT P.A h).left y J * val τ' (𝟙 _) y J ^ N * (val τ (𝟙 _) y J ^ N)⁻¹, ?_,
    fun I _ s t c v v' hc hv hv' => ?_⟩
  · apply Additive.ofMul.injective
    replace a₁ := congrArg Additive.ofMul a₁
    replace a₂ := congrArg Additive.ofMul a₂
    replace a₃ := congrArg Additive.ofMul a₃
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one] at a₁ a₂ a₃ ⊢
    linear_combination (norm := module) a₁ + N • a₃ - N • a₂
  · obtain ⟨σ, hσ⟩ : ∃ σ, IsActOf P.A P.L (N : ℤ) θ t σ := VVRank.exists_isTwistPull P.A P.isLB θ.isGen t
    have p : ∀ (z : T ⟶ P.A) (e), val (powFrame P.A P.L z e N) (𝟙 _) y J = val e (𝟙 _) y J ^ N := fun z e =>
      (map_zpow _ _ _).trans (zpow_natCast _ _)
    have b₁ := sval_twist hσ (ptSecT P.A h).left hJ
    have b₂ := sval_sum (hc σ hσ) h hJ
    have b₃ := sval_valueAt hv' hJ
    rw [pt_translT, congrArg (fun q => ptSecT P.A (q * h)) H.pt_eq, b₃, b₂, p] at b₁
    simp only [fun l => sval_valueAt (hv l) hJ, p, ← _root_.mul_assoc, ← Finset.sum_mul] at b₁
    rw [(Units.eq_mul_inv_iff_mul_eq _).2 b₁, Units.val_mul, Units.val_mul]
    change (tval θ (ptSecT P.A h).left y J).val * _ * _ * _ = _
    ring

theorem valR_comp {R : Type} [CommRing R] {X Y : Scheme.{0}} (x : Sp R ⟶ Y) (g : Y ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ g ⁻¹ᵁ U) (f : Γ(X, U)) : valR x (g ⁻¹ᵁ U) ((g.app U).hom f) = valR (x ≫ g) U f := by
  rw [CrdCalc.valR_eq x _ h, CrdCalc.valR_eq (x ≫ g) U h]
  rfl

theorem valR_fn {R K : Type} [CommRing R] [CommRing K] (y : R →+* K) (b : R) : valR (spMap y) ⊤ (fn b) = y b := by
  rw [CrdCalc.valR_eq _ _ le_rfl]
  have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y)
  have e := congrArg (fun q => q.hom b) n
  change (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (y b) = (spMap y).appTop.hom (fn b) at e
  have e' : ((spMap y).appLE ⊤ ⊤ le_rfl) = (spMap y).appTop := (Scheme.Hom.app_eq_appLE _).symm
  change (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (((spMap y).appLE ⊤ ⊤ le_rfl).hom (fn b)) = _
  rw [e', ← e]
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).inv_hom_id_apply _

theorem crd_of_isValueAt {R K : Type} [CommRing R] [Field K] (y : R →+* K) (P : PolAV (Sp R)) {k : ℤ} {I : Type}
    {s : I → LB.Sec (LPow P.A P.L k (baseOver (Sp R)))} {z : baseOver (Sp R) ⟶ P.A} {τ} {v : I → R}
    (H : ∀ i, IsValueAt P.A P.L k (s i) z τ (fn (v i))) :
    Crd (LPow P.A P.L k (baseOver (Sp R))) s (spMap y ≫ (ptSecT P.A z).left) (fun i => y (v i)) := by
  let x : Sp K ⟶ (baseOver (Sp R)).left := spMap y
  obtain ⟨j₀, hj⟩ := exists_chart P.isLB (z.left (x (IsLocalRing.closedPoint K)))
  let W := LB.wchart P.L (fun _ : Fin 1 => z.left) (fun _ => j₀)
  have hW : ⊤ ≤ x ⁻¹ᵁ W := (CrdCalc.top_le_iff x W).2 (Set.mem_iInter.2 fun _ => hj)
  have hU := hW.trans (x.preimage_mono (val_le P.A P.L z (fun _ => j₀)))
  refine ⟨fun _ => j₀, (Units.map (CrdCalc.valHom x W hW).toMonoidHom (τ.s fun _ => j₀))⁻¹, hU, fun i => ?_⟩
  have e := congrArg (valR x W) (H i fun _ => j₀)
  have e₁ := ((CrdCalc.valR_res x (val_le P.A P.L z (fun _ => j₀)) hW _).trans
    (valR_comp x (ptSecT P.A z).left _ hU ((s i).f fun _ => j₀))).symm.trans e
  have e₂ := e₁.trans ((CrdCalc.valR_mul x W hW _ _).trans (congrArg₂ (· * ·)
    ((CrdCalc.valR_res x le_top hW _).trans (valR_fn y (v i))) (CrdCalc.valR_eq x W hW _)))
  refine (Units.eq_inv_mul_iff_mul_eq _).2 ?_
  exact (mul_comm _ _).trans e₂.symm

theorem ev_crd_act : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), (∀ (K : Type) [Field K] (y : S.R →+* K) (a : S.Gam), ρ.Crd (spMap y ≫ (ρ.pt a).left) (fun i => y ⟨S.ev a i, S.ev_mem a i⟩)) ∧ ∀ a h : S.Gam, ∃ e : ℕ, ∀ i, ∑ n, algebraMap o Ω (S.ρ a n i) * S.ev h n = algebraMap o Ω (S.ζ ^ e) * S.ev (h + S.r • a) i := by
  intro hL o Ω _ _ _ hb S ρ
  refine ⟨fun K _ y a => ⟨_, ?_, crd_of_isValueAt y ρ.P (fun i => ρ.ev_val i a)⟩, fun a h => ?_⟩
  · rw [Category.assoc, ← Over.comp_left, pt_snd]
  have := ρ.P.isAb.comm
  have hN : Odd S.N := by rw [ρ.N_eq]; exact ρ.n_odd.pow.pow
  have h₀ : ρ.pt 0 = 1 := by
    have := ρ.pt_add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hp : ∀ (n : ℕ) b, ρ.pt (n • b) = ρ.pt b ^ n := fun n b => by
    induction n with
    | zero => rw [zero_smul, h₀, pow_zero]
    | succ n ih => rw [succ_nsmul, ρ.pt_add, ih, pow_succ]
  have hx : ρ.pt (S.r • a) ^ S.N = 1 := by rw [hp, ← pow_mul, (ρ.fr_tors a).1]
  let iso := Scheme.ΓSpecIso (CommRingCat.of S.R)
  let y : Sp S.R := (⊥ : PrimeSpectrum S.R)
  obtain ⟨ξ, hξ, e⟩ := exists_root_stalk hL.1.globalFns ρ.P hN hx (ρ.fr_tors _).1
    (by rw [ρ.pt_add, mul_comm]) (ρ.U_sym a) (ρ.fr_tors h) (ρ.fr_tors (h + S.r • a)) y
  let g : S.R →+* (Sp S.R).presheaf.stalk y := ((Sp S.R).presheaf.germ ⊤ y trivial).hom.comp iso.inv.hom
  have hg : Function.Injective g :=
    (germ_injective_of_isIntegral (Sp S.R) (U := ⊤) y trivial).comp (ConcreteCategory.bijective_of_isIso iso.inv).1
  have hgs : ∀ b : S.R, gs (𝟙 (baseOver (Sp S.R)).left) y ⊤ (fn b) = g b := fun b => gs_eq _ y ⊤ trivial _
  have hi : Function.Injective (algebraMap o S.R) := fun b b' h => hb.inj (congrArg Subtype.val h)
  have hζ : IsPrimitiveRoot (g (algebraMap o S.R S.ζ)) ((S.r * S.N) ^ 2) :=
    (S.prim.map_of_injective hi).map_of_injective hg
  have : NeZero ((S.r * S.N) ^ 2) := ⟨(pow_pos (Nat.mul_pos S.r_pos hN.pos) 2).ne'⟩
  have : IsDomain ((baseOver (Sp S.R)).left.presheaf.stalk y) := inferInstanceAs (IsDomain ((Sp S.R).presheaf.stalk y))
  obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one (ξ := ξ.val) (congrArg Units.val hξ)
  refine ⟨k, fun i => ?_⟩
  have e' := e S.J ρ.s (ρ.s i) _ _ _ (ρ.U_act a i) (fun l => ρ.ev_val l h) (ρ.ev_val i _)
  simp only [hgs] at e'
  have q : ∑ n, algebraMap o S.R (S.ρ a n i) * ⟨S.ev h n, S.ev_mem _ _⟩ =
      algebraMap o S.R (S.ζ ^ k) * ⟨S.ev (h + S.r • a) i, S.ev_mem _ _⟩ := hg (by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_mul, map_pow, map_pow, hk]
    simp only [map_mul]
    exact e')
  have q' := congrArg S.R.val q
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at q'
  exact q'

end GlobalTheory.ZH.EvCrd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionValuesCoordsOperatorPermuteStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
theorem _root_.GlobalTheory.T.torsionValues_coords_operator_permute : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), (∀ (K : Type) [Field K] (y : S.R →+* K) (a : S.Gam), ρ.Crd (spMap y ≫ (ρ.pt a).left) (fun i => y ⟨S.ev a i, S.ev_mem a i⟩)) ∧ ∀ a h : S.Gam, ∃ e : ℕ, ∀ i, ∑ n, algebraMap o Ω (S.ρ a n i) * S.ev h n = algebraMap o Ω (S.ζ ^ e) * S.ev (h + S.r • a) i := by
  first | exact @GlobalTheory.ZH.EvCrd.ev_crd_act | exact GlobalTheory.ZH.EvCrd.ev_crd_act | (intros; apply GlobalTheory.ZH.EvCrd.ev_crd_act <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeZeroOfLe
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.OpenPart

theorem le_nonzeroLocus_iff {k K : Type} [CommRing k] [Field K] {X : Scheme.{0}} {p : X ⟶ Sp k} {H : LB X}
    {J : Type} [Fintype J] {s : J → H.Sec} {a : J → k} {φ : H.Sec} (hφ : IsLin p s a φ)
    {x : Sp K ⟶ X} {ψ : k →+* K} (hx : x ≫ p = spMap ψ) {v : J → K} (hv : Crd H s x v) :
    ⊤ ≤ x ⁻¹ᵁ nonzeroLocus φ ↔ ∑ j, ψ (a j) * v j ≠ 0 := by
  have h : Crd H (fun _ : Unit => φ) x (fun _ => ∑ j, ψ (a j) * v j) := by
    obtain ⟨l, c, hl, hv⟩ := hv
    refine ⟨l, c, hl, fun _ => ?_⟩
    beta_reduce
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hφ l, CrdCalc.valR_eq x _ hl, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq,
      GlobalTheory.Points.valR_constFn_of_over p ψ x hx _ hl, hv, mul_left_comm]
  exact (CrdCalc.crd_isUnit_iff () h).symm.trans isUnit_iff_ne_zero

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {M : RatModel o Ω}

theorem TT_le_TT {z z' : M.Z} (h : S.supI M z' ⊆ S.supI M z) : S.TT M z ≤ S.TT M z' :=
  fun _ ha b hb => ha b (AddSubgroup.closure_mono h hb)

theorem isOpen_supI_subset (z : M.Z) : IsOpen {z' | S.supI M z ⊆ S.supI M z'} := by
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : {z' | S.supI M z ⊆ S.supI M z'} = ⋂ a ∈ S.supI M z, {z' | M.Div S.th a z'} := by
    ext z'
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rfl
  rw [this]
  exact (Set.toFinite _).isOpen_biInter fun a _ => M.isOpen_setOf_div _ _

theorem supI_subset {U₀ : M.Z.Opens} (h : S.Over₀ M U₀) (z : M.Z) {z' : M.Z} (hz' : z' ∈ U₀) :
    S.supI M z ⊆ S.supI M z' := fun a ha => ⟨ha.1, fun j => by
  rw [div_eq_mul_inv]
  exact RatModel.ringOn_le_O hz' (mul_mem (h.le (S.th_mem j)) (h.th_unit a ha.1))⟩

theorem exists_ne_zero_of_le {T T' : AddSubgroup S.Gam} (h : T' ≤ T) (hT : S.IsoFree T) (hT' : S.IsoFree T')
    {K : Type} [Field K] (ψ : o →+* K) (v : S.J → K) {i : S.J} (hi : ∑ j, ψ (S.proj T 0 j i) * v j ≠ 0) :
    ∃ i, ∑ j, ψ (S.proj T' 0 j i) * v j ≠ 0 := by
  by_contra hn
  push_neg at hn
  apply hi
  rw [← GlobalTheory.ThetaBound.proj_mul_proj S T T' h hT.1 hT' 0 0 fun _ => rfl]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  have := congrArg (ψ (S.proj T 0 k i) * ·) (hn k)
  simp only [Finset.mul_sum, mul_zero] at this
  rw [← this]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem le_preimage_G_iff : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (K : Type) [Field K] (x : Sp K ⟶ Q.P.left) (z : M.Z) (ψ : o →+* K) (v : S.J → K), Set.range (x ≫ Q.P.hom) = {z} → (IsClosed ({z} : Set M.Z) ∨ z ∈ U₀) → x ≫ Q.P.hom ≫ M.s = spMap ψ → Crd Q.O1 Q.st x v → (⊤ ≤ x ⁻¹ᵁ Q.G ↔ ∃ i, ∑ j, ψ (S.proj (S.TT M z) 0 j i) * v j ≠ 0) := by
  intro o Ω _ _ _ _ S ρ M U₀ EE hB Q K _ x z ψ v hz hc hψ hv
  have hψ' : x ≫ (Q.P.hom ≫ M.s) = spMap ψ := hψ
  have hxz : Q.P.hom (x (IsLocalRing.closedPoint K)) = z := by
    have : (x ≫ Q.P.hom) (IsLocalRing.closedPoint K) ∈ Set.range (x ≫ Q.P.hom) := ⟨_, rfl⟩
    rw [hz] at this
    exact this
  rw [CrdCalc.top_le_iff]
  simp only [Clos.G, TopologicalSpace.Opens.mem_iSup]
  constructor
  · rintro ⟨z', -, W, hW, i, φ, hφ, h1, h2⟩
    have h1' : z ∈ W := hxz ▸ h1
    exact exists_ne_zero_of_le (TT_le_TT (hW z h1')) (hB.free _).1 (hB.free _).1 ψ v
      ((le_nonzeroLocus_iff hφ hψ' hv).1 ((CrdCalc.top_le_iff x _).2 h2))
  · intro hi
    obtain ⟨z', hz', hs, hs'⟩ : ∃ z' : M.Z, IsClosed ({z'} : Set M.Z) ∧ S.supI M z' ⊆ S.supI M z ∧
        S.supI M z ⊆ S.supI M z' := by
      rcases hc with hc | hc
      · exact ⟨z, hc, le_rfl, le_rfl⟩
      · have := hB.jac
        obtain ⟨z', h1, h2⟩ := nonempty_inter_closedPoints (Z := (U₀ : Set M.Z)) ⟨z, hc⟩
          U₀.isOpen.isLocallyClosed
        exact ⟨z', h2, supI_subset hB.ov _ hc, supI_subset hB.ov _ h1⟩
    obtain ⟨i, hi⟩ := hi
    obtain ⟨i, hi⟩ := exists_ne_zero_of_le (TT_le_TT hs') (hB.free _).1 (hB.free _).1 ψ v hi
    obtain ⟨φ, hφ, -⟩ := GlobalTheory.SecRatio.existsUnique_isLin (Q.P.hom ≫ M.s) Q.st
      (fun j => S.proj (S.TT M z') 0 j i)
    refine ⟨z', hz', ⟨_, isOpen_supI_subset z'⟩, fun _ h => h, i, φ, hφ, ?_,
      (CrdCalc.top_le_iff x _).1 ((le_nonzeroLocus_iff hφ hψ' hv).2 hi)⟩
    change S.supI M z' ⊆ S.supI M (Q.P.hom (x (IsLocalRing.closedPoint K)))
    rw [hxz]
    exact hs

end GlobalTheory.ZH.OpenPart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfValFGeneric
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH
open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem RatModel.exists_eq_spMap_pt (M : RatModel o Ω) {K : Type} [Field K] (y : Sp K ⟶ M.Z)
    (hy : ∀ w, y w = genericPoint M.Z) : ∃ β : Ω →+* K, y = spMap β ≫ M.pt := by
  have hs : ∀ w, y w ⤳ genericPoint M.Z := fun w => (hy w) ▸ specializes_rfl
  have hm : ∀ x : Ω, x ∈ M.O (genericPoint M.Z) := fun x => by rw [RatModel.O_genericPoint]; trivial
  let β : Ω →+* K := (RatModel.valHomOf y _ hs).comp
    ((RingHom.id Ω).codRestrict (M.O (genericPoint M.Z)).toSubring hm)
  obtain ⟨U, hU, hz, -⟩ := exists_isAffineOpen_mem_and_subset (X := M.Z) (x := genericPoint M.Z) (U := ⊤) trivial
  have h1 : ⊤ ≤ y ⁻¹ᵁ U := fun w _ => by
    change y w ∈ U
    rw [hy]; exact hz
  have h2 : ⊤ ≤ M.pt ⁻¹ᵁ U := M.top_le_preimage_pt ⟨_, hz⟩
  refine ⟨β, ext_of_valR hU h1 (le_preimage_comp _ _ h2 (le_preimage_top _)) fun f => ?_⟩
  rw [valR_spMap_comp β M.pt U h2]
  exact (RatModel.val_valF ((top_le_preimage_iff _ _).1 h1) f).symm

variable {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

instance ZHPre.isIntegral : IsIntegral Q.G.left :=
  have := Q.semi
  isIntegral_left_of_isSemiAbelian Q.G

theorem ZHPre.hom_genericPoint : Q.G.hom (genericPoint Q.G.left) = genericPoint M.Z := by
  have hw : η[Q.G].left ≫ Q.G.hom = 𝟙 _ := Over.w η[Q.G]
  have h1 : Q.G.hom (η[Q.G].left (genericPoint M.Z)) = genericPoint M.Z :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun f : M.Z ⟶ M.Z => f (genericPoint M.Z)) hw)
  have h2 := (genericPoint_specializes (η[Q.G].left (genericPoint M.Z))).map Q.G.hom.continuous
  rw [h1] at h2
  exact (h2.antisymm (genericPoint_specializes _)).eq

theorem ZHPre.exists_generic (hU : (U₀ : Set M.Z).Nonempty) :
    ∃ (K : Type) (_ : Field K) (β : Ω →+* K) (g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀)
      (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left) (jP : ρ.P.L.ι),
      g ≫ pullback.snd _ _ ≫ U₀.ι = spMap β ≫ M.pt ∧
      r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _ ∧
      Set.range (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⊆ ρ.P.L.U jP ∧
      ∀ w, (g ≫ Q.φ) w = genericPoint Q.G.left := by
  let K : Type := Q.G.left.residueField (genericPoint Q.G.left)
  let x : Sp K ⟶ Q.G.left := Q.G.left.fromSpecResidueField (genericPoint Q.G.left)
  have hx : ∀ w, x w = genericPoint Q.G.left := fun w => Scheme.fromSpecResidueField_apply _ _
  have hx' : ∀ w, (x ≫ Q.G.hom) w = genericPoint M.Z := fun w => by
    rw [Scheme.Hom.comp_apply, hx, Q.hom_genericPoint]
  obtain ⟨β, hβ⟩ := M.exists_eq_spMap_pt (x ≫ Q.G.hom) hx'
  have hg : genericPoint M.Z ∈ U₀ := (genericPoint_specializes hU.some).mem_open U₀.isOpen hU.some_mem
  have hr : Set.range (x ≫ Q.G.hom) ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [hx', Scheme.Opens.range_ι]
    exact hg
  let y : Sp K ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι (x ≫ Q.G.hom) hr
  have hy : y ≫ U₀.ι = x ≫ Q.G.hom := IsOpenImmersion.lift_fac _ _ _
  let g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀ := Q.cart.1.lift x y hy.symm
  have hg1 : g ≫ Q.φ = x := Q.cart.1.lift_fst x y hy.symm
  have hg2 : g ≫ pullback.snd _ _ = y := Q.cart.1.lift_snd x y hy.symm
  obtain ⟨jP, hj⟩ := exists_le_preimage_of_iSup_eq_top (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ρ.P.isLB.cover
  refine ⟨K, inferInstance, β, g, pullback.lift ((g ≫ pullback.fst _ _) ≫ ρ.P.A.hom) (g ≫ pullback.fst _ _)
    (Category.comp_id _), jP, ?_, pullback.lift_snd _ _ _, (top_le_preimage_iff _ _).1 hj, fun w => hg1 ▸ hx w⟩
  rw [← Category.assoc, hg2, hy, hβ]

theorem eq_of_valF_generic {X : Scheme.{0}} [IsIntegral X] {K : Type} [Field K] (x : Sp K ⟶ X)
    (hx : ∀ w, x w = genericPoint X) {U : X.Opens} {f f' : Γ(X, U)}
    (h : ⊤ ≤ x ⁻¹ᵁ U → valF x U f = valF x U f') : f = f' := by
  by_contra h0
  have hne : ((X.basicOpen (f - f') : X.Opens) : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun h => h0 (sub_eq_zero.1 ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h)))
  have h1 : ⊤ ≤ x ⁻¹ᵁ X.basicOpen (f - f') := fun w _ => by
    change x w ∈ X.basicOpen (f - f')
    rw [hx]
    exact (genericPoint_specializes hne.some).mem_open (X.basicOpen _).isOpen hne.some_mem
  have h2 : ⊤ ≤ x ⁻¹ᵁ U := le_preimage_mono x (X.basicOpen_le _) h1
  have hu := (le_preimage_basicOpen_iff x h2 _).1 h1
  have h3 := h h2
  rw [valF_eq_valR, valF_eq_valR, valR_eq x U h2, valR_eq x U h2] at h3
  rw [valR_eq x U h2, map_sub, h3, sub_self] at hu
  exact not_isUnit_zero hu

theorem ZHPre.eq_of_genVal (hU : (U₀ : Set M.Z).Nonempty) (k : ℤ) {I : Type} [Fintype I]
    (t : I → LB.Sec (LPow ρ.P.A ρ.P.L k (baseOver (Sp S.R)))) (c : I → Ω) (V : Q.G.left.Opens)
    (σ σ' : ∀ j, Γ(Q.G.left, V ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U j))
    (h : GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t c V σ) (h' : GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t c V σ') :
    σ = σ' := by
  obtain ⟨K, _, β, g, r, jP, h1, h2, h3, h4⟩ := Q.exists_generic hU
  funext j
  obtain ⟨jL, rfl⟩ : ∃ jL, j = fun _ => jL := ⟨j 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  refine eq_of_valF_generic (g ≫ Q.φ) h4 fun hm => ?_
  have hm' := (top_le_preimage_iff _ _).1 hm
  have hV : Set.range (g ≫ Q.φ) ⊆ V := fun y hy => (hm' hy).1
  have hL : Set.range (g ≫ Q.φ) ⊆ Q.L.L.U jL := fun y hy => Set.mem_iInter.1 (hm' hy).2 0
  have e := (h K β g r jP jL h1 h2 h3 hL hV).symm.trans (h' K β g r jP jL h1 h2 h3 hL hV)
  refine mul_left_cancel₀ (zpow_ne_zero _ ?_) e
  refine IsUnit.ne_zero ?_
  have hw : ⊤ ≤ g ⁻¹ᵁ (LB.div (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀)) (Q.L.L.pull Q.φ)).U
      (fun _ => jP, fun _ => jL) := fun w _ =>
    ⟨Set.mem_iInter.2 fun _ => h3 ⟨w, Scheme.Hom.comp_apply _ _ _⟩,
      Set.mem_iInter.2 fun _ => hL ⟨w, Scheme.Hom.comp_apply _ _ _⟩⟩
  rw [valF_eq_valR, valR_eq g _ hw]
  exact (Units.isUnit _).map _

end GlobalTheory.ZH
end
