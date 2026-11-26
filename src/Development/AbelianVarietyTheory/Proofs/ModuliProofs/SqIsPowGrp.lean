module

public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNormalisedIsoPullbackMulByM
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfInvariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SqIsPowGrp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

noncomputable section

namespace GlobalTheory.SquarePol

variable {S : Scheme.{0}}

def sqIsPowGrp (G : Over S) [GrpObj G] : Out.IsPowGrp (G ⊗ G) G 2 where
  pr := ![fst G G, snd G G]
  hom := fun i => by
    fin_cases i
    · exact inferInstanceAs (IsMonHom (fst G G))
    · exact inferInstanceAs (IsMonHom (snd G G))
  lim := Fan.IsLimit.mk _ (fun s => lift (s.proj 0) (s.proj 1))
    (fun s i => by
      fin_cases i
      · exact lift_fst _ _
      · exact lift_snd _ _)
    (fun s m hm => by
      apply CartesianMonoidalCategory.hom_ext
      · exact (hm 0).trans (lift_fst _ _).symm
      · exact (hm 1).trans (lift_snd _ _).symm)

def sqPol (P : Out.PolAV S) : Out.PolAV S :=
  haveI : IsCommMonObj P.A := P.isAb.comm
  haveI : ∀ i, IsMonHom ((sqIsPowGrp P.A).pr i) := (sqIsPowGrp P.A).hom
  { A := P.A ⊗ P.A
    isAb := (PowGrp.powers S _ P.A 2 (sqIsPowGrp P.A)).2.2.2.1 P.isAb
    g := 2 * P.g
    smoothDim := (PowGrp.powers S _ P.A 2 (sqIsPowGrp P.A)).2.2.1 P.g P.smoothDim
    L := Out.boxLB P.L (sqIsPowGrp P.A).pr
    isLB := DVR.linComb_isLB _ P.isLB _ _
    rigid := by
      obtain ⟨r, hr⟩ := P.rigid
      exact ⟨_, BoxPower.boxRig_isGen (sqIsPowGrp P.A) P.L r hr⟩
    sym := BoxPower.sym_box _ _ P.sym
    ample := relAmple_boxLB S _ P.A 2 (sqIsPowGrp P.A) P.L P.isLB P.ample
    ktriv := kTriv_boxLB S _ P.A 2 (sqIsPowGrp P.A) P.L P.isLB P.ktriv }

theorem sqPol_L (P : Out.PolAV S) :
    (sqPol P).L = LB.LinComb P.L (K := Fin 2) ![(fst P.A P.A).left, (snd P.A P.A).left] ![1, 1] := by
  simp only [sqPol, Out.boxLB]
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem exists_square : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)), ∃ (P₂ : Out.PolAV (Sp K)) (e : P₂.A ≅ P.A ⊗ P.A), IsMonHom (e.hom ≫ fst P.A P.A) ∧ IsMonHom (e.hom ≫ snd P.A P.A) ∧ P₂.g = 2 * P.g ∧ LBIso P₂.L (LB.LinComb P.L (K := Fin 2) ![(e.hom ≫ fst P.A P.A).left, (e.hom ≫ snd P.A P.A).left] ![1, 1]) := by
  intro K _ _ P
  refine ⟨sqPol P, Iso.refl _, ?_, ?_, rfl, ?_⟩
  · show IsMonHom (𝟙 (P.A ⊗ P.A) ≫ fst P.A P.A)
    rw [Category.id_comp]
    exact (sqIsPowGrp P.A).hom 0
  · show IsMonHom (𝟙 (P.A ⊗ P.A) ≫ snd P.A P.A)
    rw [Category.id_comp]
    exact (sqIsPowGrp P.A).hom 1
  · show LBIso (sqPol P).L (LB.LinComb P.L (K := Fin 2)
      ![(𝟙 (P.A ⊗ P.A) ≫ fst P.A P.A).left, (𝟙 (P.A ⊗ P.A) ≫ snd P.A P.A).left] ![1, 1])
    simp only [Category.id_comp]
    have h : LBIso (sqPol P).L (sqPol P).L := ⟨idIso _, idIso_isGen (sqPol P).isLB⟩
    rw [sqPol_L] at h ⊢
    exact h

end GlobalTheory.SquarePol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTripleOfFieldExtension
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TripleDescent

variable {S S' : Scheme.{0}} {f : S' ⟶ S}

theorem lift_left_fst {T X Y : Over S} (a : T ⟶ X) (b : T ⟶ Y) : (lift a b).left ≫ (fst X Y).left = a.left :=
  congrArg (fun q => q.left) (lift_fst a b)

theorem lift_left_snd {T X Y : Over S} (a : T ⟶ X) (b : T ⟶ Y) : (lift a b).left ≫ (snd X Y).left = b.left :=
  congrArg (fun q => q.left) (lift_snd a b)

theorem isPullback_tensor {X Y : Over S} {X' Y' : Over S'} {a : X'.left ⟶ X.left} {b : Y'.left ⟶ Y.left}
    (ha : IsPullback a X'.hom X.hom f) (hb : IsPullback b Y'.hom Y.hom f) (c : (X' ⊗ Y').left ⟶ (X ⊗ Y).left)
    (c₁ : c ≫ (fst X Y).left = (fst X' Y').left ≫ a) (c₂ : c ≫ (snd X Y).left = (snd X' Y').left ≫ b) :
    IsPullback c (X' ⊗ Y').hom (X ⊗ Y).hom f := by
  have p : IsPullback (snd X Y).left (fst X Y).left Y.hom X.hom := (IsPullback.of_hasPullback X.hom Y.hom).flip
  have p' : IsPullback (snd X' Y').left (fst X' Y').left Y'.hom X'.hom :=
    (IsPullback.of_hasPullback X'.hom Y'.hom).flip
  have q := p'.paste_horiz hb
  rw [← c₂, ← ha.w] at q
  have r := (IsPullback.of_right q c₁ p).paste_vert ha
  rwa [Over.w, Over.w] at r

variable {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left}

theorem lbIso_cubeLB_pull (h : IsGrpPullback G' G f φ) (hw : LBIso L' (L.pull φ)) {T' : Over S'} {T : Over S} {n : ℕ}
    (x' : Fin n → (T' ⟶ G')) (x : Fin n → (T ⟶ G)) (U : Over.mk (T'.hom ≫ f) ⟶ T)
    (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i) :
    LBIso (cubeLB G' x' L') ((cubeLB G x L).pull U.left) := by
  obtain ⟨w, hw⟩ := hw
  exact (iso_linComb ((isGen_iff w).1 hw) _ _).chartPull (chartPullId _)
    (chartPullOut L _ _ U.left _ fun I => psum_push h x' x U hx I.down)

theorem exists_gen_cubeLB_pull (h : IsGrpPullback G' G f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ))
    {T' : Over S'} {T : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ G')) (x : Fin n → (T ⟶ G))
    (U : Over.mk (T'.hom ≫ f) ⟶ T) (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i) (t : (cubeLB G' x' L').Gen)
    (ht : t.IsGen) : ∃ t : ((cubeLB G x L).pull U.left).Gen, t.IsGen := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨c, hc, -⟩ := exists_up ((isGen_iff w).1 hw) hL hL' t ht
  exact gen_chartPull (chartPullOut L _ _ U.left _ fun I => psum_push h x' x U hx I.down) c hc

end GlobalTheory.TripleDescent


open GlobalTheory.TripleDescent in
theorem GlobalTheory.exists_triple_of_fieldExtension : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (τ : SAB H (Sp K)) (A₀ : Over (Sp K₀)) [GrpObj A₀] (φ : τ.G.left ⟶ A₀.left) (L₀ : LB A₀.left) (r : OAct (𝓞 E) A₀), IsAbelianScheme A₀ → IsGrpPullback τ.G A₀ (spMap i) φ → L₀.IsLB → LBIso τ.PP.L (L₀.pull φ) → (∀ c, (τ.act.act c).left ≫ φ = φ ≫ (r.act c).left) → ∃ (τ₀ : SAB H (Sp K₀)) (e : τ₀.G ≅ A₀), IsMonHom e.hom ∧ LBIso τ₀.PP.L (L₀.pull e.hom.left) ∧ ∀ c, τ₀.act.act c ≫ e.hom = e.hom ≫ r.act c := by
  intro hLaws E _ _ _ H K₀ K _ _ i τ A₀ _ φ L₀ r hA h hL₀ hw hact
  have := hA.comm
  have A₂ := AbelianSchemeGerms.isAbelianScheme_tensor A₀ A₀ hA hA
  have A₃ := AbelianSchemeGerms.isAbelianScheme_tensor A₀ _ hA A₂
  have lb : ∀ {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ B))
      {L : LB B.left}, L.IsLB → (cubeLB B x L).IsLB := fun x L hL => DVR.linComb_isLB _ hL _ _
  have pa : ∀ {T : Over (Sp K)} (x : T ⟶ τ.G) a,
      pushPt h.1.w (x ≫ τ.act.act a) = pushPt h.1.w x ≫ r.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  have hP := τ.PP.isLB
  let U₁ := pushPt h.1.w (𝟙 τ.G)
  have e₁ : U₁.left = φ := Category.id_comp _
  let U₂ := lift (pushPt h.1.w (fst τ.G τ.G)) (pushPt h.1.w (snd τ.G τ.G))
  let U₃ := lift (pushPt h.1.w (x3 τ.G 0)) (lift (pushPt h.1.w (x3 τ.G 1)) (pushPt h.1.w (x3 τ.G 2)))
  have u₁ : U₂.left ≫ (fst A₀ A₀).left = (fst τ.G τ.G).left ≫ φ := lift_left_fst _ _
  have u₂ : U₂.left ≫ (snd A₀ A₀).left = (snd τ.G τ.G).left ≫ φ := lift_left_snd _ _
  have P₂ : IsPullback U₂.left (τ.G ⊗ τ.G).hom (A₀ ⊗ A₀).hom (spMap i) := isPullback_tensor h.1 h.1 _ u₁ u₂
  have P₃ : IsPullback U₃.left (τ.G ⊗ τ.G ⊗ τ.G).hom (A₀ ⊗ A₀ ⊗ A₀).hom (spMap i) := by
    refine isPullback_tensor h.1 P₂ _ (lift_left_fst _ _) ?_
    refine (lift_left_snd _ _).trans ?_
    apply pullback.hom_ext
    · refine (lift_left_fst _ _).trans (Eq.symm ?_)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) u₁).trans (Category.assoc _ _ _).symm)
    · refine (lift_left_snd _ _).trans (Eq.symm ?_)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) u₂).trans (Category.assoc _ _ _).symm)
  have D₁ := GlobalTheory.T.lineBundle_trivial_iso_descend_field K₀ K i _ _ A₀.hom _ _ hA.smooth hA.proper hA.geomConnected h.1
  have D₂ := GlobalTheory.T.lineBundle_trivial_iso_descend_field K₀ K i _ _ (A₀ ⊗ A₀).hom _ _ A₂.smooth A₂.proper A₂.geomConnected P₂
  have D₃ := GlobalTheory.T.lineBundle_trivial_iso_descend_field K₀ K i _ _ (A₀ ⊗ A₀ ⊗ A₀).hom _ _ A₃.smooth A₃.proper A₃.geomConnected P₃
  have hT : ∃ t : LB.Gen (Theta A₀ L₀), t.IsGen := D₃.1 _ (lb _ hL₀)
    (exists_gen_cubeLB_pull h hL₀ hP hw (x3 τ.G) (x3 A₀) U₃ (fun j => by fin_cases j <;> simp [x3, U₃])
      τ.cub.t τ.cub.isGen)
  have ha : ∀ a, LBIso (cubeLB A₀ ![fst A₀ A₀ ≫ r.act a, snd A₀ A₀] L₀)
      (cubeLB A₀ ![fst A₀ A₀, snd A₀ A₀ ≫ r.act (H.bar a)] L₀) := fun a => by
    have k₁ := lbIso_cubeLB_pull h hw ![fst τ.G τ.G ≫ τ.act.act a, snd τ.G τ.G]
      ![fst A₀ A₀ ≫ r.act a, snd A₀ A₀] U₂ (fun j => by
        fin_cases j
        · exact (pa _ a).trans (by simp [U₂])
        · simp [U₂])
    have k₂ := lbIso_cubeLB_pull h hw ![fst τ.G τ.G, snd τ.G τ.G ≫ τ.act.act (H.bar a)]
      ![fst A₀ A₀, snd A₀ A₀ ≫ r.act (H.bar a)] U₂ (fun j => by
        fin_cases j
        · simp [U₂]
        · exact (pa _ _).trans (by simp [U₂]))
    exact D₂.2 _ _ (lb _ hL₀) (lb _ hL₀) (LBIso.trans (pull_isLB (lb _ hL₀) _) (by exact lb _ hP) (pull_isLB (lb _ hL₀) _)
      k₁.symm (LBIso.trans (by exact lb _ hP) (by exact lb _ hP) (pull_isLB (lb _ hL₀) _) (τ.adj a) k₂))
  have hp : LBIso L₀ (cubeLB A₀ ![𝟙 A₀, r.act H.w0] L₀) := by
    have k := lbIso_cubeLB_pull h hw ![𝟙 τ.G, τ.act.act H.w0] ![𝟙 A₀, r.act H.w0] U₁ (fun j => by
      fin_cases j
      · simp [U₁]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _))
    rw [e₁] at k
    exact D₁.2 _ _ hL₀ (lb _ hL₀) (LBIso.trans (pull_isLB hL₀ _) hP (pull_isLB (lb _ hL₀) _)
      hw.symm (LBIso.trans hP (by exact lb _ hP) (pull_isLB (lb _ hL₀) _) τ.prim k))
  obtain ⟨PP, cub, sym, iso, -, prim, adj⟩ :=
    GlobalTheory.PrimNorm.exists_primitive_normalisation hLaws.globalFns E H _ A₀ r L₀ hA hL₀ hT ha
  refine ⟨⟨A₀, GlobalTheory.isSemiAbelian_of_isAbelianScheme A₀ hA, r, PP, cub, sym, adj, prim⟩, Iso.refl _,
    inferInstanceAs (IsMonHom (𝟙 A₀)), ?_, fun c => (Category.comp_id _).trans (Category.id_comp _).symm⟩
  exact (LBIso.trans PP.isLB (lb _ hL₀) hL₀ iso hp.symm).chartPull (chartPullId _) (chartPullPull L₀ _ (𝟙 _) rfl)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAffineCoverOfQuotient
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.QuotientNorm

open TopologicalSpace

theorem exists_lb_of_cocycle {Y : Scheme.{0}} {K : Type} (V : K → Y.Opens) (hV : ⨆ i, V i = ⊤)
    (a : ∀ i, K → Γ(Y, V i)) (h₁ : ∀ i, a i i = 1) (hle : ∀ i j, Y.basicOpen (a i j) ≤ V j)
    (hc : ∀ i j k, resG Y (inf_le_left : V i ⊓ V j ≤ V i) (a i k) =
      resG Y (inf_le_left : V i ⊓ V j ≤ V i) (a i j) * resG Y (inf_le_right : V i ⊓ V j ≤ V j) (a j k)) :
    ∃ (L : LB Y) (σ : K → LB.Sec L), L.IsLB ∧ ∀ j, Out.nonzeroLocus (σ j) = V j := by
  have hu (i j) : IsUnit (resG Y (inf_le_left : V i ⊓ V j ≤ V i) (a i j)) :=
    IsUnit.of_mul_eq_one _ ((hc i j i).symm.trans (by rw [h₁, map_one]))
  have hg (i j) (y : Y) (hy : y ∈ V i ⊓ V j) :
      gs (𝟙 Y) y (V i ⊓ V j) (hu i j).unit.val = gs (𝟙 Y) y (V i) (a i j) := gs_res _ y _ hy _
  have hc' (i j k) (y : Y) (hy : y ∈ V i ⊓ V j) :
      gs (𝟙 Y) y (V i) (a i k) = gs (𝟙 Y) y (V i) (a i j) * gs (𝟙 Y) y (V j) (a j k) := by
    have e := congrArg (gs (𝟙 Y) y _) (hc i j k)
    rwa [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy] at e
  refine ⟨⟨K, V, fun i j => (hu i j).unit⟩, fun k => ⟨fun i => a i k, fun i j => hc i j k⟩,
    ⟨hV, fun i => Units.ext (fn_ext fun y hy => ?_), fun i j k => Units.ext (fn_ext fun y hy => ?_)⟩, fun j => ?_⟩
  · exact (gs_res (𝟙 Y) y (le_inf le_rfl le_rfl) hy _).trans ((hg i i y ⟨hy, hy⟩).trans (by rw [h₁]; rfl))
  · refine (gs_mul (𝟙 Y) y _ hy _ _).trans ?_
    refine (congrArg₂ (· * ·) ((gs_res (𝟙 Y) y inf_le_left hy _).trans (hg i j y hy.1))
      ((gs_res (𝟙 Y) y (le_inf (inf_le_left.trans inf_le_right) inf_le_right) hy _).trans
        (hg j k y ⟨hy.1.2, hy.2⟩))).trans ((hc' i j k y hy.1).symm.trans ?_)
    exact ((gs_res (𝟙 Y) y (le_inf (inf_le_left.trans inf_le_left) inf_le_right) hy _).trans
      (hg i k y ⟨hy.1.1, hy.2⟩)).symm
  · refine le_antisymm (iSup_le fun i => hle i j) (le_trans ?_ (basicOpen_le_nonzeroLocus _ j))
    exact (Y.basicOpen_of_isUnit (f := a j j) (h₁ j ▸ isUnit_one)).ge

variable {G : Type} [Group G] {X Y : Scheme.{0}} {ρ : G →* Aut X} {π : X ⟶ Y}

theorem eq_of_gs (h : IsAffineQuotient ρ π) {W : Y.Opens} {a b : Γ(Y, W)}
    (e : ∀ x, π x ∈ W → gs π x W a = gs π x W b) : a = b :=
  h.app_injective W (fn_ext fun x hx => (gs_pull (𝟙 X) π x W hx a).trans
    (((Category.id_comp π).symm ▸ e x hx :).trans (gs_pull (𝟙 X) π x W hx b).symm))

theorem exists_norm [Fintype G] (h : IsAffineQuotient ρ π) {W : Y.Opens} {D : X.Opens}
    (hD : ∀ g, π ⁻¹ᵁ W ≤ (ρ g).asIso.hom ⁻¹ᵁ D) (r : Γ(X, D)) :
    ∃ a : Γ(Y, W), ∀ x, π x ∈ W → gs π x W a = ∏ g, gs (ρ g).asIso.hom x D r := by
  obtain ⟨a, ha⟩ := h.mem_range_app W (∏ g, (ρ g).asIso.hom.appLE D _ (hD g) r) fun k => ⟨h.preimage_le W k, by
    rw [map_prod]
    refine Fintype.prod_equiv (Equiv.mulRight k) _ _ fun g => ?_
    have : (ρ (g * k)).asIso.hom = (ρ k).asIso.hom ≫ (ρ g).asIso.hom := by rw [map_mul]; rfl
    simp only [Equiv.coe_mulRight, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, this]⟩
  refine ⟨a, fun x hx => ?_⟩
  have e := gs_pull (𝟙 X) π x W hx a
  rw [Category.id_comp] at e
  rw [← e, show (π.app W).hom a = _ from ha, gs_eq (𝟙 X) x (π ⁻¹ᵁ W) hx, map_prod, map_prod]
  refine Finset.prod_congr rfl fun g _ => ?_
  exact (gs_eq (𝟙 X) x (π ⁻¹ᵁ W) hx _).symm.trans ((gs_appLE _ D _ (hD g) (𝟙 X) x hx r).trans (by rw [Category.id_comp]))

theorem exists_affine_cover_of_quotient :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → X.IsSeparated → ∀ (L : LB X) (n : ℕ) (σ : Fin n → LB.Sec L), L.IsLB → (∀ i, IsAffineOpen (Out.nonzeroLocus (σ i))) → (∀ x : X, ∃ i, ∀ g, (ρ g).asIso.hom x ∈ Out.nonzeroLocus (σ i)) → (∃ (L : LB X') (n : ℕ) (σ : Fin n → LB.Sec L), L.IsLB ∧ (∀ i, IsAffineOpen (Out.nonzeroLocus (σ i))) ∧ ⨆ i, Out.nonzeroLocus (σ i) = ⊤) := by
  rintro G _ _ X Y ρ π H _ L n σ - haff hcov
  classical
  have := Fintype.ofFinite G
  obtain ⟨-, hsurj, -, -, hst⟩ := quotient_isIntegral_surjective_orbits G X Y ρ π H
  have h : IsAffineQuotient ρ π :=
    ⟨H.2.1, H.1, fun W => (H.2.2 W).1, fun W s hs => (H.2.2 W).2 s fun g _ => (hs g).2⟩
  let W : Fin n → X.Opens := fun i => ⨅ g, (ρ g).asIso.hom ⁻¹ᵁ Out.nonzeroLocus (σ i)
  have hW (i x) : x ∈ W i ↔ ∀ g, (ρ g).asIso.hom x ∈ Out.nonzeroLocus (σ i) := by
    change x ∈ ((W i : X.Opens) : Set X) ↔ _
    simp only [W, Opens.coe_iInf, Set.mem_iInter]
    rfl
  choose V hV using fun i => hst (W i) fun k => by
    ext x
    change (ρ k).asIso.hom x ∈ W i ↔ x ∈ W i
    simp only [hW, ← aut_map_mul_apply]
    exact ⟨fun e g => by simpa using e (g * k⁻¹), fun e g => e _⟩
  have hm (i x) : π x ∈ V i ↔ ∀ g, (ρ g).asIso.hom x ∈ Out.nonzeroLocus (σ i) := by
    rw [← hW, ← hV]; rfl
  choose r hr using fun i j => AmpleSpan.exists_isRatio (σ j) (σ i)
  choose a ha using fun i j => exists_norm h (W := V i) (D := Out.nonzeroLocus (σ i)) (fun g x hx => (hm i x).1 hx g) (r i j)
  have top : ⨆ i, V i = ⊤ := top_le_iff.1 fun y _ => by
    obtain ⟨x, rfl⟩ := π.surjective y
    obtain ⟨i, hi⟩ := hcov x
    exact Opens.mem_iSup.2 ⟨i, (hm i x).2 hi⟩
  have hc (i j k) (f : X ⟶ X) (x : X) (hi : f x ∈ Out.nonzeroLocus (σ i)) (hj : f x ∈ Out.nonzeroLocus (σ j)) :
      gs f x _ (r i k) = gs f x _ (r i j) * gs f x _ (r j k) := by
    obtain ⟨l, hl⟩ := exists_chart_of_mem_nonzeroLocus hi
    refine ((mem_nonzeroLocus_iff_pull _ f x hl).1 hi).mul_right_cancel ?_
    rw [← (hr i k).gs f x hi hl, (hr j k).gs f x hj hl, (hr i j).gs f x hi hl]
    ring
  obtain ⟨L', σ', hL', hσ'⟩ := exists_lb_of_cocycle V top a
    (fun i => eq_of_gs h fun x hx => by
      rw [ha i i x hx, AmpleSpan.gs_one' _ _ _ hx]
      refine Finset.prod_eq_one fun g _ => ?_
      have hi := (hm i x).1 hx g
      obtain ⟨l, hl⟩ := exists_chart_of_mem_nonzeroLocus hi
      refine ((mem_nonzeroLocus_iff_pull _ _ x hl).1 hi).mul_right_cancel ?_
      rw [← (hr i i).gs _ x hi hl, _root_.one_mul])
    (fun i j y hy => by
      obtain ⟨x, rfl⟩ := π.surjective y
      have hx : π x ∈ V i := Y.basicOpen_le _ hy
      have u := (LBGerm.isUnit_gs_iff π x _ hx _).2 hy
      rw [ha i j x hx, IsUnit.prod_univ_iff] at u
      refine (hm j x).2 fun g => ?_
      have := (LBGerm.isUnit_gs_iff _ x _ ((hm i x).1 hx g) _).1 (u g)
      rw [(hr i j).basicOpen] at this
      exact this.2)
    (fun i j k => eq_of_gs h fun x hx => by
      rw [gs_res _ x _ hx, gs_mul _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx, ha i k x hx.1, ha i j x hx.1,
        ha j k x hx.2, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun g _ => hc i j k _ x ((hm i x).1 hx.1 g) ((hm j x).1 hx.2 g))
  refine ⟨L', n, σ', hL', fun i => ?_, by simp only [hσ', top]⟩
  rw [hσ']
  refine h.isAffineOpen_of_preimage ?_
  rw [hV]
  exact IsAffineOpen.iInf fun g => (haff i).preimage (ρ g).asIso.hom

end GlobalTheory.QuotientNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGrpPullbackRetraction
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

def translInvIso {S : Scheme.{0}} (B : Over S) [GrpObj B] (c : 𝟙_ (Over S) ⟶ B) : B ≅ B where
  hom := 𝟙 B * (toUnit B ≫ c)⁻¹
  inv := 𝟙 B * (toUnit B ≫ c)
  hom_inv_id := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit, inv_mul_cancel_right]
  inv_hom_id := by
    rw [MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv, ← Category.assoc, comp_toUnit, mul_inv_cancel_right]

theorem comp_translInvIso_hom {S : Scheme.{0}} {B T : Over S} [GrpObj B] (c : 𝟙_ (Over S) ⟶ B) (x : T ⟶ B) :
    x ≫ (translInvIso B c).hom = x * (toUnit T ≫ c)⁻¹ := by
  simp [translInvIso, MonObj.comp_mul, GrpObj.comp_inv]

theorem unit_left_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : η[G'].left ≫ φ = f ≫ η[G].left := by
  have hw : (η[G'].left ≫ φ) ≫ G.hom = (Over.mk ((𝟙_ (Over S')).hom ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    rfl
  let u : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G := Over.homMk (η[G'].left ≫ φ) hw
  have hη : (η[G'] : 𝟙_ (Over S') ⟶ G') * η[G'] = η[G'] := by
    rw [MonObj.one_eq_one]
    exact _root_.one_mul _
  have huu : u * u = u := by
    ext1
    rw [h.2 _ η[G'] η[G'] u u rfl rfl, hη]
    rfl
  have hu1 : u = 1 := mul_eq_left.mp huu
  have := congrArg (fun v => CommaMorphism.left v) hu1
  simpa [u, Hom.one_def] using this

theorem exists_isGrpPullback_retraction (rig : Out.RigiditySt) {S S' : Scheme.{0}} (A₀ : Over S) [GrpObj A₀]
    (A' : Over S') [GrpObj A'] (f : S' ⟶ S) (i : S ⟶ S') (ρ₀ : A'.left ⟶ A₀.left) (j : A₀.left ⟶ A'.left)
    (h₀ : IsAbelianScheme A₀) (h' : IsAbelianScheme A') (hj : IsGrpPullback A₀ A' i j)
    (hρ : IsPullback ρ₀ A'.hom A₀.hom f) (hjρ : j ≫ ρ₀ = 𝟙 _) :
    ∃ ρ, IsGrpPullback A' A₀ f ρ ∧ j ≫ ρ = 𝟙 _ := by
  let adj := Over.mapPullbackAdj f
  let B : Over S' := Over.mk (pullback.snd A₀.hom f)
  let F : (Over S')ᵒᵖ ⥤ GrpCat := (Over.map f).op ⋙ yonedaGrpObj A₀
  let α : (F ⋙ forget _).RepresentableBy B :=
    { homEquiv := (adj.homEquiv _ _).symm
      homEquiv_comp := fun g h => (adj.representableBy A₀).homEquiv_comp g h }
  let _ : GrpObj B := GrpObj.ofRepresentableBy B F α
  let E : ∀ T : Over S', (T ⟶ B) ≃ ((Over.map f).obj T ⟶ A₀) := fun T => (adj.homEquiv T A₀).symm
  have hmul : ∀ {T : Over S'} (x y : T ⟶ B), E T (x * y) = E T x * E T y := by
    intro T x y
    exact ((yonedaGrpObjIsoOfRepresentableBy B F α).hom.app (Opposite.op T)).hom.map_mul x y
  have hinv : ∀ {T : Over S'} (x : T ⟶ B), E T x⁻¹ = (E T x)⁻¹ := by
    intro T x
    exact ((yonedaGrpObjIsoOfRepresentableBy B F α).hom.app (Opposite.op T)).hom.map_inv x
  have hleft : ∀ {T : Over S'} (x : T ⟶ B), (E T x).left = x.left ≫ pullback.fst A₀.hom f :=
    fun x => rfl
  have hB : IsGrpPullback B A₀ f (pullback.fst A₀.hom f) := by
    refine ⟨IsPullback.of_hasPullback A₀.hom f, ?_⟩
    intro T x y x₁ y₁ hx hy
    have ex : x₁ = E T x := by ext1; rw [hx, hleft]
    have ey : y₁ = E T y := by ext1; rw [hy, hleft]
    rw [ex, ey, ← hmul, hleft]
  have hBab : IsAbelianScheme B := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback h₀ hB
  let x₀ : (Over.map f).obj A' ⟶ A₀ := Over.homMk ρ₀ (by rw [hρ.w]; rfl)
  let m₀ : A' ⟶ B := (E A').symm x₀
  have hm₀ : m₀.left ≫ pullback.fst A₀.hom f = ρ₀ := by
    rw [← hleft]
    change (E A' ((E A').symm x₀)).left = ρ₀
    rw [Equiv.apply_symm_apply]
    rfl
  let c : 𝟙_ (Over S') ⟶ B := η[A'] ≫ m₀
  let m : A' ⟶ B := m₀ ≫ (translInvIso B c).hom
  have hm : m = m₀ * (toUnit A' ≫ c)⁻¹ := comp_translInvIso_hom c m₀
  have hm1 : η[A'] ≫ m = η[B] := by
    rw [← Category.assoc, comp_translInvIso_hom, MonObj.one_eq_one, toUnit_unit, Category.id_comp]
    exact _root_.mul_inv_cancel c
  have : IsMonHom m := rig S' A' B h' hBab m hm1
  refine ⟨m.left ≫ pullback.fst A₀.hom f, ⟨?_, ?_⟩, ?_⟩
  · have h1 : IsIso m₀.left := by
      have e : m₀.left = hρ.isoPullback.hom := by
        apply pullback.hom_ext
        · rw [IsPullback.isoPullback_hom_fst]; exact hm₀
        · rw [IsPullback.isoPullback_hom_snd]; exact Over.w m₀
      rw [e]; infer_instance
    have h2 : IsIso (translInvIso B c).hom.left :=
      inferInstanceAs (IsIso ((Over.forget S').map (translInvIso B c).hom))
    have h3 : IsIso m.left := by
      change IsIso (m₀.left ≫ (translInvIso B c).hom.left)
      infer_instance
    have sq : IsPullback m.left A'.hom B.hom (𝟙 S') :=
      IsPullback.of_horiz_isIso ⟨by rw [Over.w m, Category.comp_id]⟩
    have := sq.paste_horiz (IsPullback.of_hasPullback A₀.hom f)
    rwa [Category.id_comp] at this
  · intro T x y x₁ y₁ hx hy
    rw [hB.2 T (x ≫ m) (y ≫ m) x₁ y₁ (by rw [hx, ← Category.assoc]; rfl)
      (by rw [hy, ← Category.assoc]; rfl), ← MonObj.mul_comp, ← Category.assoc]
    rfl
  · have hJ : j ≫ ((Over.map f).obj A').hom = A₀.hom := by
      change j ≫ A'.hom ≫ f = A₀.hom
      rw [← hρ.w, ← Category.assoc, hjρ, Category.id_comp]
    let J : A₀ ⟶ (Over.map f).obj A' := Over.homMk j hJ
    have hρm : m.left ≫ pullback.fst A₀.hom f = (x₀ * (E A' (toUnit A' ≫ c))⁻¹).left := by
      rw [← hleft, hm, hmul, hinv, Equiv.apply_symm_apply]
    have hc : c.left ≫ pullback.fst A₀.hom f = η[A'].left ≫ ρ₀ := by
      change (η[A'].left ≫ m₀.left) ≫ _ = _
      rw [Category.assoc, hm₀]
    have hz : J ≫ E A' (toUnit A' ≫ c) = 1 := by
      ext1
      change j ≫ (A'.hom ≫ c.left) ≫ pullback.fst A₀.hom f = A₀.hom ≫ η[A₀].left
      rw [Category.assoc, hc, ← Category.assoc j, hj.1.w]
      simp only [Category.assoc]
      rw [← Category.assoc i, ← unit_left_comp hj, Category.assoc, hjρ, Category.comp_id]
    have hJx : J ≫ x₀ = 𝟙 A₀ := by
      ext1
      exact hjρ
    calc j ≫ m.left ≫ pullback.fst A₀.hom f = (J ≫ (x₀ * (E A' (toUnit A' ≫ c))⁻¹)).left := by
          rw [hρm]; rfl
      _ = 𝟙 A₀.left := by
          rw [MonObj.comp_mul, GrpObj.comp_inv, hJx, hz, _root_.inv_one, _root_.mul_one]; rfl

theorem exists_isConst_of_isPullback :
    Out.Laws → ∀ (A₀ : Over (Sp ℂ)) [GrpObj A₀] (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (ρ₀ : A'.left ⟶ A₀.left) (j : A₀.left ⟶ A'.left), IsAbelianScheme A₀ → IsAbelianScheme A' → IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j → IsPullback ρ₀ A'.hom A₀.hom (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ₀ = 𝟙 _ → ∃ ρ, IsConst A' A₀ ρ j := by
  intro hL A₀ _ A' _ ρ₀ j h₀ h' hj hρ hjρ
  obtain ⟨ρ, hρ', hjρ'⟩ := exists_isGrpPullback_retraction hL.rigidity A₀ A' _ _ ρ₀ j h₀ h' hj hρ hjρ
  exact ⟨ρ, by unfold IsConst; exact ⟨hρ', hj, hjρ'⟩⟩

end GlobalTheory.KS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNonzeroCoordinateAffineChart
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNonzeroCoordinateAffineChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.CoordChart

private theorem isIso_restrict_lemma {X Z Y : Scheme.{0}} (x : X ⟶ Z) [Mono x] (j : Y ⟶ X)
    [IsOpenImmersion (j ≫ x)] : IsIso (x ∣_ (j ≫ x).opensRange) := by
  set V := (j ≫ x).opensRange with hV
  let s : V.toScheme ⟶ X := (j ≫ x).isoOpensRange.inv ≫ j
  have hs : s ≫ x = V.ι := by
    rw [← cancel_epi (j ≫ x).isoOpensRange.hom]
    simp only [s, Category.assoc, Iso.hom_inv_id_assoc]
    exact (Scheme.Hom.isoOpensRange_hom_ι (j ≫ x)).symm
  have hr : Set.range s ⊆ Set.range (x ⁻¹ᵁ V).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    show x (s y) ∈ V
    have e : x (s y) = V.ι y := by rw [← Scheme.Hom.comp_apply, hs]
    rw [e]
    have hm : V.ι y ∈ Set.range V.ι := ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι] at hm
    exact hm
  let s' := IsOpenImmersion.lift (x ⁻¹ᵁ V).ι s hr
  have h1 : s' ≫ (x ⁻¹ᵁ V).ι = s := IsOpenImmersion.lift_fac _ _ _
  refine ⟨⟨s', ?_, ?_⟩⟩
  · rw [← cancel_mono ((x ⁻¹ᵁ V).ι ≫ x), Category.assoc, reassoc_of% h1, hs, morphismRestrict_ι,
      Category.id_comp]
  · rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, reassoc_of% h1, hs, Category.id_comp]

theorem isOpenImmersion_of_mono_of_local {X Z : Scheme.{0}} (x : X ⟶ Z) [Mono x]
    (h : ∀ p : X, ∃ (Y : Scheme.{0}) (j : Y ⟶ X), IsOpenImmersion (j ≫ x) ∧
      x p ∈ Set.range (j ≫ x)) : IsOpenImmersion x := by
  choose Y j hj hp using h
  refine IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsOpenImmersion)
    (fun p => (j p ≫ x).opensRange) ?_ (fun p => ?_)
  · rintro _ ⟨p, rfl⟩
    simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion, SetLike.mem_coe]
    exact ⟨p, by rw [Scheme.Hom.mem_opensRange]; exact hp p⟩
  · have := isIso_restrict_lemma x (j p)
    infer_instance

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, CommRingCat.ofHom_comp]

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
    f = g := by
  have e := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  simpa using e

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (y : Sp B ⟶ Sp A) :
    ∃ f : A →+* B, y = spMap f := by
  refine ⟨(Spec.preimage y).hom, ?_⟩
  simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]

theorem mono_of_ring_points {A : Type} [CommRing A] {Z : Scheme.{0}} (x : Sp A ⟶ Z)
    (h : ∀ (B : Type) [CommRing B] (f g : A →+* B), spMap f ≫ x = spMap g ≫ x → f = g) : Mono x := by
  refine ⟨fun {W} a b hab => ?_⟩
  have key : ∀ (B : Type) [CommRing B] (t : Sp B ⟶ W), t ≫ a = t ≫ b := by
    intro B _ t
    obtain ⟨f, hf⟩ := exists_spMap (t ≫ a)
    obtain ⟨g, hg⟩ := exists_spMap (t ≫ b)
    have hfg : f = g := h _ f g (by rw [← hf, ← hg, Category.assoc, Category.assoc, hab])
    rw [hf, hg, hfg]
  exact W.affineOpenCover.openCover.hom_ext a b
    (fun k => key (W.affineOpenCover.X k) (W.affineOpenCover.openCover.f k))

theorem exists_chart : ∀ (R σ : Type) [CommRing R] (I : Ideal (MvPolynomial σ R)) (Z : Scheme.{0}) (s : Z ⟶ Sp R) (M : LB Z) (th : σ → M.Sec) (i : σ), ProjRep I s M th → ∃ x : Sp (MvPolynomial σ R ⧸ (I ⊔ Ideal.span {MvPolynomial.X i - 1})) ⟶ Z, IsOpenImmersion x ∧ Set.range x = (Out.nonzeroLocus (th i) : Set Z) ∧ x ≫ s = spMap ((Ideal.Quotient.mk _).comp MvPolynomial.C) ∧ SecCoord M th x (fun a => Ideal.Quotient.mk _ (MvPolynomial.X a)) := by
  intro R σ _ I Z s M th i hP
  obtain ⟨hM, hpts, hrep⟩ := hP
  set J := I ⊔ Ideal.span {MvPolynomial.X i - 1} with hJ
  set q := Ideal.Quotient.mk J with hq

  have hq1 : q (MvPolynomial.X i) = 1 := by
    rw [← sub_eq_zero, ← map_one q, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.subset_span rfl)

  have hev : ∀ F, MvPolynomial.eval₂ (q.comp MvPolynomial.C) (fun a => q (MvPolynomial.X a)) F = q F := by
    intro F
    have e : MvPolynomial.eval₂Hom (q.comp MvPolynomial.C) (fun a => q (MvPolynomial.X a)) = q :=
      MvPolynomial.ringHom_ext (fun r => by simp) (fun a => by simp)
    exact RingHom.congr_fun e F
  obtain ⟨x, ⟨hxs, hxc⟩, -⟩ := hrep _ (q.comp MvPolynomial.C) (fun a => q (MvPolynomial.X a))
    (by rw [Ideal.eq_top_iff_one, ← hq1]; exact Ideal.subset_span ⟨i, rfl⟩)
    (fun F hF => by rw [hev, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.mem_sup_left hF)

  have hmono : Mono x := by
    apply mono_of_ring_points
    intro B _ f g hfg
    have hcf := GlobalTheory.ZM.Coord.baseChange hxc f
    have hcg := GlobalTheory.ZM.Coord.baseChange hxc g
    rw [hfg] at hcf
    obtain ⟨u, hu⟩ := GlobalTheory.ZM.Coord.unique hM hcg hcf
    have hu1 : (u : B) = 1 := by
      have e := hu i
      simp only [hq1, map_one] at e
      simpa using e.symm
    have hv : ∀ a, f (q (MvPolynomial.X a)) = g (q (MvPolynomial.X a)) := fun a => by
      rw [hu a, hu1, _root_.one_mul]
    have hb : f.comp (q.comp MvPolynomial.C) = g.comp (q.comp MvPolynomial.C) := by
      apply spMap_inj
      rw [← spMap_comp (q.comp MvPolynomial.C) f, ← spMap_comp (q.comp MvPolynomial.C) g, ← hxs,
        reassoc_of% hfg]
    have hc : f.comp q = g.comp q :=
      MvPolynomial.ringHom_ext (fun r => by simpa using RingHom.congr_fun hb r) (fun a => by simpa using hv a)
    exact Ideal.Quotient.ringHom_ext hc

  have hsub : Set.range x ⊆ (Out.nonzeroLocus (th i) : Set Z) := by
    rintro _ ⟨p, rfl⟩
    refine (GlobalTheory.ZM.CoordMove.mem_nonzeroLocus_iff hM i p hxc).2 ?_
    show q (MvPolynomial.X i) ∉ p.asIdeal
    rw [hq1]
    exact fun h1 => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

  have hloc : ∀ z ∈ (Out.nonzeroLocus (th i) : Set Z), ∃ (B : Type) (_ : CommRing B)
      (ψ : (MvPolynomial σ R ⧸ J) →+* B), IsOpenImmersion (spMap ψ ≫ x) ∧ z ∈ Set.range (spMap ψ ≫ x) := by
    intro z hz
    obtain ⟨R', _, x', v', hx'o, ⟨p, rfl⟩, hx'c⟩ := (GlobalTheory.T.sectionCoordinateVector_exists_locally Z M σ th hM).2.2 z
    have hp : v' i ∉ p.asIdeal := (GlobalTheory.ZM.CoordMove.mem_nonzeroLocus_iff hM i p hx'c).1 hz
    have hunit : IsUnit (algebraMap R' (Localization.Away (v' i)) (v' i)) :=
      IsLocalization.Away.algebraMap_isUnit (v' i)
    have hc1 := GlobalTheory.ZM.Coord.scale (GlobalTheory.ZM.Coord.baseChange hx'c (algebraMap R' (Localization.Away (v' i))))
      hunit.unit⁻¹
    set w : σ → Localization.Away (v' i) :=
      fun a => ((hunit.unit⁻¹ : (Localization.Away (v' i))ˣ) : Localization.Away (v' i)) *
        algebraMap R' (Localization.Away (v' i)) (v' a) with hw
    have hwi : w i = 1 := by simp [w]
    obtain ⟨β', hβ'⟩ := exists_spMap ((spMap (algebraMap R' (Localization.Away (v' i))) ≫ x') ≫ s)
    obtain ⟨hspan, hI⟩ := hpts _ β' _ w hβ' hc1
    have hker : J ≤ RingHom.ker (MvPolynomial.eval₂Hom β' w) := by
      refine sup_le (fun F hF => hI F hF) (Ideal.span_le.2 ?_)
      rintro _ rfl
      simp [hwi]
    let ψ : (MvPolynomial σ R ⧸ J) →+* Localization.Away (v' i) :=
      Ideal.Quotient.lift J (MvPolynomial.eval₂Hom β' w) (fun F hF => hker hF)
    have hψC : ∀ r, ψ (q (MvPolynomial.C r)) = β' r := fun r =>
      (Ideal.Quotient.lift_mk J _ _).trans (by simp)
    have hψX : ∀ a, ψ (q (MvPolynomial.X a)) = w a := fun a =>
      (Ideal.Quotient.lift_mk J _ _).trans (by simp)
    obtain ⟨y, -, hyu⟩ := hrep _ β' w hspan hI
    have e2 : spMap (algebraMap R' (Localization.Away (v' i))) ≫ x' = y := hyu _ ⟨hβ', hc1⟩
    have e1 : spMap ψ ≫ x = y := by
      refine hyu _ ⟨?_, ?_⟩
      · rw [Category.assoc, hxs, spMap_comp]
        congr 1
        exact RingHom.ext hψC
      · have e := GlobalTheory.ZM.Coord.baseChange hxc ψ
        convert e using 2 with a
        exact (hψX a).symm
    have hrange := PrimeSpectrum.localization_away_comap_range (Localization.Away (v' i)) (v' i)
    have hpm : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R' (Localization.Away (v' i)))) := by
      rw [hrange]
      exact hp
    obtain ⟨p', hp'⟩ := hpm
    refine ⟨Localization.Away (v' i), inferInstance, ψ, ?_, p', ?_⟩
    · rw [e1, ← e2]
      infer_instance
    · rw [e1, ← e2]
      show x' (PrimeSpectrum.comap (algebraMap R' (Localization.Away (v' i))) p') = x' p
      rw [hp']
  have := hmono
  refine ⟨x, ?_, ?_, hxs, hxc⟩
  · apply isOpenImmersion_of_mono_of_local x
    intro p
    obtain ⟨B, _, ψ, h1, h2⟩ := hloc (x p) (hsub ⟨p, rfl⟩)
    exact ⟨Sp B, spMap ψ, h1, h2⟩
  · refine Set.Subset.antisymm hsub (fun z hz => ?_)
    obtain ⟨B, _, ψ, -, ⟨b, hb⟩⟩ := hloc z hz
    exact ⟨(spMap ψ) b, hb⟩

end GlobalTheory.ZM.CoordChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNonzeroCoordinateAffineChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzeroCoordinate_affineChart : ∀ (R σ : Type) [CommRing R] (I : Ideal (MvPolynomial σ R)) (Z : Scheme.{0}) (s : Z ⟶ Sp R) (M : LB Z) (th : σ → M.Sec) (i : σ), ProjRep I s M th → ∃ x : Sp (MvPolynomial σ R ⧸ (I ⊔ Ideal.span {MvPolynomial.X i - 1})) ⟶ Z, IsOpenImmersion x ∧ Set.range x = (Out.nonzeroLocus (th i) : Set Z) ∧ x ≫ s = spMap ((Ideal.Quotient.mk _).comp MvPolynomial.C) ∧ SecCoord M th x (fun a => Ideal.Quotient.mk _ (MvPolynomial.X a)) := by
  first | exact @GlobalTheory.ZM.CoordChart.exists_chart | exact GlobalTheory.ZM.CoordChart.exists_chart | (intros; apply GlobalTheory.ZM.CoordChart.exists_chart <;> assumption)
end
end
