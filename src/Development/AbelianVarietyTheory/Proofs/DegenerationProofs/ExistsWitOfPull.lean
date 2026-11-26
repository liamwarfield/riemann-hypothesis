module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsIsoPairOfEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomExtOfIsOpenImmersion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWitOfPull
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.WitnessMove

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}


set_option maxHeartbeats 1600000 in
theorem unif_move (hU : Out.UnifBaseChangeSt) (h5 : Out.Laws5) {Y : Model Xo c β} {O' : Type} [CommRing O']
    [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b} {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    (hR : Out.AdmBase R I) {f : O' →+* R} {u : R} {χ : Sp R ⟶ Y.X} (t : SAB H (Sp R)) (m : SABMap t Y.t χ)
    (W' : ArcWit Y a I f u χ) (ψ : t.G ≅ W'.t.G)
    [IsMonHom ψ.hom] (hφ : ψ.hom.left ≫ W'.m.φ = m.φ) (hact : ∀ x, t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) :
    ∃ (bc : t.G ≅ (Over.pullback (Out.specOf (RingHom.id R))).obj W'.t.G) (D'' : Out.DegData R I)
      (hD : Out.IsPullDeg (RingHom.id R) W'.P.D.toPre D''.toPre) (U'' : Out.Unif I D'' W'.P.A t.G)
      (_ : Module (𝓞 E) D''.toPre.X) (oD : letI := H.starRing; D''.toPre.OAct (𝓞 E)),
      IsMonHom bc.hom ∧ bc.hom.left ≫ pullback.fst W'.t.G.hom (Out.specOf (RingHom.id R)) = ψ.hom.left ∧
      U''.LG = t.PP ∧
      U''.gen.hom.left ≫ W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R) =
        pullback.fst t.G.hom (Out.jK R) ≫ ψ.hom.left ∧
      Out.IsPullUnif (RingHom.id R) hD bc W'.P.U U'' ∧
      (∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y) ∧
      (letI := H.starRing; ∀ x, oD.onB.act x ≫ hD.e.hom =
        hD.e.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.P.oD.onB.act x)) ∧
      (letI := H.starRing; U''.toUnifPre.OLinear (𝓞 E) oD W'.P.oA t.act.toRingAct) ∧
      (letI := H.starRing; TraceFormTwistIso D''.toPre oD H.w0) := by
  let _ := H.starRing
  have hs := specOf_id R
  have gp₁ : IsGrpPullback t.G W'.t.G (Out.specOf (RingHom.id R)) ψ.hom.left :=
    (isGrpPullback_of_iso ψ).congr hs.symm rfl
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso gp₁ (isGrpPullback_pullback W'.t.G (Out.specOf (RingHom.id R)))
  have gpG : IsGrpPullback W'.P.A.A W'.t.G (Out.jK R) (W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R)) := by
    have := W'.P.U.gen_hom
    have : IsMonHom W'.P.U.gen.symm.hom := by show IsMonHom W'.P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso W'.P.U.gen.symm).comp (isGrpPullback_pullback W'.t.G (Out.jK R))).congr
      (Category.id_comp _) rfl
  have gp₂ : IsGrpPullback ((Over.pullback (Out.jK R)).obj t.G) W'.t.G (Out.jK R)
      (pullback.fst t.G.hom (Out.jK R) ≫ ψ.hom.left) :=
    ((isGrpPullback_pullback t.G (Out.jK R)).comp (isGrpPullback_of_iso ψ)).congr (Category.comp_id _) rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp₂ gpG
  have hgi : W'.P.U.gen.inv.left ≫ W'.P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have wA : LBIso (W'.P.A.L.pull eA.hom.left) (W'.P.U.LG.L.pull (pullback.fst t.G.hom (Out.jK R) ≫ bc.hom.left ≫
      pullback.fst W'.t.G.hom (Out.specOf (RingHom.id R)))) :=
    LBIso.chartPull (h := eA.hom.left ≫ W'.P.U.gen.inv.left)
      (chartPullSame W'.P.A.L (fun _ => eA.hom.left) (fun _ => W'.P.U.gen.hom.left) _ _ fun _ => by
        rw [Category.assoc, hgi, Category.comp_id])
      (chartPullSame W'.P.U.LG.L _ (fun _ => pullback.fst W'.t.G.hom (Out.jK R)) _ _ fun _ => by
        rw [hbc, ← heA]; simp only [Category.assoc]) W'.P.U.ext
  obtain ⟨wL', he', gL, rL⟩ := rigIso_congr W'.P.bundle (CubeMap.ofHom ψ.hom) (sabMap_cubical m W'.m ψ hφ) hbc
    (e := Out.specOf (RingHom.id R)) hs
  obtain ⟨Wo, hWo, hψW⟩ := h5.psiOnExists R I hR W'.P.D
  have hgen : (Out.specOf (RingHom.id R)).base (genericPoint (Spec (CommRingCat.of R))) ∈ Wo := by
    rw [hs]; exact hWo
  have hI : I.map (RingHom.id R) ≤ I := by rw [Ideal.map_id]
  obtain ⟨D'', hD, U'', hLG, hgenU, hPU⟩ := hU R R I I hR hR (RingHom.id R) hI W'.P.D W'.P.A W'.t.G W'.t.semi W'.P.U
    Wo hψW hgen t.G bc mbc W'.P.A rfl eA mE wA t.PP wL' he' gL rL
  have hbcact : ∀ x, t.act.toRingAct.act x ≫ bc.hom =
      bc.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.toRingAct.act x) := by
    intro x
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · have a₂ : ((Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.act x)).left ≫
          pullback.fst W'.t.G.hom (Out.specOf (RingHom.id R)) = pullback.fst _ _ ≫ (W'.t.act.act x).left :=
        pullback.lift_fst _ _ _
      show (t.act.act x ≫ bc.hom).left ≫ _ =
        (bc.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.act x)).left ≫ _
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, a₂, hbc, ← Category.assoc, hbc,
        ← Over.comp_left, hact, Over.comp_left]
    · exact (Over.w (t.act.act x ≫ bc.hom)).trans
        (Over.w (bc.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.act x))).symm
  have actA : ∀ x, (W'.P.oA.act x).left ≫ W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R) =
      W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R) ≫ (W'.t.act.act x).left := by
    intro x
    have e : W'.P.oA.act x ≫ W'.P.U.gen.inv = W'.P.U.gen.inv ≫ (Over.pullback (Out.jK R)).map (W'.t.act.act x) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (W'.P.lin.ext x)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  have extA : ∀ x, (Over.pullback (Out.jK R)).map (t.act.toRingAct.act x) ≫ U''.gen.hom =
      U''.gen.hom ≫ W'.P.oA.act x := by
    intro x
    rw [hgenU]
    apply Over.OverMorphism.ext
    apply gpG.1.hom_ext
    · have a₁ : ((Over.pullback (Out.jK R)).map (t.act.act x)).left ≫ pullback.fst t.G.hom (Out.jK R) =
          pullback.fst t.G.hom (Out.jK R) ≫ (t.act.act x).left := pullback.lift_fst _ _ _
      have a₃ : (t.act.act x).left ≫ ψ.hom.left = ψ.hom.left ≫ (W'.t.act.act x).left := by
        rw [← Over.comp_left, hact, Over.comp_left]
      show ((Over.pullback (Out.jK R)).map (t.act.act x) ≫ eA.hom).left ≫ _ = (eA.hom ≫ W'.P.oA.act x).left ≫ _
      rw [Over.comp_left, Category.assoc, heA, ← Category.assoc, a₁, Category.assoc, a₃, Over.comp_left,
        Category.assoc, actA, reassoc_of% heA]
    · rw [Over.w, Over.w]
  obtain ⟨mod'', oD'', xl, el, lin'', w0''⟩ := h5.oLinBaseChange R R I I hR hR (RingHom.id R) W'.P.D W'.P.A W'.t.G W'.P.U
    t.G bc mbc W'.P.A D'' hD U'' hPU (𝓞 E) W'.P.oD W'.P.oA W'.t.act.toRingAct W'.P.lin t.act.toRingAct hbcact
    W'.P.oA extA
  refine ⟨bc, D'', hD, U'', mod'', oD'', mbc, hbc, hLG, ?_, hPU, xl, el, lin'', w0'' H.w0 W'.P.w0⟩
  rw [hgenU]; exact heA


set_option maxHeartbeats 1600000 in
theorem exists_wit_of_pull (h5 : Out.Laws5) (hQ : QkPullExistsSt) {Y : Model Xo c β} {O' : Type} [CommRing O']
    [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b} {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    (hR : Out.AdmBase R I) {f : O' →+* R} {u : R} {χ : Sp R ⟶ Y.X} (W : ArcWit Y a I f u χ) (t : SAB H (Sp R))
    (m : SABMap t Y.t χ) (P : PELUnif I t)
    (bc : t.G ≅ (Over.pullback (Out.specOf (RingHom.id R))).obj W.t.G) [IsMonHom bc.hom]
    (hbc : bc.hom.left ≫ pullback.fst W.t.G.hom (Out.specOf (RingHom.id R)) ≫ W.m.φ = m.φ)
    (hD : Out.IsPullDeg (RingHom.id R) W.P.D.toPre P.D.toPre) (hPU : Out.IsPullUnif (RingHom.id R) hD bc W.P.U P.U)
    (xl : ∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y)
    (el : letI := H.starRing; ∀ x, P.oD.onB.act x ≫ hD.e.hom =
      hD.e.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W.P.oD.onB.act x)) :
    ∃ W' : ArcWit Y a I f u χ, W'.t = t ∧ HEq W'.m m ∧ HEq W'.P P := by
  letI := H.starRing
  obtain ⟨he, w, e, -, -, d1, d2, d3, d4, d5, d6⟩ := ArcWit.witMove h5 hQ hR W P.U P.oD bc hD hPU xl el
  refine ⟨⟨t, m, P, _, he, w, e, d1, d2, d3, d4, d5, fun F _ _ _ _ uF h1 h2 => ⟨(d6 F uF h1 h2).1,
    fun yF hyF k p₀ σ hσ q₀ q x e1 e2 e3 e4 => (d6 F uF h1 h2).2 yF hyF k p₀ σ hσ q₀ q x e1 e2 e3 ?_⟩⟩,
    rfl, HEq.rfl, HEq.rfl⟩
  rw [hbc]; exact e4


set_option maxHeartbeats 1600000 in
theorem exists_wit (hU : Out.UnifBaseChangeSt) (h5 : Out.Laws5) (h6 : Out.UnifUniqSt) (hQ : QkPullExistsSt)
    {Y : Model Xo c β} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b} {R : Type}
    [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} (hR : Out.AdmBase R I) {f : O' →+* R} {u : R}
    {χ : Sp R ⟶ Y.X} (W : ArcWit Y a I f u χ) (t : SAB H (Sp R)) (m : SABMap t Y.t χ) (P : PELUnif I t) :
    ∃ W' : ArcWit Y a I f u χ, W'.t = t ∧ HEq W'.m m ∧ HEq W'.P P := by
  letI := H.starRing
  have hs := specOf_id R
  obtain ⟨ψ, hψ, hφ, hact, -⟩ := sabMap_iso m W.m rfl rfl
  obtain ⟨bc, D'', hD₂, U'', mod'', oD'', mbc, hbc, hLG, -, hPU₂, xl₂, el₂, lin'', w0''⟩ :=
    unif_move hU h5 hR t m W ψ hφ hact
  let P'' : PELUnif I t :=
    { D := D'', mod := mod'', oD := oD'', A := W.P.A, oA := W.P.oA, U := U'', bundle := hLG, lin := lin'', w0 := w0'' }
  obtain ⟨⟨t₁, m₁, P₁, φ₁, he₁, w₁, e₁, s₁⟩, rfl, hm₁, hP₁⟩ := exists_wit_of_pull h5 hQ hR W t m P'' bc
    (by rw [reassoc_of% hbc, hφ]) hD₂ hPU₂ xl₂ el₂
  obtain rfl : m₁ = m := eq_of_heq hm₁
  clear hP₁
  have res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h : W ≤ V) (h' : V ≤ U)
      (x : Γ(X, U)ˣ) : res h (res h' x) = res (h.trans h') x := by
    have e : X.presheaf.map (homOfLE h').op ≫ X.presheaf.map (homOfLE h).op =
        X.presheaf.map (homOfLE (h.trans h')).op := by
      rw [← Functor.map_comp]
      rfl
    apply Units.ext
    exact congrArg (fun φ => φ.hom (x : Γ(X, U))) e

  have res_g_mul_res_g_eq_res_g_of_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (i j k : L.ι) {W : X.Opens}
      (h₁ : W ≤ L.U i ⊓ L.U j) (h₂ : W ≤ L.U j ⊓ L.U k) (h₃ : W ≤ L.U i ⊓ L.U k) :
      res h₁ (L.g i j) * res h₂ (L.g j k) = res h₃ (L.g i k) := by
    have hW : W ≤ L.U i ⊓ L.U j ⊓ L.U k := le_inf h₁ (h₂.trans inf_le_right)
    have key := congrArg (⇑(res hW)) (hL.cocycle i j k)
    simp only [map_mul, res_res_lemma] at key
    exact key

  have isGen_g_iso_self_of_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) :
      (⟨fun p : L.ι × L.ι => L.g p.1 p.2⟩ : LB.Iso L L).IsGen := by
    rintro ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
    have h₀ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₁ ⊓ L.U p₂ := inf_le_left
    have h₁ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₁ ⊓ L.U q₁ :=
      le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    have h₂ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U q₁ ⊓ L.U q₂ := inf_le_right
    have h₃ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₁ ⊓ L.U q₂ :=
      le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)
    have h₄ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₂ ⊓ L.U q₂ :=
      le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
    have c₁ := res_g_mul_res_g_eq_res_g_of_isLB hL p₁ q₁ q₂ h₁ h₂ h₃
    have c₂ := res_g_mul_res_g_eq_res_g_of_isLB hL p₁ p₂ q₂ h₀ h₄ h₃
    have key : res h₀ (L.g p₁ p₂) =
        res h₁ (L.g p₁ q₁) * (res h₄ (L.g p₂ q₂))⁻¹ * res h₂ (L.g q₁ q₂) := by
      rw [mul_right_comm, c₁, ← c₂, mul_inv_cancel_right]
    exact key

  have exists_iso_pair_of_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L₁ L₂ : RigLB G}
      (h : L₁ = L₂) :
      ∃ (w : LB.Iso L₁.L L₂.L) (w' : LB.Iso L₂.L L₁.L), w.IsGen ∧ w'.IsGen ∧
        LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₁.rig L₂.rig ∧
        LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₂.rig L₁.rig := by
    cases h
    refine ⟨⟨fun p : L₁.L.ι × L₁.L.ι => L₁.L.g p.1 p.2⟩, ⟨fun p : L₁.L.ι × L₁.L.ι => L₁.L.g p.1 p.2⟩,
      isGen_g_iso_self_of_isLB L₁.isLB, isGen_g_iso_self_of_isLB L₁.isLB, ?_, ?_⟩
    · intro p
      exact L₁.rigGen p.1 p.2
    · intro p
      exact L₁.rigGen p.1 p.2
  obtain ⟨wL₀, -, g₀, -, m₀, -⟩ := exists_iso_pair_of_eq (P.bundle.trans P₁.bundle.symm)
  obtain ⟨hD₁, hlev, holin⟩ := h6 R I hR P₁.D P.D P₁.A P.A t₁.G t₁.semi P₁.U P.U wL₀ g₀ m₀
  obtain ⟨xl₁, el₁⟩ := holin (𝓞 E) P₁.oD P.oD P₁.oA P.oA t₁.act.toRingAct P₁.lin P.lin
  have mR : IsMonHom (Iso.refl t₁.G).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨bc₀, mbc₀, hbc₀⟩ := grpPullback_iso ((isGrpPullback_of_iso (Iso.refl t₁.G)).congr hs.symm rfl)
    (isGrpPullback_pullback t₁.G (Out.specOf (RingHom.id R)))
  have hbc₀' : bc₀.hom.left ≫ pullback.fst t₁.G.hom (Out.specOf (RingHom.id R)) = 𝟙 _ := hbc₀
  have hPU₁ := isPullUnif_of_uniq P₁.U P.U hD₁ wL₀ g₀ m₀ hlev bc₀ hbc₀'
  exact exists_wit_of_pull h5 hQ hR ⟨t₁, m₁, P₁, φ₁, he₁, w₁, e₁, s₁⟩ t₁ m₁ P bc₀
    (by rw [← Category.assoc]; exact (congrArg (· ≫ m₁.φ) hbc₀').trans (Category.id_comp _)) hD₁ hPU₁ xl₁ el₁

end GlobalTheory.WitnessMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsHomRangeSubset
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
  {Ω' : Type} [Field Ω'] [Algebra o Ω'] {M' : RatModel o Ω'} {φ : Ω →ₐ[o] Ω'}

theorem comp_toSpecΓ_eq_valMap {C : Type} [CommRing C] {X : Scheme.{0}} (V : X.Opens) (p : Sp C ⟶ V)
    (h : ⊤ ≤ (p ≫ V.ι) ⁻¹ᵁ V) : p ≫ V.toSpecΓ = Spec.map (valMap (p ≫ V.ι) V h) := by
  rw [Scheme.Opens.toSpecΓ, Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, valMap,
    ← Spec.map_comp, ← Spec.map_comp]
  have e : V.topIso.inv ≫ p.appTop = (p ≫ V.ι).appLE V ⊤ h := by
    rw [← Scheme.Hom.appLE_comp_appLE p V.ι V ⊤ ⊤ (by simp) le_top, Scheme.Opens.ι_appLE, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE]
    rfl
  rw [← e]

theorem exists_hom_range_subset {U : M.Z.Opens} (hU : IsAffineOpen U) (hUne : (U : Set M.Z).Nonempty)
    {V : M'.Z.Opens} (hVne : (V : Set M'.Z).Nonempty) (h : ∀ x ∈ M.ringOn U, φ x ∈ M'.ringOn V) :
    ∃ (p : Sp Ω' ⟶ V) (g : (V : Scheme.{0}) ⟶ M.Z), p ≫ V.ι = M'.pt ∧ Set.range g ⊆ U ∧
      p ≫ g = spMap φ.toRingHom ≫ M.pt := by
  let χ : M.ringOn U →+* M'.ringOn V :=
    (φ.toRingHom.comp (M.ringOn U).val.toRingHom).codRestrict (M'.ringOn V) fun x => h x x.2
  let ψ : Γ(M.Z, U) →+* Γ(M'.Z, V) :=
    (M'.sectionsEquiv V hVne).symm.toRingHom.comp (χ.comp (M.sectionsEquiv U hUne).toRingHom)
  have hr : Set.range M'.pt ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    exact (top_le_preimage_iff _ _).1 (M'.top_le_preimage_pt hVne)
  have hp := IsOpenImmersion.lift_fac V.ι M'.pt hr
  set p := IsOpenImmersion.lift V.ι M'.pt hr
  have hp' : p ≫ V.toSpecΓ = Spec.map (valMap M'.pt V (M'.top_le_preimage_pt hVne)) := by
    have := comp_toSpecΓ_eq_valMap V p (hp ▸ M'.top_le_preimage_pt hVne)
    simpa only [hp] using this
  refine ⟨p, V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec, hp, ?_, ?_⟩
  · rintro _ ⟨w, rfl⟩
    rw [← hU.range_fromSpec]
    exact ⟨_, rfl⟩
  rw [← Category.assoc, hp']
  conv_rhs => rw [← specMap_valMap_fromSpec hU M.pt (M.top_le_preimage_pt hUne)]
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  ext a
  have e : (M'.sectionsEquiv V hVne (ψ a) : Ω') = φ (M.sectionsEquiv U hUne a) :=
    congrArg Subtype.val ((M'.sectionsEquiv V hVne).apply_symm_apply _)
  exact e

theorem IsHom.map_mem_of_ringOn {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' φ f) {U : M.Z.Opens} (hU : IsAffineOpen U)
    (hUne : (U : Set M.Z).Nonempty) {V : M'.Z.Opens} (h : ∀ x ∈ M.ringOn U, φ x ∈ M'.ringOn V) {z : M'.Z}
    (hz : z ∈ V) : f z ∈ U := by
  obtain ⟨p, g, hp, hg, e⟩ := exists_hom_range_subset hU hUne ⟨z, hz⟩ h
  have e' : V.ι ≫ f = g := hom_ext_of_isOpenImmersion V.ι hp (by rw [← Category.assoc, hp]; exact hf) e
  exact hg ⟨⟨z, hz⟩, by rw [← e']; rfl⟩

theorem isAffineOpen_of_isHom (R : Subalgebra o Ω) [Algebra.FiniteType o R] [IsFractionRing R Ω] {U : M.Z.Opens}
    (hR : R ≤ M.ringOn U) {g : (ofAffine o Ω R).Z ⟶ M.Z} (hg : M.IsHom (ofAffine o Ω R) (AlgHom.id o Ω) g)
    (hU : Set.range g ⊆ U) : IsAffineOpen U ∧ M.ringOn U = R := by
  have hne : (U : Set M.Z).Nonempty := ⟨_, hU ⟨genericPoint _, rfl⟩⟩
  refine ⟨?_, le_antisymm (fun x hx => ?_) hR⟩
  · haveI : IsAffine (ofAffine o Ω R).Z := inferInstanceAs (IsAffine (Sp R))
    obtain ⟨p, h, hp, -, e⟩ := exists_hom_range_subset (M := ofAffine o Ω R) (φ := AlgHom.id o Ω)
      (isAffineOpen_top _) ⟨genericPoint _, trivial⟩ hne fun x hx => by
        obtain ⟨a, rfl⟩ := mem_ringOn_univ_ofAffine.1 hx
        exact hR a.2
    have hid : spMap (AlgHom.id o Ω).toRingHom = 𝟙 _ := Spec.map_id _
    have hg' : (ofAffine o Ω R).pt ≫ g = M.pt := by
      have := hg
      rwa [IsHom, hid, Category.id_comp] at this
    have e1 : h ≫ g = U.ι := hom_ext_of_isOpenImmersion (φ := AlgHom.id o Ω) U.ι hp
      (by rw [← Category.assoc, e, Category.assoc, hg']) (by rw [hp, hid, Category.id_comp])
    have hr : Set.range g ⊆ Set.range U.ι := by rwa [Scheme.Opens.range_ι]
    have hl := IsOpenImmersion.lift_fac U.ι g hr
    set l := IsOpenImmersion.lift U.ι g hr
    have e2 : h ≫ l = 𝟙 _ := by rw [← cancel_mono U.ι, Category.assoc, hl, e1, Category.id_comp]
    have e3 : l ≫ h = 𝟙 _ := by
      refine IsHom.unique (φ := AlgHom.id o Ω) ?_ (isHom_id _)
      have : (ofAffine o Ω R).pt ≫ l = p := by rw [← cancel_mono U.ι, Category.assoc, hl, hg', hp]
      rw [IsHom, ← Category.assoc, this, e]
    haveI : IsIso h := ⟨l, e2, e3⟩
    exact IsAffine.of_isIso h
  · obtain ⟨a, rfl⟩ := mem_ringOn_univ_ofAffine.1 (mem_ringOn.2 fun z _ =>
      hg.map_mem_O (mem_ringOn.1 hx (g z) (hU ⟨z, rfl⟩)))
    exact a.2

theorem IsHom.inv_mem_O {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' φ f) {z : M'.Z} {x : Ω} (hx : x ∈ M.O (f z))
    (h0 : x ≠ 0) (hi : (φ x)⁻¹ ∈ M'.O z) : x⁻¹ ∈ M.O (f z) := by
  obtain ⟨U, a, hz, rfl⟩ := hx
  have e := hf.valF_app ⟨_, hz⟩ a
  have h1 : z ∈ M'.Z.basicOpen (f.app U a) :=
    (isUnit_valF_iff (U := f ⁻¹ᵁ U) hz _).1 ((isUnit_O_iff _).2 ⟨by simpa [e] using h0, by simpa only [e] using hi⟩)
  rw [← Scheme.preimage_basicOpen] at h1
  exact ((isUnit_O_iff _).1 ((isUnit_valF_iff hz a).2 h1)).2

theorem IsHom.div_of_div {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' φ f) {J : Type} {t : J → Ω} {i k : J} {z : M'.Z}
    (hk : M.Div t k (f z)) (h : M'.Div (fun j => φ (t j)) i z) : M.Div t i (f z) := by
  have h0 : t i / t k ≠ 0 := div_ne_zero ((map_ne_zero φ).1 h.1) hk.1
  exact (hk.div_iff_isUnit i).2 ((isUnit_O_iff _).2 ⟨h0, hf.inv_mem_O (hk.2 i) h0 (by simpa using h.2 k)⟩)

section Pairing

variable {J : Type} [Fintype J]

def pairing (φ : Ω →ₐ[o] Ω') (s : J → Ω') (v : J → Ω) : Ω' := ∑ j, φ (v j) * s j

theorem pairing_sum {I : Type} [Fintype I] (s : J → Ω') (c : I → Ω) (a : I → J → Ω) :
    pairing φ s (∑ i, c i • a i) = ∑ i, φ (c i) * pairing φ s (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [pairing, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum, _root_.mul_assoc]
  exact Finset.sum_comm

theorem pairing_div (s : J → Ω') (v : J → Ω) (c : Ω) :
    pairing φ s (fun j => v j / c) = (φ c)⁻¹ * pairing φ s v := by
  simp only [pairing, map_div₀, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem exists_pairing_eq {I : Type} [Fintype I] (s : J → Ω') {S : Subalgebra o Ω} {a : I → J → Ω} {v : J → Ω}
    (hv : v ∈ Submodule.span S (Set.range a)) :
    ∃ c : I → Ω, (∀ i, c i ∈ S) ∧ pairing φ s v = ∑ i, φ (c i) * pairing φ s (a i) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hv
  exact ⟨fun i => c i, fun i => (c i).2, pairing_sum s (fun i => (c i : Ω)) a⟩

theorem IsHom.exists_div_pairing {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' φ f) (s : J → Ω') {I K : Type} [Fintype I]
    [Fintype K] {a : I → J → Ω} {b : K → J → Ω} {z : M'.Z}
    (h : Submodule.span (M.O (f z)) (Set.range a) = Submodule.span (M.O (f z)) (Set.range b)) {i : I}
    (hi : M'.Div (fun i => pairing φ s (a i)) i z) : ∃ k, M'.Div (fun k => pairing φ s (b k)) k z := by
  have h0 : pairing φ s (a i) ≠ 0 := hi.1
  have h1 : ∀ k, pairing φ s (b k) / pairing φ s (a i) ∈ M'.O z := fun k => by
    obtain ⟨c, hc, e⟩ := exists_pairing_eq (φ := φ) s (h ▸ Submodule.subset_span ⟨k, rfl⟩ :
      b k ∈ Submodule.span (M.O (f z)) (Set.range a))
    rw [e, Finset.sum_div]
    exact sum_mem fun i' _ => by
      rw [mul_div_assoc]
      exact mul_mem (hf.map_mem_O (hc i')) (hi.2 i')
  obtain ⟨d, hd, e⟩ := exists_pairing_eq (φ := φ) s (h ▸ Submodule.subset_span ⟨i, rfl⟩ :
      a i ∈ Submodule.span (M.O (f z)) (Set.range b))
  have e1 : ∑ k, (⟨φ (d k), hf.map_mem_O (hd k)⟩ * ⟨_, h1 k⟩ : M'.O z) = 1 := by
    refine Subtype.ext ?_
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, OneMemClass.coe_one, ← mul_div_assoc,
      ← Finset.sum_div, ← e, div_self h0]
  obtain ⟨k, -, hk⟩ := IsLocalRing.exists_of_isUnit_sum (e1 ▸ isUnit_one)
  obtain ⟨hk0, hk1⟩ := (isUnit_O_iff _).1 (isUnit_of_mul_isUnit_right hk)
  have hk2 : pairing φ s (b k) ≠ 0 := fun h => hk0 (by simp [h])
  refine ⟨k, hk2, fun k' => ?_⟩
  have := mul_mem (h1 k') hk1
  convert this using 1
  field_simp

theorem Lat.exists_eq_sum_pairing [DecidableEq J] (EE : M.Lat J) (s : J → Ω') {I : Type} [Fintype I]
    {a : I → J → Ω} {z : M.Z} (h : EE.E z = Submodule.span (M.O z) (Set.range a)) (j : J) :
    ∃ c : I → Ω, s j = ∑ i, φ (c i) * pairing φ s (a i) := by
  obtain ⟨U, b, hz, hb, H⟩ := EE.loc z
  have h1 : ∀ l, b l ∈ Submodule.span (M.O z) (Set.range a) := fun l =>
    h ▸ H z hz ▸ Submodule.subset_span ⟨l, rfl⟩
  choose c _ hc using fun l => exists_pairing_eq (φ := φ) s (h1 l)
  have e : (Pi.single j 1 : J → Ω) = ∑ l, b⁻¹ j l • b l := by
    ext j'
    have := congrFun (congrFun (Matrix.nonsing_inv_mul b (isUnit_iff_ne_zero.2 hb)) j) j'
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simp [Finset.sum_apply, this, Pi.single_apply, eq_comm]
  have e2 : pairing φ s (Pi.single j 1) = s j := by
    simp [pairing, Pi.single_apply, apply_ite φ]
  refine ⟨fun i => ∑ l, b⁻¹ j l * c l i, ?_⟩
  rw [← e2, e]
  refine (pairing_sum s (fun l => b⁻¹ j l) fun l => b l).trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hc, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, _root_.mul_assoc]
  exact Finset.sum_comm

theorem Lat.eq_top_of_pairing_mem [DecidableEq J] (EE : M.Lat J) {s : J → Ω'}
    (hs : Subfield.closure (Set.range φ ∪ {x | ∃ i j, x = s j / s i}) = ⊤) {I : Type} [Fintype I]
    {a : I → J → Ω} {z : M.Z} (h : EE.E z = Submodule.span (M.O z) (Set.range a)) {g : Ω'} (hg : g ≠ 0)
    {K : Subfield Ω'} (h1 : ∀ x, φ x ∈ K) (h2 : ∀ i, pairing φ s (a i) / g ∈ K) : K = ⊤ := by
  have h3 : ∀ j, s j / g ∈ K := fun j => by
    obtain ⟨c, e⟩ := EE.exists_eq_sum_pairing (φ := φ) s h j
    rw [e, Finset.sum_div]
    exact sum_mem fun i _ => by
      rw [mul_div_assoc]
      exact mul_mem (h1 _) (h2 i)
  refine top_unique (hs ▸ Subfield.closure_le.2 ?_)
  rintro _ (⟨x, rfl⟩ | ⟨i, j, rfl⟩)
  · exact h1 x
  · have := div_mem (h3 j) (h3 i)
    rwa [div_div_div_cancel_right₀ hg] at this

end Pairing

theorem map_mem_of_ringOn {V : M.Z.Opens} (hV : IsAffineOpen V) (hne : (V : Set M.Z).Nonempty) {K : Subfield Ω'}
    (h : ∀ x ∈ M.ringOn V, φ x ∈ K) (x : Ω) : φ x ∈ K := by
  obtain ⟨a, b, -, rfl⟩ := exists_eq_div hV hne x
  rw [map_div₀]
  exact div_mem (h _ ((mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩)) (h _ ((mem_ringOn_iff_exists hne).2 ⟨b, rfl⟩))

theorem div_comp_iff {I K : Type} {t : K → Ω} {e : I → K} (he : Function.Surjective e) {i : I} {z : M.Z} :
    M.Div (fun i => t (e i)) i z ↔ M.Div t (e i) z :=
  and_congr_right fun _ => (he.forall (p := fun k => t k / t (e i) ∈ M.O z)).symm

theorem div_mul_prod_iff {I K : Type} {t : I → Ω} {u : K → Ω} {i : I} {k : K} {z : M.Z} :
    M.Div (fun q : I × K => t q.1 * u q.2) (i, k) z ↔ M.Div t i z ∧ M.Div u k z := by
  constructor
  · rintro ⟨h0, h⟩
    have hi : t i ≠ 0 := left_ne_zero_of_mul h0
    have hk : u k ≠ 0 := right_ne_zero_of_mul h0
    exact ⟨⟨hi, fun i' => by simpa [mul_div_mul_right _ _ hk] using h (i', k)⟩,
      ⟨hk, fun k' => by simpa [mul_div_mul_left _ _ hi] using h (i, k')⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨mul_ne_zero h1.1 h2.1, fun q => by simpa [mul_div_mul_comm] using mul_mem (h1.2 q.1) (h2.2 q.2)⟩

end GlobalTheory.ZH.RatModel
end
end
