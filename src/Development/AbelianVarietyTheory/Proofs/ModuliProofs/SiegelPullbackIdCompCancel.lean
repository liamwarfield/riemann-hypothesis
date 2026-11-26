module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowerSectionOfChartFunctions
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ModuliNonemptyOfObj
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SiegelPullComp

theorem iso_pull {X Y : Scheme.{0}} {L M : LB X} (d : Y ⟶ X) (h : LBIso L M) : LBIso (L.pull d) (M.pull d) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨LB.linCombIso w (fun _ : PUnit => d) (fun _ => 1), DVR.linCombIso_isGen w hw _ _⟩

private theorem gm_res_eq_gm {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) {U V : X.Opens} (h : V ≤ U) (hy : f y ∈ V)
    (x : Γ(X, U)ˣ) : gm f y V (res h x) = gm f y U x := by
  unfold gm
  rw [dite_eq_left hy, dite_eq_left (h hy)]
  simp only [MonoidHom.comp_apply]
  rw [pullU_res₂]
  ext
  simp [res]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

private theorem lbIso_of_chart_le_of_gm_transition_eq {Y : Scheme.{0}} {A' B : LB Y} (hB : LBIso B B) (idx : A'.ι → B.ι)
    (le : ∀ i, A'.U i ≤ B.U (idx i))
    (hg : ∀ (y : Y) i j, y ∈ A'.U i → y ∈ A'.U j →
      gm (𝟙 Y) y (A'.U i ⊓ A'.U j) (A'.g i j) = gm (𝟙 Y) y (B.U (idx i) ⊓ B.U (idx j)) (B.g (idx i) (idx j))) :
    LBIso A' B := by
  obtain ⟨w, hw⟩ := hB
  have cp : ChartPull (B.div A') (B.div B) (𝟙 Y) :=
    { idx := fun p => (p.1, idx p.2)
      le := fun p y hy => ⟨hy.1, le p.2 hy.2⟩
      g := by
        rintro y ⟨p1, p2⟩ ⟨q1, q2⟩ hp hq
        have hp' : y ∈ B.U p1 ⊓ A'.U p2 := hp
        have hq' : y ∈ B.U q1 ⊓ A'.U q2 := hq
        change gm (𝟙 Y) y ((B.U p1 ⊓ A'.U p2) ⊓ (B.U q1 ⊓ A'.U q2)) (res _ (B.g p1 q1) * (res _ (A'.g p2 q2))⁻¹) =
          gm (𝟙 Y) y ((B.U p1 ⊓ B.U (idx p2)) ⊓ (B.U q1 ⊓ B.U (idx q2)))
            (res _ (B.g p1 q1) * (res _ (B.g (idx p2) (idx q2)))⁻¹)
        rw [map_mul, map_mul, map_inv, map_inv, gm_res_eq_gm (𝟙 Y) y, gm_res_eq_gm (𝟙 Y) y, gm_res_eq_gm (𝟙 Y) y,
          gm_res_eq_gm (𝟙 Y) y, hg y p2 q2 hp'.2 hq'.2]
        all_goals first
          | exact ⟨hp', hq'⟩
          | exact ⟨⟨hp'.1, le _ hp'.2⟩, ⟨hq'.1, le _ hq'.2⟩⟩ }
  obtain ⟨t, ht⟩ := gen_chartPull cp w hw
  exact ⟨t, ht⟩

theorem iso_pull_pull {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (d : Z ⟶ Y) :
    LBIso ((L.pull a).pull d) (L.pull (d ≫ a)) := by
  have base : LBIso (L.pull (d ≫ a)) (L.pull (d ≫ a)) :=
    exists_iso_linComb hL (fun _ : PUnit => d ≫ a) (fun _ => 1) (fun _ _ _ => rfl)
  have le : ∀ K : ((L.pull a).pull d).ι, ((L.pull a).pull d).U K ≤ (L.pull (d ≫ a)).U (fun _ => K ⟨⟩ ⟨⟩) :=
    fun K y hy => by
      have h1 : d y ∈ (L.pull a).U (K ⟨⟩) := mem_pull.1 hy
      have h2 : a (d y) ∈ L.U (K ⟨⟩ ⟨⟩) := mem_pull.1 h1
      exact mem_pull.2 h2
  refine lbIso_of_chart_le_of_gm_transition_eq base (fun K _ => K ⟨⟩ ⟨⟩) le ?_
  intro y K K' hK hK'
  rw [gm_pull_g (L.pull a) d (𝟙 Z) y K K' hK hK', gm_pull_g L (d ≫ a) (𝟙 Z) y _ _ (le K hK) (le K' hK')]
  simp only [Category.id_comp]
  rw [gm_pull_g L a d y (K ⟨⟩) (K' ⟨⟩) (mem_pull.1 hK) (mem_pull.1 hK')]

theorem iso_pull_id {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L (L.pull (𝟙 X)) := by
  have base : LBIso (L.pull (𝟙 X)) (L.pull (𝟙 X)) :=
    exists_iso_linComb hL (fun _ : PUnit => 𝟙 X) (fun _ => 1) (fun _ _ _ => rfl)
  have le : ∀ i : L.ι, L.U i ≤ (L.pull (𝟙 X)).U (fun _ => i) := fun i y hy => mem_pull.2 hy
  refine lbIso_of_chart_le_of_gm_transition_eq base (fun i _ => i) le ?_
  intro y i j hi hj
  rw [gm_pull_g L (𝟙 X) (𝟙 X) y _ _ (le i hi) (le j hj), Category.id_comp]

variable {h k : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}

theorem pb_id (c : SiegPre h k ζ s) : SiegPB c c (𝟙 _) := by
  unfold SiegPB
  have : IsMonHom (Iso.refl c.A).hom := by
    show IsMonHom (𝟙 c.A)
    infer_instance
  refine ⟨𝟙 _, 𝟙 _, ?_, ?_, iso_pull_id c.isLB, fun a => by simp⟩
  · exact (isGrpPullback_of_iso (Iso.refl c.A)).congr rfl rfl
  · unfold Geo.Tor.IsSquare
    simp

theorem pb_comp {c : SiegPre h k ζ s} {c' : SiegPre h k ζ' s'} {c'' : SiegPre h k ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} (m : SiegPB c' c f) (m' : SiegPB c'' c' f') : SiegPB c'' c (f' ≫ f) := by
  unfold SiegPB at m m' ⊢
  obtain ⟨φ, φ₂, hg, ⟨hs1, hs2⟩, hl, hlev⟩ := m
  obtain ⟨ψ, ψ₂, hg', ⟨ht1, ht2⟩, hl', hlev'⟩ := m'
  refine ⟨ψ ≫ φ, ψ₂ ≫ φ₂, hg'.comp hg, ?_, ?_, fun a => ?_⟩
  · unfold Geo.Tor.IsSquare
    constructor
    · rw [Category.assoc, hs1, ← Category.assoc, ht1, Category.assoc]
    · rw [Category.assoc, hs2, ← Category.assoc, ht2, Category.assoc]
  · exact LBIso.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB c.isLB _) hl'
      (LBIso.trans (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _)
        (iso_pull ψ₂ hl) (iso_pull_pull c.isLB φ₂ ψ₂))
  · rw [← Category.assoc, hlev' a, Category.assoc, hlev a, ← Category.assoc]

private theorem hom_ext_tensor_left_of_fst_snd_eq {T : Scheme.{0}} {A : Over T} {X : Scheme.{0}} {a b : X ⟶ (A ⊗ A).left}
    (h₁ : a ≫ (fst A A).left = b ≫ (fst A A).left) (h₂ : a ≫ (snd A A).left = b ≫ (snd A A).left) : a = b := by
  have hw : b ≫ (A ⊗ A).hom = a ≫ (A ⊗ A).hom := by
    rw [← Over.w (fst A A), ← Category.assoc, ← Category.assoc, h₁]
  have key : (Over.homMk a rfl : Over.mk (a ≫ (A ⊗ A).hom) ⟶ A ⊗ A) = Over.homMk b hw := by
    apply CartesianMonoidalCategory.hom_ext
    · ext
      simpa only [Over.comp_left, Over.homMk_left] using h₁
    · ext
      simpa only [Over.comp_left, Over.homMk_left] using h₂
  exact congrArg CommaMorphism.left key

theorem pb_cancel {c : SiegPre h k ζ s} {c' : SiegPre h k ζ' s'} {c'' : SiegPre h k ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} (m : SiegPB c' c f) (n : SiegPB c'' c (f' ≫ f)) : SiegPB c'' c' f' := by
  unfold SiegPB at m n ⊢
  obtain ⟨φ, φ₂, hg, ⟨hs1, hs2⟩, hl, hlev⟩ := m
  obtain ⟨ψ, ψ₂, hn, ⟨ht1, ht2⟩, hln, hlevn⟩ := n
  have hw : ψ ≫ c.A.hom = (c''.A.hom ≫ f') ≫ f := by rw [hn.1.w, Category.assoc]
  obtain ⟨χ, hχ1, hχ2⟩ : ∃ χ : c''.A.left ⟶ c'.A.left, χ ≫ φ = ψ ∧ χ ≫ c'.A.hom = c''.A.hom ≫ f' :=
    ⟨hg.1.lift ψ (c''.A.hom ≫ f') hw, hg.1.lift_fst _ _ _, hg.1.lift_snd _ _ _⟩
  have hgc : IsGrpPullback c''.A c'.A f' χ := IsGrpPullback.cancel hg (hn.congr rfl hχ1.symm) hχ2
  have q1 : ((fst c''.A c''.A).left ≫ χ) ≫ c'.A.hom = (Over.mk ((c''.A ⊗ c''.A).hom ≫ f')).hom := by
    rw [Category.assoc, hχ2, ← Category.assoc, Over.w (fst c''.A c''.A)]
    rfl
  have q2 : ((snd c''.A c''.A).left ≫ χ) ≫ c'.A.hom = (Over.mk ((c''.A ⊗ c''.A).hom ≫ f')).hom := by
    rw [Category.assoc, hχ2, ← Category.assoc, Over.w (snd c''.A c''.A)]
    rfl
  obtain ⟨χ₂, hq1, hq2⟩ : ∃ χ₂ : (c''.A ⊗ c''.A).left ⟶ (c'.A ⊗ c'.A).left,
      χ₂ ≫ (fst c'.A c'.A).left = (fst c''.A c''.A).left ≫ χ ∧
      χ₂ ≫ (snd c'.A c'.A).left = (snd c''.A c''.A).left ≫ χ := by
    refine ⟨(lift (Over.homMk _ q1 : Over.mk ((c''.A ⊗ c''.A).hom ≫ f') ⟶ c'.A) (Over.homMk _ q2)).left, ?_, ?_⟩
    · rw [← Over.comp_left, lift_fst]
      rfl
    · rw [← Over.comp_left, lift_snd]
      rfl
  have e : χ₂ ≫ φ₂ = ψ₂ := by
    apply hom_ext_tensor_left_of_fst_snd_eq
    · rw [Category.assoc, hs1, ← Category.assoc, hq1, Category.assoc, hχ1, ht1]
    · rw [Category.assoc, hs2, ← Category.assoc, hq2, Category.assoc, hχ1, ht2]
  refine ⟨χ, χ₂, hgc, ⟨hq1, hq2⟩, ?_, fun a => ?_⟩
  · rw [← e] at hln
    exact LBIso.trans c''.isLB (pull_isLB c.isLB _) (pull_isLB c'.isLB _) hln
      (LBIso.symm (LBIso.trans (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _)
        (iso_pull χ₂ hl) (iso_pull_pull c.isLB φ₂ χ₂)))
  · apply hg.1.hom_ext
    · simp only [Category.assoc, hχ1, hlevn, hlev]
    · simp only [Category.assoc, hχ2]
      rw [reassoc_of% (Over.w (c''.lev a)), Over.w (c'.lev a)]
      simp

theorem id_comp_cancel : ∀ (h k : ℕ) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (ζ : B) (ζ' : B') (ζ'' : B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (c : SiegPre h k ζ s) (c' : SiegPre h k ζ' s') (c'' : SiegPre h k ζ'' s'') (f : S' ⟶ S) (f' : S'' ⟶ S'), SiegPB c c (𝟙 _) ∧ (SiegPB c' c f → (SiegPB c'' c' f' ↔ SiegPB c'' c (f' ≫ f))) := by
  intro h k B B' B'' _ _ _ ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f'
  exact ⟨pb_id c, fun m => ⟨fun m' => pb_comp m m', fun n => pb_cancel m n⟩⟩

end GlobalTheory.SiegelPullComp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.siegelPullback_id_comp_cancel : ∀ (h k : ℕ) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (ζ : B) (ζ' : B') (ζ'' : B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (c : SiegPre h k ζ s) (c' : SiegPre h k ζ' s') (c'' : SiegPre h k ζ'' s'') (f : S' ⟶ S) (f' : S'' ⟶ S'), SiegPB c c (𝟙 _) ∧ (SiegPB c' c f → (SiegPB c'' c' f' ↔ SiegPB c'' c (f' ≫ f))) := by
  first | exact @GlobalTheory.SiegelPullComp.id_comp_cancel | exact GlobalTheory.SiegelPullComp.id_comp_cancel | (intros; apply GlobalTheory.SiegelPullComp.id_comp_cancel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasTh
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasTh
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaCoset

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ThetaCoord GlobalTheory.CommPairing GlobalTheory.GlobalLift GlobalTheory.VVRank

theorem exists_eq_smul {N n : ℕ} (hN : N ≠ 0) (hn : n ∣ N) {c : ZMod (N ^ 2)} (hc : n • c = 0) :
    ∃ d : ZMod (N ^ 2), N • (N / n) • d = c := by
  obtain ⟨m, rfl⟩ := hn
  have h₀ : 0 < n := Nat.pos_of_ne_zero (left_ne_zero_of_mul hN)
  have : NeZero ((n * m) ^ 2) := ⟨pow_ne_zero _ hN⟩
  obtain ⟨e, rfl⟩ := ZMod.natCast_zmod_surjective c
  rw [nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff,
    show (n * m) ^ 2 = n * (n * m * m) by ring] at hc
  obtain ⟨d, rfl⟩ := Nat.dvd_of_mul_dvd_mul_left h₀ hc
  refine ⟨d, ?_⟩
  rw [Nat.mul_div_cancel_left _ h₀, nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

theorem exists_label {G : Type} [CommGroup G] {r N n : ℕ} (hN : N ≠ 0) (hn : n ∣ N) (p : Fin r → G)
    (hp : ∀ i, p i ^ (N ^ 2) = 1)
    (hb : ∀ y : G, y ^ (N ^ 2) = 1 → ∃! c : Fin r → ZMod (N ^ 2), ∏ i, p i ^ (c i).val = y)
    (a : Fin r → ZMod (N ^ 2)) {z : G} (hz : z ^ n = 1) :
    ∃ c : Fin r → ZMod (N ^ 2), (∏ i, p i ^ ((a + (N / n) • c) i).val) ^ N = (∏ i, p i ^ (a i).val) ^ N * z := by
  have : NeZero (N ^ 2) := ⟨pow_ne_zero _ hN⟩
  let f : (Fin r → ZMod (N ^ 2)) → G := fun c => ∏ i, p i ^ (c i).val
  have f₀ : f 0 = 1 := Finset.prod_eq_one fun i _ => by rw [Pi.zero_apply, ZMod.val_zero, pow_zero]
  have fa : ∀ c d, f (c + d) = f c * f d := fun c d => by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hp i), pow_add]
  have fs : ∀ (m : ℕ) c, f (m • c) = f c ^ m := fun m c => by
    induction m with
    | zero => rw [zero_smul, f₀, pow_zero]
    | succ m ih => rw [succ_nsmul, fa, ih, pow_succ]
  obtain ⟨c₀, hc₀, -⟩ := hb z (by
    obtain ⟨m, hm⟩ := hn.trans (dvd_pow_self N two_ne_zero)
    rw [hm, pow_mul, hz, one_pow])
  replace hc₀ : f c₀ = z := hc₀
  have h₁ : n • c₀ = 0 := (hb 1 (one_pow _)).unique ((fs n c₀).trans (by rw [hc₀, hz])) f₀
  choose d hd using fun i => exists_eq_smul hN hn (congrFun h₁ i)
  refine ⟨d, ?_⟩
  change f _ ^ N = f a ^ N * z
  rw [fa, mul_pow, ← fs N (_ • d), ← hc₀]
  exact congrArg (fun c => _ * f c) (funext hd)

variable {S : Scheme.{0}}

theorem ne_zero_of_isGenSec (hB : SecBaseChangeAnySt) (P : PolAV S) {K : Type} [Field K] (x : Sp K ⟶ S)
    {th : LB.Sec (LPow P.A P.L 1 (Over.mk x))} (H : IsGenSec P.A P.L 1 th) : SecM.ofSec P.A th ≠ 0 := by
  obtain ⟨V, hV, b, hb⟩ := hB S P 1 le_rfl (x (IsLocalRing.closedPoint K))
  obtain ⟨t, rfl⟩ : ∃ t : Sp K ⟶ (overRes (T := baseOver S) V).left, t ≫ (overRes (T := baseOver S) V).hom = x :=
    ⟨IsOpenImmersion.lift V.ι x (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      rwa [Subsingleton.elim p (IsLocalRing.closedPoint K)]),
      (congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _)⟩
  obtain ⟨hli, -⟩ := hb K t (fun i => pullS P.A _ (homAt t) (b i)) fun i => isPullSec_pullS _ _ _ _
  have : Nontrivial Γ((baseAt t).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have i : Fin (1 ^ P.g) := ⟨0, by rw [one_pow]; exact one_pos⟩
  intro h₀
  obtain ⟨r, hr⟩ := H (pullS P.A _ (homAt t) (b i))
  have e : SecM.ofSec P.A (pullS P.A _ (homAt t) (b i)) = r • SecM.ofSec P.A th := Subtype.ext (funext hr)
  rw [h₀, smul_zero] at e
  exact hli.ne_zero i e

theorem exists_ne_zero_over (h₁ : Laws) (h₂ : Laws2) (P : PolAV S) {K : Type} [Field K] [IsAlgClosed K]
    (x : Sp K ⟶ S) {k n : ℕ} (hn : 2 ≤ n) (hK : (n : K) ≠ 0) {I : Type} {y : I → (Over.mk x ⟶ P.A)}
    {v : I → Γ((Over.mk x).left, ⊤)} (H : IsThetaPtOver P k y v) (a : Over.mk x ⟶ P.A) :
    ∃ z : Over.mk x ⟶ P.A, z ^ n = 1 ∧ ∀ i, y i ^ k = a * z → v i ≠ 0 := by
  have hL := P.isLB
  obtain ⟨th, s₁, α, τ, U, s₂, w, u, hth, hα, hτ, hs₁, hU, hs₂, hw, hv⟩ := H
  obtain ⟨z, hz, hu⟩ := UT.ExactTerm.exists_good_point h₁.goodPt h₁.polBaseChange P x hn hK th
    (ne_zero_of_isGenSec h₂.secBaseChangeAny P x hth) a
  refine ⟨z, hz, fun i hi h₀ => ?_⟩
  let p : (Over.mk x).left := IsLocalRing.closedPoint K
  choose J hJ using fun χ : (Over.mk x).left ⟶ P.A.left => exists_chart hL (χ p)
  replace hJ : Good P.L p J := hJ
  have b₁ := sv_act (hU i).pt_eq (hs₂ i) (𝟙 _) hJ 1
  have b₂ := sv_mulPull hs₁ (𝟙 _) hJ (y i)
  have b₃ := sv_of_isValueAt (hw i) (𝟙 _) hJ
  rw [Category.id_comp, _root_.mul_one] at b₁
  rw [Category.id_comp] at b₃
  rw [hv, Units.mul_right_eq_zero] at h₀
  rw [b₃, b₂, hi, h₀, UT.ExactTerm.gs_zero' _ _ ⊤ trivial, MulZeroClass.zero_mul] at b₁
  exact ((Units.isUnit _).mul ((Units.isUnit _).mul (hu p J hJ))).ne_zero b₁.symm

theorem coset_bot (h₁ : Laws) (h₂ : Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {s : S ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) {n : ℕ} (hn : 2 ≤ n) (hd : n ∣ N') {K : Type} [Field K] [IsAlgClosed K]
    (x : Sp K ⟶ S) {v : Ix g (N' ^ 2) → K} (H : t.HasTh x v) (a : Ix g (N' ^ 2)) :
    ∃ c, v (a + (N' / n) • c) ≠ 0 := by
  have := t.ab.comm
  let π : Over.mk x ⟶ baseOver S := Over.homMk x (by simp)
  have hK : (n : K) ≠ 0 := by
    have := H.2.1.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
    rw [map_natCast] at this
    exact (isUnit_of_dvd_unit (Nat.cast_dvd_cast hd) this).ne_zero
  have : Subsingleton (Over.mk x).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (Over.mk x).left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  obtain ⟨z, hz, hv⟩ := exists_ne_zero_over h₁ h₂ t.pol x hn hK (isThetaPtOver_of_subsingleton t.pol H)
    ((π ≫ t.lab a) ^ N')
  have e : ∀ c, π ≫ t.lab c = ∏ i, (π ≫ t.pt i) ^ (c i).val := fun c => by
    rw [TObj.lab, VVRank.comp_linComb, linComb, List.prod_ofFn]
  obtain ⟨c, hc⟩ := exists_label (G := Over.mk x ⟶ t.A) H.1.pos.ne' hd (fun i => π ≫ t.pt i)
    (fun i => by rw [← MonObj.comp_pow, t.torsion, MonObj.comp_one])
    (fun y hy => by simpa only [linComb, List.prod_ofFn] using t.bij K x y hy) a hz
  rw [← e, ← e] at hc
  refine ⟨c, fun h₀ => hv _ hc ?_⟩
  rw [h₀, map_zero]

end GlobalTheory.ThetaCoset

namespace GlobalTheory

theorem coset_of_hasTh : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (n : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R) (q : Ideal R), 2 ≤ n → n ∣ N' → t.HasTh x v → q.IsPrime → Coset n N' v q := by
  intro h₁ h₂ o _ g N' J b S s t n R _ x v q hn hd H hq a
  let φ : R →+* AlgebraicClosure q.ResidueField :=
    (algebraMap q.ResidueField (AlgebraicClosure q.ResidueField)).comp (algebraMap R q.ResidueField)
  obtain ⟨c, hc⟩ := ThetaCoset.coset_bot h₁ h₂ t hn hd _ (T.hasThetaConstants_ring_baseChange h₂ o g N' J b S s t R _ φ x v H) a
  refine ⟨c, fun hm => hc ?_⟩
  rw [RingHom.comp_apply, Ideal.algebraMap_residueField_eq_zero.2 hm, map_zero]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasThStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaCosetNonvanishing_of_hasTh : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (n : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R) (q : Ideal R), 2 ≤ n → n ∣ N' → t.HasTh x v → q.IsPrime → Coset n N' v q := by
  first | exact @GlobalTheory.coset_of_hasTh | exact GlobalTheory.coset_of_hasTh | (intros; apply GlobalTheory.coset_of_hasTh <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnit
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaUniq

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ThetaCoord GlobalTheory.CommPairing GlobalTheory.GlobalLift GlobalTheory.VVRank

theorem exists_unit_of_local {R I : Type} [CommRing R] {v v' : I → R} (hv : Ideal.span (Set.range v) = ⊤)
    (h : ∀ (q : Ideal R) [q.IsMaximal], ∃ u : (Localization.AtPrime q)ˣ, ∀ a,
      algebraMap R (Localization.AtPrime q) (v' a) = u * algebraMap R (Localization.AtPrime q) (v a)) :
    ∃ u : Rˣ, ∀ a, v' a = u * v a := by
  obtain ⟨c, hc⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.1 ((Ideal.eq_top_iff_one _).1 hv)
  have key : ∀ (q : Ideal R) [q.IsMaximal], ∃ u : (Localization.AtPrime q)ˣ,
      algebraMap R (Localization.AtPrime q) (c.sum fun i a => a * v' i) = u ∧ ∀ a,
      algebraMap R (Localization.AtPrime q) (v' a) = u * algebraMap R (Localization.AtPrime q) (v a) := fun q _ => by
    obtain ⟨u, hu⟩ := h q
    refine ⟨u, ?_, hu⟩
    have e := congrArg (algebraMap R (Localization.AtPrime q)) hc
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finsupp.sum, map_sum, map_mul, map_one] at e ⊢
    simp only [hu, mul_left_comm _ (u : Localization.AtPrime q)]
    rw [← Finset.mul_sum, e, _root_.mul_one]
  have hu : IsUnit (c.sum fun i a => a * v' i) := by
    by_contra hn
    obtain ⟨q, hq, hm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hn)
    obtain ⟨u, e, -⟩ := key q
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q) q _).1 (e ▸ u.isUnit) hm
  refine ⟨hu.unit, fun a => Module.eq_of_localization_maximal (R := R) (fun q _ => Localization.AtPrime q)
    (fun q _ => Algebra.linearMap R (Localization.AtPrime q)) _ _ fun q _ => ?_⟩
  obtain ⟨u, e, e'⟩ := key q
  rw [Algebra.linearMap_apply, Algebra.linearMap_apply, map_mul, IsUnit.unit_spec, e, e']

theorem exists_ratio_base {X Y S₀ : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    {u u' : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ c : Γ(S₀, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      val u r z J = val u' r z J * gm (r ≫ p) z ⊤ c := by
  obtain ⟨c, hc⟩ := SymLiftOdd.exists_const hL p e he hp (fun U _ h => (Fintype.prod_sum_type _).trans (by
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel]))
    (DVR.mulGen_isGen L _ _ _ _ u (LB.invGen L _ _ u') hu (DVR.invGen_isGen _ _ _ _ hu'))
  refine ⟨c, fun Z r z J hJ => ?_⟩
  rw [← hc Z r z J hJ, val_mul hJ, val_inv, mul_comm, inv_mul_cancel_right]

variable {S : Scheme.{0}} {T : Over S}

theorem exists_unit_of_isGenSec_local {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} [IsLocalRing Γ(T.left, ⊤)]
    {th th' : LB.Sec (LPow A L k T)} (H : IsGenSec A L k th) (H' : IsGenSec A L k th') :
    ∃ u : Γ(T.left, ⊤)ˣ, SecM.ofSec A th = (u : Γ(T.left, ⊤)) • SecM.ofSec A th' := by
  obtain ⟨r, hr⟩ := H' th
  obtain ⟨r', hr'⟩ := H th'
  have e : SecM.ofSec A th = r • SecM.ofSec A th' := Subtype.ext (funext hr)
  have e' : SecM.ofSec A th' = r' • SecM.ofSec A th := Subtype.ext (funext hr')
  by_cases hu : IsUnit r
  · exact ⟨hu.unit, e⟩
  have h₁ : IsUnit (1 - r * r') :=
    (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_left fun h => hu (isUnit_of_mul_isUnit_left h)
  have h₂ : SecM.ofSec A th = 0 := h₁.smul_eq_zero.1 (by rw [sub_smul, one_smul, mul_smul, ← e', ← e, sub_self])
  exact ⟨1, by rw [e', h₂, smul_zero, smul_zero]⟩

theorem exists_unit_over (hG : GlobalFnsSt) (P : PolAV S) [IsLocalRing Γ(T.left, ⊤)] {k : ℕ} (hk : Odd k) {I : Type}
    {x : I → (T ⟶ P.A)} {v v' : I → Γ(T.left, ⊤)} (H : IsThetaPtOver P k x v) (H' : IsThetaPtOver P k x v') :
    ∃ u : Γ(T.left, ⊤)ˣ, ∀ i, v' i = u * v i := by
  have hL := P.isLB
  obtain ⟨th, s₁, α, τ, U, s₂, w, u, hth, hα, hτ, hs₁, hU, hs₂, hw, hv⟩ := H
  obtain ⟨th', s₁', α', τ', U', s₂', w', u', hth', hα', hτ', hs₁', hU', hs₂', hw', hv'⟩ := H'
  obtain ⟨ρ, hρ⟩ := exists_unit_of_isGenSec_local hth' hth
  obtain ⟨c, hc⟩ := exists_ratio_base hL (fst T P.A).left (lift (𝟙 T) (1 : T ⟶ P.A)).left
    (by rw [← Over.comp_left, lift_fst]; rfl) (SymLiftOdd.surj_fst hG P.isAb T) hα' hα
  obtain ⟨d, hd⟩ := exists_ratio_base hL (𝟙 T.left) (𝟙 T.left) (Category.comp_id _) (fun a => ⟨a, rfl⟩) hτ hτ'
  have key : ∀ i, w' i = (ρ * c * d : Γ(T.left, ⊤)ˣ) * w i := fun i => fn_ext fun z _ => by
    choose J hJ using fun χ : T.left ⟶ P.A.left => exists_chart hL (χ z)
    replace hJ : Good P.L z J := hJ
    have a₀ : tval (U' i) (lift (𝟙 T) (1 : T ⟶ P.A)).left z J = tval (U i) (lift (𝟙 T) (1 : T ⟶ P.A)).left z J :=
      val_corr hJ (SymLiftOdd.symLift_unique hG P.isAb hL hk.pow _ _ (hU' i) (hU i)) _
    have a₁ : bval (b := 1) α' (lift (𝟙 T) (x i)).left z J =
        bval (b := 1) α (lift (𝟙 T) (x i)).left z J * gm (𝟙 T.left) z ⊤ c := by
      have := hc _ (lift (𝟙 T) (x i)).left z J hJ
      rw [lift_fst_left] at this
      exact this
    have a₂ := hd _ (𝟙 _) z J hJ
    have a₃ : sv P.A th' (lift (𝟙 T) (x i ^ k)).left z J =
        gs (𝟙 T.left) z ⊤ ρ * sv P.A th (lift (𝟙 T) (x i ^ k)).left z J := by
      have := ThetaAct.sv_smul (ρ : Γ(T.left, ⊤)) (SecM.ofSec P.A th) (lift (𝟙 T) (x i ^ k)).left z hJ
      rw [← hρ, lift_fst_left] at this
      exact this
    have b₁ := sv_act (hU i).pt_eq (hs₂ i) (𝟙 T) hJ 1
    have b₂ := sv_mulPull hs₁ (𝟙 T) hJ (x i)
    have b₃ := sv_of_isValueAt (hw i) (𝟙 T) hJ
    have c₁ := sv_act (hU' i).pt_eq (hs₂' i) (𝟙 T) hJ 1
    have c₂ := sv_mulPull hs₁' (𝟙 T) hJ (x i)
    have c₃ := sv_of_isValueAt (hw' i) (𝟙 T) hJ
    rw [Category.id_comp, _root_.mul_one] at b₁ c₁
    rw [Category.id_comp] at b₃ c₃ a₂
    rw [b₃, b₂] at b₁
    rw [c₃, c₂, a₀, a₁, a₃] at c₁
    simp only [Over.id_left] at b₁ c₁
    rw [a₂] at b₁
    refine (Units.mul_left_inj (val τ' (𝟙 T.left) z J)).1 ?_
    rw [c₁, gs_mul _ _ ⊤ trivial, gs_unit _ _ ⊤ trivial, gs_unit _ _ ⊤ trivial, map_mul, map_mul]
    simp only [Units.val_mul] at b₁ ⊢
    linear_combination (-(gm (𝟙 T.left) z ⊤ ρ).val * (gm (𝟙 T.left) z ⊤ c).val) * b₁
  refine ⟨u' * (ρ * c * d) * u⁻¹, fun i => ?_⟩
  rw [hv', hv, key, Units.val_mul _ u⁻¹, _root_.mul_assoc _ _ (u * w i), Units.inv_mul_cancel_left, Units.val_mul u',
    _root_.mul_assoc (u' : Γ(T.left, ⊤))]

theorem isThetaPtOver_of_local (P : PolAV S) {R : Type} [CommRing R] [IsLocalRing R] (y : Sp R ⟶ S) {n : ℕ} {I : Type}
    {x : I → (Over.mk y ⟶ P.A)} {v : I → Γ((Over.mk y).left, ⊤)} (H : IsThetaPt P n x v) : IsThetaPtOver P n x v := by
  obtain ⟨V, hp, H'⟩ := H.2.2 (IsLocalRing.closedPoint R)
  obtain rfl : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).1 hp
  let h : Over.mk y ⟶ overRes (T := Over.mk y) ⊤ := Over.homMk (Sp R).topIso.inv (by
    show (Sp R).topIso.inv ≫ (⊤ : (Sp R).Opens).ι ≫ y = y
    rw [Scheme.toIso_inv_ι_assoc])
  have hh : h ≫ overResι ⊤ = 𝟙 _ := Over.OverMorphism.ext (Scheme.toIso_inv_ι (Sp R))
  have := isThetaPtOver_pull P H' h (overResι ⊤) hh
  convert this using 2 with a a
  · rw [← Category.assoc, hh, Category.id_comp]
  · have q := congrArg (fun q => q.left.appTop.hom (v a)) hh
    simp only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, Over.id_left,
      Scheme.Hom.id_appTop, CommRingCat.hom_id, RingHom.id_apply] at q
    exact q.symm

theorem exists_unit_local (hG : GlobalFnsSt) {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {s : S ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) {R : Type} [CommRing R] [IsLocalRing R] (x : Sp R ⟶ S)
    {v v' : Ix g (N' ^ 2) → R} (H : t.HasTh x v) (H' : t.HasTh x v') : ∃ u : Rˣ, ∀ a, v' a = u * v a := by
  let e : Γ(Sp R, ⊤) ≃+* R := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  haveI : IsLocalRing Γ((Over.mk x).left, ⊤) := e.symm.isLocalRing
  obtain ⟨u, hu⟩ := exists_unit_over hG t.pol H.1 (isThetaPtOver_of_local _ x H) (isThetaPtOver_of_local _ x H')
  refine ⟨Units.map e.toMonoidHom u, fun a => ?_⟩
  have q := (congrArg e (hu a)).trans (map_mul e _ _)
  exact (e.apply_symm_apply (v' a)).symm.trans (q.trans (congrArg (_ * ·) (e.apply_symm_apply (v a))))

end GlobalTheory.ThetaUniq

namespace GlobalTheory

theorem hasTh_unique_unit : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (R : Type) [CommRing R] (x : Sp R ⟶ S) (v v' : Ix g (N' ^ 2) → R), t.HasTh x v → t.HasTh x v' → Ideal.span (Set.range v) = ⊤ → ∃ u : Rˣ, ∀ a, v' a = u * v a :=
  fun h₁ h₂ o _ g N' J b S s t R _ x v v' H H' hv => ThetaUniq.exists_unit_of_local hv fun q _ =>
    ThetaUniq.exists_unit_local h₁.globalFns t _
      (T.hasThetaConstants_ring_baseChange h₂ o g N' J b S s t R _ (algebraMap R (Localization.AtPrime q)) x v H)
      (T.hasThetaConstants_ring_baseChange h₂ o g N' J b S s t R _ (algebraMap R (Localization.AtPrime q)) x v' H')

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstants_unique_up_to_unit : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (R : Type) [CommRing R] (x : Sp R ⟶ S) (v v' : Ix g (N' ^ 2) → R), t.HasTh x v → t.HasTh x v' → Ideal.span (Set.range v) = ⊤ → ∃ u : Rˣ, ∀ a, v' a = u * v a := by
  first | exact @GlobalTheory.hasTh_unique_unit | exact GlobalTheory.hasTh_unique_unit | (intros; apply GlobalTheory.hasTh_unique_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleIffOfIsReduced
noncomputable section

namespace GlobalTheory.ModelCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ObjPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

section Obj

variable {B : Type} [CommRing B] {b : Base l B} {S S' : Scheme.{0}} {s : S ⟶ Sp B} {f : S' ⟶ S}

def objOfSABMap (o : Obj D l b s) {t' : SAB H S'} (m : SABMap t' o.t f) : Obj D l b (f ≫ s) :=
  have hL : LBIso t'.PP.L (o.t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hpr := o.proper
  have hp := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally
    S S' o.t.G t'.G f m.cm.F o.t.PP.L t'.PP.L o.t.PP.isLB t'.PP.isLB
    (AbelianSchemeGerms.isAbelianScheme_of_proper o.t.G o.t.semi) m.cart hL
  { t := t'
    proper := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hpr
    ample := hp.2.1 o.ample
    ktriv := hp.2.2 o.ktriv
    eta := fun a => GlobalTheory.ObjPull.secPull m.cart (o.eta a)
    eta_add := fun a c => by rw [o.eta_add, map_mul]
    eta_ker := fun a ha => by rw [o.eta_ker a ha, map_one]
    etaA := fun a => GlobalTheory.ObjPull.secPull m.cart (o.etaA a)
    etaA_add := fun a c => by rw [o.etaA_add, map_mul]
    etaA_ker := fun a => by rw [o.etaA_ker a, map_one]
    geom := fun k _ _ x β hx => by
      obtain ⟨hdet, I, hI, hA, hM⟩ := o.geom k (x ≫ f) β (by rw [Category.assoc, hx])
      refine ⟨fun τ => ?_, tateMove (pushEquiv m.cart (Over.mk x)) (fun c g => ?_) (fun n g g' c hc => ?_) I,
        hI, fun a => ?_, fun a ha => ?_⟩
      · rw [GlobalTheory.LiePull.lieMult_pull _ S S' o.t.G t'.G f m.cm.F o.t.act t'.act m.cart m.act k x τ,
          GlobalTheory.LiePull.lieMult_pull _ S S' o.t.G t'.G f m.cm.F o.t.act t'.act m.cart m.act k x τ]
        exact hdet τ
      · apply Over.OverMorphism.ext
        show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
        rw [Category.assoc, m.act, Category.assoc]
      · exact (GlobalTheory.weilIs_grpPullback_of_comm S S' o.t.G t'.G f m.cm.F o.t.PP.L t'.PP.L o.t.PP.isLB t'.PP.isLB
          m.cart hL (Over.mk x) n g g' _ _ _ rfl rfl).2 hc
      · exact (MulEquiv.eq_symm_apply _).2 ((pushEquiv_secPull m.cart _ _).trans (hA a))
      · exact (MulEquiv.eq_symm_apply _).2 ((pushEquiv_secPull m.cart _ _).trans (hM a ha)) }

def objMapOfSABMap (o : Obj D l b s) {t' : SAB H S'} (m : SABMap t' o.t f) : ObjMap (objOfSABMap o m) o f :=
  ⟨m, fun _ => secPull_left m.cart _, fun _ => secPull_left m.cart _⟩

theorem sec_eq_secPull {t : SAB H S} {t' : SAB H S'} (m : SABMap t' t f) {e : 𝟙_ (Over S) ⟶ t.G}
    {e' : 𝟙_ (Over S') ⟶ t'.G} (h : e'.left ≫ m.φ = f ≫ e.left) : e' = GlobalTheory.ObjPull.secPull m.cart e := by
  apply Over.OverMorphism.ext
  apply m.cart.1.hom_ext
  · exact h.trans (secPull_left m.cart _).symm
  · rw [Over.w, Over.w]

end Obj

section Model

variable {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

variable (Y : Model Xo c β)

end Model

section Push

variable {X : Scheme.{0}} {G : Over X} {L : LB G.left}

end Push

end GlobalTheory.ModelCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomLift
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.SharpPull

section
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A C : Over S} {A' C' : Over S'}
  [GrpObj A] [GrpObj C] [GrpObj A'] [GrpObj C'] {φ : A'.left ⟶ A.left} {ψ : C'.left ⟶ C.left}

theorem push_inj (h : IsGrpPullback A' A f φ) {T : Over S'} {x y : T ⟶ A'}
    (e : pushHom h T x = pushHom h T y) : x = y :=
  Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))

theorem push_left (h : IsGrpPullback A' A f φ) {T : Over S'} (x : T ⟶ A') :
    (pushHom h T x).left = x.left ≫ φ := rfl

theorem push_surj (h : IsGrpPullback A' A f φ) {T : Over S'} (y : Over.mk (T.hom ≫ f) ⟶ A) :
    ∃ x : T ⟶ A', pushHom h T x = y :=
  ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem push_comp (h : IsGrpPullback A' A f φ) (h' : IsGrpPullback C' C f ψ) {p : A ⟶ C} {p' : A' ⟶ C'}
    (e : p'.left ≫ ψ = φ ≫ p.left) {T : Over S'} (x : T ⟶ A') :
    pushHom h' T (x ≫ p') = pushHom h T x ≫ p :=
  Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, e, Category.assoc])

theorem exists_lift (h : IsGrpPullback A' A f φ) (h' : IsGrpPullback C' C f ψ) (p : A ⟶ C) :
    ∃ p' : A' ⟶ C', p'.left ≫ ψ = φ ≫ p.left :=
  ⟨Over.homMk (h'.1.lift (φ ≫ p.left) A'.hom (by rw [Category.assoc, Over.w, h.1.w])) (h'.1.lift_snd _ _ _),
    h'.1.lift_fst _ _ _⟩

theorem isMonHom_lift (h : IsGrpPullback A' A f φ) (h' : IsGrpPullback C' C f ψ) {p : A ⟶ C} [IsMonHom p]
    {p' : A' ⟶ C'} (e : p'.left ≫ ψ = φ ≫ p.left) : IsMonHom p' := by
  have h1 : (1 : 𝟙_ (Over S') ⟶ A') ≫ p' = 1 := by
    apply push_inj h'
    rw [push_comp h h' e, map_one, map_one, MonObj.one_comp]
  have h2 : (fst A' A' * snd A' A') ≫ p' = (fst A' A' ≫ p') * (snd A' A' ≫ p') := by
    apply push_inj h'
    rw [push_comp h h' e, map_mul, map_mul, MonObj.mul_comp, push_comp h h' e, push_comp h h' e]
  constructor
  · simpa [Hom.one_def] using h1
  · rw [Hom.mul_def, Hom.mul_def] at h2
    have e1 : lift (fst A' A' ≫ p') (snd A' A' ≫ p') = p' ⊗ₘ p' := by ext <;> simp
    simpa [e1] using h2
end

theorem sharp_pull : ∀ (h g k : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (o : Type) [CommRing o] (b : TBase o k) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s) (t' : TObj g k J b s') (c : SiegPre h k (b.ζ : o) s), f ≫ s = s' → TMap t' t f → c.Principal → IsSharp W a bas t c → ∃ c' : SiegPre h k (b.ζ : o) s', c'.Principal ∧ IsSharp W a bas t' c' := by
  intro h g k W J a bas o _ b S S' s s' f t t' c hf ⟨φ, hφ, hL, hpt, hact⟩ hc ⟨pr, hmon, huniv, hiso, hmat, hlev⟩
  obtain ⟨⟨c', hpb⟩, hprin⟩ := GlobalTheory.T.siegelObject_pullback_exists_and_principal h k o (b.ζ : o) S S' s s' f c hf
  refine ⟨c', hprin c' hpb hc, ?_⟩
  obtain ⟨ψ, ψ₂, hψ, hsq, ⟨w, hw⟩, hlv⟩ := hpb
  choose pr' hpr using fun u => exists_lift hφ hψ (pr u)
  refine ⟨pr', fun u => ?_, fun T y => ?_, ?_, fun j u => ?_, fun i u => ?_⟩
  · have := hmon u
    exact isMonHom_lift hφ hψ (hpr u)
  · obtain ⟨x₀, hx₀, hu⟩ := huniv (Over.mk (T.hom ≫ f)) (fun u => pushHom hψ T (y u))
    obtain ⟨x, rfl⟩ := push_surj hφ x₀
    refine ⟨x, fun u => push_inj hψ ?_, fun x' hx' => push_inj hφ (hu _ fun u => ?_)⟩
    · rw [push_comp hφ hψ (hpr u), hx₀ u]
    · rw [← push_comp hφ hψ (hpr u), hx' u]
  · have hc : ∀ uv : Fin 8 × Fin 8, (lift (pr' uv.1) (pr' uv.2)).left ≫ ψ₂ = φ ≫ (lift (pr uv.1) (pr uv.2)).left := by
      intro uv
      apply pullback.hom_ext
      · show (_ ≫ ψ₂) ≫ (fst c.A c.A).left = (φ ≫ _) ≫ (fst c.A c.A).left
        rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, hpr, Category.assoc,
          ← Over.comp_left, lift_fst]
      · show (_ ≫ ψ₂) ≫ (snd c.A c.A).left = (φ ≫ _) ≫ (snd c.A c.A).left
        rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, hpr, Category.assoc,
          ← Over.comp_left, lift_snd]
    have H₁ := iso_linComb ((isGen_iff w).1 hw)
      (fun uv : Fin 8 × Fin 8 => (lift (pr' uv.1) (pr' uv.2)).left) (fun uv => W uv.1 uv.2)
    have H₂ : LBIso (t.L.pull φ) (LB.LinComb c.P
        (fun uv : Fin 8 × Fin 8 => (lift (pr' uv.1) (pr' uv.2)).left ≫ ψ₂) (fun uv => W uv.1 uv.2)) :=
      LBIso.chartPull (Geo.Tor.chartPullPull t.L φ φ rfl) (chartPullSame c.P _ _ _ φ hc) hiso
    exact LBIso.trans t'.isLB (DVR.linComb_isLB _ c.isLB _ _) (DVR.linComb_isLB _ c'.isLB _ _)
      (LBIso.trans t'.isLB (DVR.linComb_isLB _ t.isLB _ _) (DVR.linComb_isLB _ c.isLB _ _) hL H₂) H₁.symm
  · apply push_inj hψ
    have e : ∀ v, pushHom hψ t'.A (pr' v) = preHom (pushHom hφ t'.A (𝟙 _)) (pr v) := fun v =>
      (congrArg _ (Category.id_comp _).symm).trans (push_comp hφ hψ (hpr v) (𝟙 _))
    have e₂ : pushHom hφ t'.A (t'.act j) = pushHom hφ t'.A (𝟙 _) ≫ t.act j :=
      (congrArg _ (Category.id_comp _).symm).trans (push_comp hφ hφ (hact j) (𝟙 _))
    rw [push_comp hφ hψ (hpr u), e₂, Category.assoc, hmat j u]
    refine (map_list_prod (preHom (pushHom hφ t'.A (𝟙 _))) _).trans (Eq.trans ?_ (map_list_prod _ _).symm)
    rw [List.map_ofFn, List.map_ofFn]
    congr 2
    funext v
    simp only [Function.comp_apply, map_zpow, e]
  · apply hψ.1.hom_ext
    · rw [hlv, ← hlev i u, Over.comp_left, Over.comp_left, Category.assoc, hpr, ← Category.assoc, hpt, Category.assoc]
    · rw [Over.w, Over.w]; rfl

end GlobalTheory.SharpPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelBaseChangeOverring
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelBaseChangeOverring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem surjectiveOnStalks_of_dedekind_overring {O O' F : Type} [CommRing O] [IsDedekindDomain O] [Field F]
    [Algebra O F] [IsFractionRing O F] [CommRing O'] (β' : O' →+* F) (b : O →+* O') (hβ' : Function.Injective β')
    (h : ∀ x, β' (b x) = algebraMap O F x) : b.SurjectiveOnStalks := by
  intro P' hP'
  rw [RingHom.surjective_localRingHom_iff]
  intro s
  obtain ⟨x, y, hy, hs⟩ := IsFractionRing.div_surjective (A := O) (β' s)
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyF : algebraMap O F y ≠ 0 := fun e => hy0 (IsFractionRing.injective O F (by rw [e, map_zero]))
  have h1 : (1 : O') ∉ P' := P'.primeCompl.one_mem
  have key : ∀ u v : O, v * x = u * y → b v * s = b u := by
    intro u v e
    apply hβ'
    have e' := congrArg (algebraMap O F) e
    rw [map_mul, map_mul] at e'
    rw [map_mul, h, h, ← hs, ← mul_div_assoc, e', mul_div_assoc, div_self hyF, _root_.mul_one]
  by_cases hP : P'.comap b = ⊥
  · refine ⟨x, y, 1, h1, fun hm => hy0 ?_, by rw [_root_.one_mul, _root_.one_mul]; exact key x y (mul_comm _ _)⟩
    have : y ∈ P'.comap b := hm
    rwa [hP, Ideal.mem_bot] at this
  · have hd := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain O hP
      (Localization.AtPrime (P'.comap b))
    have inj : Function.Injective (algebraMap O (Localization.AtPrime (P'.comap b))) :=
      IsLocalization.injective _ (P'.comap b).primeCompl_le_nonZeroDivisors
    obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap O (Localization.AtPrime (P'.comap b)) x) (algebraMap O _ y)
    obtain ⟨u, v, rfl⟩ := IsLocalization.exists_mk'_eq (P'.comap b).primeCompl c
    have hv : b v ∉ P' := v.2
    rcases hc with hc | hc
    · have e : u * x = v * y := by
        apply inj
        rw [map_mul, map_mul, ← hc, ← IsLocalization.mk'_spec' (Localization.AtPrime (P'.comap b)) u v]
        ring
      have e' := key _ _ e
      refine ⟨v, u, 1, h1, fun hm => hv ?_, by rw [_root_.one_mul, _root_.one_mul]; exact e'⟩
      rw [← e']
      exact P'.mul_mem_right _ hm
    · have e : v * x = u * y := by
        apply inj
        rw [map_mul, map_mul, ← hc, ← IsLocalization.mk'_spec' (Localization.AtPrime (P'.comap b)) u v]
        ring
      exact ⟨u, v, 1, h1, hv, by rw [_root_.one_mul, _root_.one_mul]; exact key _ _ e⟩

theorem flat_of_dedekind_of_injective {O O' : Type} [CommRing O] [IsDedekindDomain O] [CommRing O'] [IsDomain O']
    (b : O →+* O') (hb : Function.Injective b) : b.Flat := by
  algebraize [b]
  refine IsDedekindDomain.flat_iff_torsion_eq_bot.2 ?_
  rw [eq_bot_iff]
  rintro x ⟨a, ha⟩
  have ha' : b a * x = 0 := by
    rw [Submonoid.smul_def, Algebra.smul_def] at ha
    exact ha
  rcases mul_eq_zero.1 ha' with e | e
  · exact absurd (hb (by rw [e, map_zero])) (nonZeroDivisors.ne_zero a.2)
  · exact e

theorem isNormalScheme_of_flat_of_surjectiveOnStalks {X Y : Scheme.{0}} (f : Y ⟶ X) [Flat f] [SurjectiveOnStalks f]
    (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y := by
  intro y
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks f y
  obtain ⟨h₁, h₂⟩ := hX (f y)
  let e := (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
  exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩

theorem Models.Cpt.exists_above_isIso_of_overring : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (O' : Type) [CommRing O'] (β' : O' →+* F) (b : O →+* O') (C : Cpt c t β) (ν : SABMap t t (𝟙 U)), ν.φ = 𝟙 _ → IsDedFrac β → IsDedFrac β' → β'.comp b = β → ∃ (C' : Cpt c t β') (a : C'.Above C b (𝟙 U) ν), IsIso (pullback.lift a.π C'.s a.π_over) := by
  intro E _ _ _ H U F O _ _ c t β O' _ β' b C ν hν hβ hβ' hb
  obtain ⟨⟨_, _⟩, -, hF⟩ := hβ
  obtain ⟨⟨_, -⟩, -, hF'⟩ := hβ'
  have inj' : Function.Injective β' := by
    letI := β'.toAlgebra
    exact IsFractionRing.injective O' F
  have hbx : ∀ x, β' (b x) = β x := fun x => congrArg (fun f : O →+* F => f x) hb
  have inj : Function.Injective β := by
    letI := β.toAlgebra
    exact IsFractionRing.injective O F
  have injb : Function.Injective b := fun x y e => inj (by rw [← hbx, ← hbx, e])
  have hS : SurjectiveOnStalks (spMap b) := by
    letI := β.toAlgebra
    exact (HasRingHomProperty.Spec_iff (P := @SurjectiveOnStalks)).2
      (surjectiveOnStalks_of_dedekind_overring β' b inj' hbx)
  have hFl : Flat (spMap b) := by
    rw [Flat.SpecMap_iff]
    exact flat_of_dedekind_of_injective b injb
  have hS' : SurjectiveOnStalks (pullback.fst C.s (spMap b)) :=
    MorphismProperty.of_isPullback (P := @SurjectiveOnStalks) (IsPullback.of_hasPullback _ _).flip hS
  have hsp : spMap β' ≫ spMap b = spMap β := by
    rw [← hb, spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  have hp : IsPullback (pullback.fst (pullback.snd C.s (spMap b)) (spMap β') ≫ pullback.fst C.s (spMap b))
      (pullback.snd (pullback.snd C.s (spMap b)) (spMap β')) C.s (spMap β) := by
    rw [← hsp]
    exact (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback _ _)
  have hj : ((C.jQ ≫ hp.isoPullback.inv) ≫ pullback.fst (pullback.snd C.s (spMap b)) (spMap β')) ≫
      pullback.fst C.s (spMap b) = C.jQ ≫ pullback.fst _ _ := by
    simp only [Category.assoc, hp.isoPullback_inv_fst]
  obtain ⟨t', ⟨mu⟩⟩ : ∃ t' : SAB H (pullback C.s (spMap b)), Nonempty (SABMap t' C.t (pullback.fst C.s (spMap b))) := by
    obtain ⟨PP, cub, sym, adj, prim, m, hm⟩ := sabPull Out.CubePf.cubePull (pullback.fst C.s (spMap b)) C.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨m', hm'⟩ : ∃ m' : SABMap t t' ((C.jQ ≫ hp.isoPullback.inv) ≫
      pullback.fst (pullback.snd C.s (spMap b)) (spMap β')), C.m.φ = m'.φ ≫ mu.φ := by
    have aux : ∀ (g : U ⟶ pullback C.s (spMap b)) (e : U ⟶ C.X) (n : SABMap t C.t e),
        g ≫ pullback.fst C.s (spMap b) = e → ∃ m' : SABMap t t' g, n.φ = m'.φ ≫ mu.φ := by
      rintro g e n rfl
      exact ObjMaps.exists_sab_cancel mu n
    exact aux _ _ C.m hj
  have := C.flat
  have := C.jQ_open
  have hr : Set.range (C.jQ ≫ hp.isoPullback.inv) = hp.isoPullback.hom ⁻¹' Set.range C.jQ := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, by simp⟩
    · rintro ⟨u, hu⟩
      exact ⟨u, by simp [hu]⟩
  have hiso : IsIso (pullback.lift (pullback.fst C.s (spMap b)) (pullback.snd C.s (spMap b)) pullback.condition) := by
    rw [pullback.lift_fst_snd]
    infer_instance
  refine ⟨⟨pullback C.s (spMap b), pullback.snd _ _,
    isNormalScheme_of_flat_of_surjectiveOnStalks (pullback.fst C.s (spMap b)) C.normal,
    ProjSpace.isProjOver_pullback_snd b C.proj, inferInstance, C.jQ ≫ hp.isoPullback.inv, ?_, inferInstance, ?_, t', m', ?_⟩,
    ⟨pullback.fst _ _, pullback.condition, inferInstance, mu, ?_, ?_⟩, hiso⟩
  · rw [Category.assoc, hp.isoPullback_inv_snd, C.jQ_over]
  · rw [hr]
    exact C.jQ_dense.preimage hp.isoPullback.hom.isOpenEmbedding.isOpenMap
  · rw [hr, ← C.ab_gen]
    ext x
    simp only [Set.mem_preimage]
    rw [← abLocus_pullback abLocusOne C.t.semi mu.cart.1, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      hp.isoPullback_hom_fst]
  · exact hj.trans (Category.id_comp _).symm
  · refine hm'.symm.trans ?_
    rw [hν, Category.id_comp]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelBaseChangeOverringStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
theorem _root_.GlobalTheory.T.exists_model_baseChange_overring : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (O' : Type) [CommRing O'] (β' : O' →+* F) (b : O →+* O') (C : Cpt c t β) (ν : SABMap t t (𝟙 U)), ν.φ = 𝟙 _ → IsDedFrac β → IsDedFrac β' → β'.comp b = β → ∃ (C' : Cpt c t β') (a : C'.Above C b (𝟙 U) ν), IsIso (pullback.lift a.π C'.s a.π_over) := by
  first | exact @GlobalTheory.Models.Cpt.exists_above_isIso_of_overring | exact GlobalTheory.Models.Cpt.exists_above_isIso_of_overring | (intros; apply GlobalTheory.Models.Cpt.exists_above_isIso_of_overring <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticDatumTorsionLevel
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SiegUnram

open GlobalTheory.FamRep

section Group

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {L : LB G.left} {L' : LB G'.left}



end Group

variable {o : Type} [CommRing o] {S S' : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
  {s' : S' ⟶ Sp o}

theorem locallyOfFiniteType_of_isQProjOver (h : IsQProjOver s) : LocallyOfFiniteType s := by
  obtain ⟨N, i, hi, -, rfl⟩ := h
  have := isProper_str o N
  infer_instance

end GlobalTheory.SiegUnram
end
end
