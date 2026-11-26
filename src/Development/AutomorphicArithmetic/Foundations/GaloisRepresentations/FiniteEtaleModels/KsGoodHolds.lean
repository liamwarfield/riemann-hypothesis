module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.CovLink
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.StepAHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiesAbsHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ExistsIsoOfCart
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ActGActGInv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OBaseOnto
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OStepF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeMapFiniteEtaleSurjectiveStatement

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BEtaPt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

private theorem ev_nsmul {G : GDatum} {k : Type} [Field k] {Q : Type} [Group Q] {act : G.O → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : GTateIso G k Q act e) (n c : ℕ) (x : G.La) :
    I.ev n (c • x) = I.ev n x ^ c := by
  induction c with
  | zero =>
    rw [zero_nsmul, pow_zero]
    have h := I.add n 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  | succ c ih =>
    rw [succ_nsmul, I.add, ih, pow_succ]

theorem UpperTheory.Gal.FiniteEtaleModels.etaPtB_holds :
    EtaPtB := by
  unfold UpperTheory.Gal.FiniteEtaleModels.EtaPtB
  intro p _ D G L R _ _ gb h X s N' N o' o ψ hT Ω _ _ z x y hv
  unfold UpperTheory.Gal.Int.Geo.IsTrans at hT
  obtain ⟨-, -, -, -, hgeo⟩ := hT
  obtain ⟨I', I'', h1, h2, hiff⟩ := hgeo Ω z (Spec.preimage (z ≫ s)).hom (by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap
    rw [CommRingCat.ofHom_hom, Spec.map_preimage])
  have hN' : 0 < (N' : ℕ) := by
    have := N'.2.1
    omega
  have hN : 0 < (N : ℕ) := by
    have := N.2.1
    omega
  have key := (hiff _ (Nat.mul_pos hN' hN) (Nat.Coprime.mul_left N'.2.2 N.2.2)
    ((N : ℕ) • x) ((N' : ℕ) • y)).2 hv
  have ex : I'.ev ((N' : ℕ) * N) ((N : ℕ) • x) = I'.ev N' x := by
    have t1 := I'.tower (N' : ℕ) N hN' hN x
    have t2 := ev_nsmul I' ((N' : ℕ) * N) N x
    exact t2.trans t1
  have ey : I''.ev ((N' : ℕ) * N) ((N' : ℕ) • y) = I''.ev N y := by
    have t1 := I''.tower (N : ℕ) N' hN hN' y
    have t2 := ev_nsmul I'' ((N' : ℕ) * N) N' y
    rw [mul_comm] at t1
    exact t2.trans t1
  have key2 := (ex ▸ ey ▸ key : I'.ev N' x ≫ ψ = I''.ev N y)
  have e1 := h1 x
  have e2 := h2 y
  rw [← Category.assoc]
  exact (congrArg (fun f => f ≫ ψ) e1).trans (key2.trans e2.symm)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.AdmissibleOfIntegralConjLe
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)

namespace UpperTheory.Gal.FiniteEtaleModels

theorem powMap_congr {X Y : Scheme.{0}} {A : Over X} {B : Over Y} {f f' : X ⟶ Y} {φ φ' : A.left ⟶ B.left} (h : f = f') (h' : φ = φ')
    (u : φ ≫ B.hom = A.hom ≫ f) (u' : φ' ≫ B.hom = A.hom ≫ f') (k : ℕ) : GlobalTheory.KS.powMap f φ u k = GlobalTheory.KS.powMap f' φ' u' k := by
  subst h h'; rfl

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {E : Type} [Field E] [NumberField E] {gb : GBase D.toG E}
  {w : HeightOneSpectrum (𝓞 E)} {q : ℕ} [Fact q.Prime] {r : ℤ} {𝔴 𝔫 : Ideal (𝓞 D.F)} {S : Site gb w q r 𝔴 𝔫}

theorem Down.pw_ov (hP : PowCart) {N₁ N₂ : ℕ} {𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)} {X₁ : Ext S N₁ 𝔟₁} {X₂ : Ext S N₂ 𝔟₂} (d : Down X₁ X₂) (k : ℕ) :
    d.pw k ≫ (GlobalTheory.KS.pow X₂.Y.univ.A k).hom ≫ X₂.Y.s = (GlobalTheory.KS.pow X₁.Y.univ.A k).hom ≫ X₁.Y.s := by
  have h := (hP _ _ _ X₁.Y.univ.A X₂.Y.univ.A X₂.Y.univ.A d.t (𝟙 _) d.Φ (𝟙 _) d.w (by simp) k).2.1
  rw [Down.pw, ← Category.assoc, h, Category.assoc, d.ov]

theorem exists_wit (hP : PowCart) {k : ℕ} (T : KS L gb k) (h : G.GAf) (M₁ M₂ : Lv p) (a b) :
    ∃ W : Wit T h M₁ M₂, ∀ {N₁ N₂ : ℕ} {𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)} {X₁ : Ext S N₁ 𝔟₁} {X₂ : Ext S N₂ 𝔟₂} {c₁ c₂ : ℕ} {a₁ a₂ : 𝓞 D.F}
      (C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁) (C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂) (d : Down X₁ X₂), d.Extends W C₁ C₂ →
      X₁.site.pi T C₁ ≫ d.pw k = T.X.tr (T.lev M₁) (T.lev M₂) h a b ≫ X₂.site.pi T C₂ := by
  obtain ⟨π, o, ψ, φ, hw, hov, htr, he⟩ := T.tr_eq M₁ M₂ h a b
  refine ⟨⟨π, o, ψ, φ, hov, htr⟩, fun {_ _ _ _ X₁ X₂ _ _ _ _} C₁ C₂ d hd => ?_⟩
  have e1 := (hP _ _ _ (T.M M₁).univ.A X₁.Y.univ.A X₂.Y.univ.A C₁.j d.t C₁.m.φ d.Φ C₁.m.cart.1.w d.w k).2.2
    (by rw [Category.assoc, d.w, ← Category.assoc, C₁.m.cart.1.w, Category.assoc])
  have e2 := (hP _ _ _ (T.M M₁).univ.A (T.M M₂).univ.A X₂.Y.univ.A π C₂.j (ψ.left ≫ φ.φ) C₂.m.φ hw C₂.m.cart.1.w k).2.2
    (by rw [Category.assoc, C₂.m.cart.1.w, ← Category.assoc, hw, Category.assoc])
  have e3 : C₁.pw k ≫ d.pw k = GlobalTheory.KS.powMap π (ψ.left ≫ φ.φ) hw k ≫ C₂.pw k :=
    e1.trans ((powMap_congr hd.1 (hd.2.trans (Category.assoc _ _ _).symm) _ _ k).trans e2.symm)
  show ((T.e M₁).hom ≫ C₁.pw k) ≫ d.pw k = _ ≫ (T.e M₂).hom ≫ C₂.pw k
  rw [Category.assoc, e3, ← Category.assoc, ← he, Category.assoc]

def Ext.ps {N₁ : ℕ} {𝔟 : Ideal (𝓞 D.F)} (X : Ext S N₁ 𝔟) (k : ℕ) : (GlobalTheory.KS.pow X.Y.univ.A k).left ⟶ Spec (CommRingCat.of (Ow w)) :=
  (GlobalTheory.KS.pow X.Y.univ.A k).hom ≫ X.Y.s

def Ok {N₁ N₂ : ℕ} {𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)} {X₁ : Ext S N₁ 𝔟₁} {X₂ : Ext S N₂ 𝔟₂} {k : ℕ} (T : KS L gb k) (h : G.GAf) {M₁ M₂ : Lv p}
    (π₁ : T.X.Z (T.lev M₁) ⟶ (GlobalTheory.KS.pow X₁.Y.univ.A k).left) (π₂ : T.X.Z (T.lev M₂) ⟶ (GlobalTheory.KS.pow X₂.Y.univ.A k).left)
    (t : (GlobalTheory.KS.pow X₁.Y.univ.A k).left ⟶ (GlobalTheory.KS.pow X₂.Y.univ.A k).left) : Prop :=
  t ≫ X₂.ps k = X₁.ps k ∧ ∀ a b, π₁ ≫ t = T.X.tr (T.lev M₁) (T.lev M₂) h a b ≫ π₂

theorem ok_of (hP : PowCart) {N₁ N₂ : ℕ} {𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)} {X₁ : Ext S N₁ 𝔟₁} {X₂ : Ext S N₂ 𝔟₂} {k : ℕ} (T : KS L gb k) (h : G.GAf)
    {M₁ M₂ : Lv p} {c₁ c₂ : ℕ} {a₁ a₂ : 𝓞 D.F} (C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁) (C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂)
    (Q : Down X₁ X₂ → Prop) (ad : T.X.admitted (T.lev M₁) (T.lev M₂) h)
    (H : ∀ W : Wit T h M₁ M₂, ∃ d : Down X₁ X₂, d.Extends W C₁ C₂ ∧ Q d) :
    ∃ d : Down X₁ X₂, Ok T h (X₁.site.pi T C₁) (X₂.site.pi T C₂) (d.pw k) ∧ Q d := by
  obtain ⟨W, hW⟩ := exists_wit (S := S) hP T h M₁ M₂ ad.1 ad.2
  obtain ⟨d, hd, hq⟩ := H W
  exact ⟨d, ⟨d.pw_ov hP k, fun _ _ => hW C₁ C₂ d hd⟩, hq⟩

theorem Ok.comp {N₁ N₂ N₃ : ℕ} {𝔟₁ 𝔟₂ 𝔟₃ : Ideal (𝓞 D.F)} {X₁ : Ext S N₁ 𝔟₁} {X₂ : Ext S N₂ 𝔟₂} {X₃ : Ext S N₃ 𝔟₃} {k : ℕ} {T : KS L gb k}
    {h h' : G.GAf} {M₁ M₂ M₃ : Lv p} {π₁ : T.X.Z (T.lev M₁) ⟶ (GlobalTheory.KS.pow X₁.Y.univ.A k).left}
    {π₂ : T.X.Z (T.lev M₂) ⟶ (GlobalTheory.KS.pow X₂.Y.univ.A k).left} {π₃ : T.X.Z (T.lev M₃) ⟶ (GlobalTheory.KS.pow X₃.Y.univ.A k).left} {t t'}
    (H : Ok T h π₁ π₂ t) (H' : Ok T h' π₂ π₃ t') (ad : T.X.admitted (T.lev M₁) (T.lev M₂) h) (ad' : T.X.admitted (T.lev M₂) (T.lev M₃) h') :
    Ok T (h' * h) π₁ π₃ (t ≫ t') := by
  refine ⟨by rw [Category.assoc, H'.1, H.1], fun a b => ?_⟩
  rw [← Category.assoc, H.2 ad.1 ad.2, Category.assoc, H'.2 ad'.1 ad'.2, ← Category.assoc, T.X.tr_mul]

theorem admissible_of_integral_conj_le {k : ℕ} (T : KS L gb k) {h : G.GAf} {M₁ M₂ : Lv p} (hi : Integ L h) (ha : ∀ u ∈ L.KN M₁.1, h * u * h⁻¹ ∈ L.KN M₂.1) :
    T.X.admitted (T.lev M₁) (T.lev M₂) h :=
  ⟨(T.Δ_eq _).2 hi, fun u hu => by rw [T.K_eq] at hu ⊢; exact ha u hu⟩

theorem cls_of (hNum : NumEx) (hCls : ClsEx) {N₁ : ℕ} {𝔟 : Ideal (𝓞 D.F)} (X : Ext S N₁ 𝔟) {k : ℕ} (T : KS L gb k) (M : Lv p) (c : ℕ) (a : 𝓞 D.F)
    (hn : X.site.Num M.1 c a) : Nonempty (X.site.Cl (T.M M).univ c a) :=
  (hCls q (datAt S.atq S.sp) (Ow w) E S.b gb _ S.mat M.1 _ c a _ hn.1 (lt_of_lt_of_le (by norm_num) M.2.1) X.lev.1 X.lev.2.1 hn.2 X.Y _ _
    (T.M M).univ).1

theorem lev_le {N₀ κ : ℕ} {𝔞 𝔞' : Ideal (𝓞 D.F)} {K₀ K₁ : Subgroup G.GAf} (hK₀ : IsLev L (Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞) K₀)
    (hK₁ : IsLev L (Ideal.span {((N₀ * κ : ℕ) : 𝓞 D.F)} * 𝔞') K₁) (hle : 𝔞' ≤ 𝔞) : K₁ ≤ K₀ := fun u hu => by
  obtain ⟨u1, u2⟩ := (hK₁ u).1 hu
  refine (hK₀ u).2 ⟨u1, fun v hv => AddSubgroup.closure_mono ?_ (u2 v hv)⟩
  rintro z ⟨x, hx, y⟩
  refine ⟨x, Ideal.mul_mono ?_ hle hx, y⟩
  rw [Ideal.span_singleton_le_span_singleton, Nat.cast_mul]
  exact dvd_mul_right _ _

theorem forget_of (hSc : Sc D G) (hNum : NumEx) (hCls : ClsEx) (hInv : PiInv) (hP : PowCart) (hQ : QuotOf) (hF : StepF) (hD : DegGen) (hE : FEtExt)
    {k : ℕ} (T : KS L gb k) {N₀ κ : ℕ} {𝔞 𝔞' : Ideal (𝓞 D.F)} (X₁ : Ext S (N₀ * κ) 𝔞') (X₀ : Ext S N₀ 𝔞) (hle : 𝔞' ≤ 𝔞) {K₀ K₁ : Subgroup G.GAf}
    (hK₀ : IsLev L (Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞) K₀) (hK₁ : IsLev L (Ideal.span {((N₀ * κ : ℕ) : 𝓞 D.F)} * 𝔞') K₁) {M N : Lv p}
    (hd : N.1 ∣ M.1) {c₁ c₀ : ℕ} {a₁ a₀ : 𝓞 D.F} (n₁ : X₁.site.Num M.1 c₁ a₁) (n₀ : X₀.site.Num N.1 c₀ a₀)
    (C₁ : X₁.site.Cl (T.M M).univ c₁ a₁) (C₀ : X₀.site.Cl (T.M N).univ c₀ a₀) :
    ∃ s, Ok T 1 (X₁.site.pi T C₁) (X₀.site.pi T C₀) s ∧ IsQuot T.X (Ow w) K₀ (T.lev M) (X₀.ps k) (X₁.site.pi T C₁ ≫ s) ∧
      IsQuot T.X (Ow w) K₁ (T.lev M) (s ≫ X₀.ps k) (X₁.site.pi T C₁) ∧ FEt s (K₁.relIndex K₀) := by
  have ad : T.X.admitted (T.lev M) (T.lev N) 1 := admissible_of_integral_conj_le T (integ_of_mem (one_mem _)) fun u hu => by simpa using KN_anti hd hu
  obtain ⟨d, ok, fd, ed, pd⟩ := ok_of hP T 1 C₁ C₀ _ ad (hF p D G L hSc E gb w q r 𝔴 _ S k T N₀ κ 𝔞' 𝔞 X₁ X₀ hle M N c₁ c₀ a₁ a₀ n₁ n₀ hd C₁ C₀)
  obtain ⟨t, ht⟩ := hd
  have n₀' : X₀.site.Num M.1 (c₀ * t) (t * a₀) := by
    rw [ht]; exact (hNum p D E gb w q r 𝔴 _ X₀.site N.1 (lt_of_lt_of_le (by norm_num) N.2.1)).2 c₀ a₀ t n₀
  obtain ⟨C₀'⟩ := cls_of hNum hCls X₀ T M _ _ n₀'
  have pb := (hP _ _ _ X₁.Y.univ.A X₀.Y.univ.A X₀.Y.univ.A d.t (𝟙 _) d.Φ (𝟙 _) d.w (by simp) k).1 pd
  have fs : IsFinite (d.pw k) := MorphismProperty.of_isPullback pb.flip fd
  have ets : Etale (d.pw k) := MorphismProperty.of_isPullback pb.flip ed
  have e0 : X₁.site.pi T C₁ ≫ d.pw k = X₀.site.pi T C₀' :=
    (ok.2 ad.1 ad.2).trans (hInv p D G L E gb w q r 𝔴 _ X₀.site k T K₀ hK₀ M N t c₀ a₀ ht n₀ C₀' C₀ 1 (one_mem _) _ _)
  have q0 : IsQuot T.X (Ow w) K₀ (T.lev M) (X₀.ps k) (X₁.site.pi T C₁ ≫ d.pw k) :=
    e0.symm ▸ hQ p D G L hSc E gb w q r 𝔴 _ X₀.site k T K₀ hK₀ M _ _ n₀' C₀'
  have q1 : IsQuot T.X (Ow w) K₁ (T.lev M) (d.pw k ≫ X₀.ps k) (X₁.site.pi T C₁) := by
    rw [ok.1]
    exact hQ p D G L hSc E gb w q r 𝔴 _ X₁.site k T K₁ hK₁ M _ _ n₁ C₁
  have fl : Flat (X₀.ps k) := by
    obtain ⟨n, hn⟩ := X₀.dim k
    haveI : Smooth (X₀.ps k) := hn.smooth
    infer_instance
  exact ⟨d.pw k, ok, q0, q1, hE (Ow w) E _ _ _ _ _ fl fs ets (hD E _ T.X (Ow w) K₀ K₁ _ _ _ _ _ _ (lev_le hK₀ hK₁ hle) q0 q1)⟩

theorem transl_of (hSc : Sc D G) (hNum : NumEx) (hCls : ClsEx) (hP : PowCart) (hExt : ExtEx) (hA : StepA) (hB : StepB)
    {k : ℕ} (T : KS L gb k) {N₀ κ : ℕ} {𝔞 𝔞' : Ideal (𝓞 D.F)} (X₁ : Ext S (N₀ * κ) 𝔞') (X₀ : Ext S N₀ 𝔞) (hle : 𝔞' ≤ 𝔞) {M N N₁ : Lv p}
    {c₁ c₀ : ℕ} {a₁ a₀ : 𝓞 D.F} (n₁ : X₁.site.Num M.1 c₁ a₁) (n₀ : X₀.site.Num N.1 c₀ a₀)
    (C₁ : X₁.site.Cl (T.M M).univ c₁ a₁) (C₀ : X₀.site.Cl (T.M N).univ c₀ a₀) {h₁ h₂ : G.GAf} (i₁ : Integ L h₁) (i₂ : Integ L h₂)
    (hκ : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h₂ v' = κ • v) (hN₁ : ((N₁.1 : ℕ) : 𝓞 D.F) ∈ Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞')
    (ad₂ : ∀ u ∈ L.KN M.1, h₂ * u * h₂⁻¹ ∈ L.KN N₁.1) (ad₁ : ∀ u ∈ L.KN N₁.1, h₁ * u * h₁⁻¹ ∈ L.KN N.1)
    (hcase : h₁ = 1 ∨ ∃ (𝔴' : Ideal (𝓞 D.F)) (i : ℕ), 𝔴'.IsMaximal ∧ uId D q r ≤ 𝔴' ∧ 𝔞' ≤ 𝔞 * 𝔴' ∧ i ≤ D.n ∧
      Ideal.absNorm 𝔴' ^ i ∣ N₁.1 ∧ IsTjElt L q r 𝔴' i h₁) :
    ∃ t, Ok T (h₁ * h₂) (X₁.site.pi T C₁) (X₀.site.pi T C₀) t := by
  rcases hcase with h1 | ⟨𝔴', i, m', u', le', hi, dv, tj⟩
  · rw [h1] at ad₁
    rw [h1, _root_.one_mul]
    obtain ⟨d, ok, -⟩ := ok_of hP T h₂ C₁ C₀ (fun _ => True) (admissible_of_integral_conj_le T i₂ fun u hu => by simpa using ad₁ _ (ad₂ u hu)) fun W =>
      (hA p D G L hSc E gb w q r 𝔴 _ S k T N₀ κ 𝔞' 𝔞 X₁ X₀ hle _ i₂ hκ M N c₁ c₀ a₁ a₀ n₁ n₀ C₁ C₀ W).imp fun _ h => ⟨h, trivial⟩
    exact ⟨_, ok⟩
  · obtain ⟨X₂⟩ := hExt p D G hSc E gb w q r 𝔴 _ S N₀ 𝔞' ⟨X₀.lev.1, X₀.lev.2.1, X₀.lev.2.2.1, X₁.lev.2.2.2.1, X₁.lev.2.2.2.2⟩
    obtain ⟨c₂, a₂, n₂⟩ := (hNum p D E gb w q r 𝔴 _ X₂.site N₁.1 (lt_of_lt_of_le (by norm_num) N₁.2.1)).1 hN₁
    obtain ⟨C₂⟩ := cls_of hNum hCls X₂ T N₁ c₂ a₂ n₂
    obtain ⟨d₂, ok₂, -⟩ := ok_of hP T h₂ C₁ C₂ (fun _ => True) (admissible_of_integral_conj_le T i₂ ad₂) fun W =>
      (hA p D G L hSc E gb w q r 𝔴 _ S k T N₀ κ 𝔞' 𝔞' X₁ X₂ le_rfl _ i₂ hκ M N₁ c₁ c₂ a₁ a₂ n₁ n₂ C₁ C₂ W).imp fun _ h => ⟨h, trivial⟩
    obtain ⟨d₁, ok₁, -⟩ := ok_of hP T h₁ C₂ C₀ (fun _ => True) (admissible_of_integral_conj_le T i₁ ad₁) fun W =>
      (hB p D G L hSc E gb w q r 𝔴 _ S k T N₀ 𝔞' 𝔞 X₂ X₀ 𝔴' i m' u' le' hi h₁ i₁ tj N₁ N c₂ c₀ a₂ a₀ n₂ n₀ dv C₂ C₀ W).imp fun _ h => ⟨h, trivial⟩
    exact ⟨_, ok₂.comp ok₁ (admissible_of_integral_conj_le T i₂ ad₂) (admissible_of_integral_conj_le T i₁ ad₁)⟩

end

theorem ksGood_of (hSite : SiteEx) (hNum : NumEx) (hCls : ClsEx) (hCov : KSCover) (hInv : PiInv) (hP : PowCart) (hExt : ExtEx)
    (hQ : QuotOf) (hA : StepA) (hB : StepB) (hF : StepF) (hD : DegGen) (hE : FEtExt) (hL : LiesAbs) : KSGood := by
  intro p _ D G L hSc E _ _ e gb hstd k T N J A _ g θ w 𝔴 hpl ⟨q, r, N₀, 𝔞, K₀, hat, hlev, hK₀, hNK, hNm, hdeck, hall⟩
  haveI : Fact q.Prime := ⟨hat.prime⟩
  obtain ⟨S⟩ := hSite p D G hSc E e gb hstd w q r 𝔴 _ hpl hat ⟨N₀, 𝔞, hlev.1, hlev.2.1, hlev.2.2.1, hlev.2.2.2.1, hlev.2.2.2.2, rfl⟩
  have pos : ∀ M : Lv p, 0 < M.1 := fun M => lt_of_lt_of_le (by norm_num) M.2.1
  obtain ⟨X₀⟩ := hExt p D G hSc E gb w q r 𝔴 _ S N₀ 𝔞 hlev
  obtain ⟨c₀, a₀, n₀⟩ := (hNum p D E gb w q r 𝔴 _ X₀.site N.1 (pos N)).1 hNm
  obtain ⟨C₀⟩ := cls_of hNum hCls X₀ T N c₀ a₀ n₀
  obtain ⟨Cv⟩ := hCov p D G L E gb w q r 𝔴 _ X₀.site k T K₀ hK₀ N c₀ a₀ n₀ C₀ hNK J A g θ hdeck
  refine ⟨Cv.toCover, fun j => ?_⟩
  obtain ⟨κ, 𝔞', K₁, h₁, h₂, N₁, hlev', hK₁, hle, -, hMm, hdec, hh, i₁, i₂, hκ, hN₁, ad₂, ad₁, hcase⟩ := hall j
  obtain ⟨X₁⟩ := hExt p D G hSc E gb w q r 𝔴 _ S (N₀ * κ) 𝔞' hlev'
  obtain ⟨c₁, a₁, n₁⟩ := (hNum p D E gb w q r 𝔴 _ X₁.site (g j).M.1 (pos _)).1 hMm
  obtain ⟨C₁⟩ := cls_of hNum hCls X₁ T (g j).M c₁ a₁ n₁
  obtain ⟨s, ok, q0, q1, fe⟩ := forget_of hSc hNum hCls hInv hP hQ hF hD hE T X₁ X₀ hle hK₀ hK₁ (g j).dvd n₁ n₀ C₁ C₀
  refine hL p D G L E gb k T N J A g θ (Ow w) Cv.toCover j K₀ K₁ _ (X₁.site.pi T C₁) s _ (lev_le hK₀ hK₁ hle) hNK q0 q1
    (fun a b => (ok.2 a b).symm) fe hdec fun x hx => ?_
  have x1 : x ∈ L.KN 1 := (g j).le_one hx
  have κx : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG (h₂ * x) v' = κ • v := fun v hv => by
    obtain ⟨v', hv', e'⟩ := hκ v hv
    refine ⟨L.actG x⁻¹ v', integ_of_mem (inv_mem x1) v' hv', ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right, e']
  obtain ⟨t, okt⟩ := transl_of hSc hNum hCls hP hExt hA hB T X₁ X₀ hle n₁ n₀ C₁ C₀ i₁ (i₂.mul (integ_of_mem x1)) κx hN₁ (ad₂ x hx) ad₁ hcase
  rw [← _root_.mul_assoc, ← hh] at okt
  exact ⟨t, okt.1.trans ok.1.symm, okt.2⟩

end UpperTheory.Gal.FiniteEtaleModels
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PExtEx
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.extEx_holds :
    MIn → PowProj → ExtEx := by
  intro hM hPP p _ D G hSc E _ _ gb w q _ r 𝔴 𝔫 S N₁ 𝔟 hL
  obtain ⟨h3, hcq, hcp, hsup, hpow⟩ := hL
  obtain ⟨M⟩ := hM.ex q _ (Ow w) S.b N₁ h3 hcq
  have het : IsEtIdeal S.b 𝔟 :=
    (hM.placeOf q _ (Ow w) S.b r 𝔴 S.atq.max S.std.pmem S.std.a1 S.std.ule S.std.tw 𝔟 hsup).2 hpow
  obtain ⟨Y, π, ρ, hov, ⟨m⟩, hG⟩ := hM.finModel q _ (Ow w) S.b N₁ h3 hcq 𝔟 1 het M
  have hfin : IsFinite π := hG.fin
  have het' : Etale π := hG.etale
  have hMp : IsProjOver M.s := hM.proj q _ (Ow w) S.b N₁ h3 hcq hSc.cpt M
  have hYp : IsProjOver Y.s := by
    rw [← hov]
    exact GlobalTheory.isProjOver_comp_of_finite (Ow w) M.X Y.X π M.s hfin hMp
  have hYs : ∃ d, SmoothOfRelativeDimension d Y.s := by
    have h0 := het'
    rw [Etale.iff_smoothOfRelativeDimension_zero] at h0
    have key : ∀ n, SmoothOfRelativeDimension n M.s → SmoothOfRelativeDimension (0 + n) (π ≫ M.s) :=
      fun n hn => inferInstance
    rw [← hov]
    exact ⟨_, key _ M.smooth⟩
  refine ⟨⟨⟨h3, hcq, hcp, hsup, hpow⟩, M, Y, π, hov, m, hfin, het', fun k => ?_, fun k => ?_⟩⟩
  · exact (hPP q _ (Ow w) S.b N₁ h3 hcq Y.X Y.s Y.univ k).1 hYp
  · obtain ⟨d, hd⟩ := hYs
    exact (hPP q _ (Ow w) S.b N₁ h3 hcq Y.X Y.s Y.univ k).2 d hd
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PQuotOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

private theorem conj_congOne {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {u v : G.GAf} {N : ℕ}
    (hu : u ∈ L.KN 1) (hv : L.CongOne N v) : L.CongOne N (u * v * u⁻¹) := by
  intro z hz
  have hu' : L.CongOne 1 u ∧ L.CongOne 1 u⁻¹ := hu
  obtain ⟨w1, hw1, e1⟩ := hu'.2 z hz
  have hz' : L.actG u⁻¹ z ∈ LaHat D := by
    rw [e1, one_smul]
    exact add_mem hz hw1
  obtain ⟨w2, hw2, e2⟩ := hv _ hz'
  obtain ⟨w3, hw3, e3⟩ := hu'.1 w2 hw2
  refine ⟨L.actG u w2, ?_, ?_⟩
  · rw [e3, one_smul]
    exact add_mem hw2 hw3
  · have key : L.actG u (L.actG u⁻¹ z) = z := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e2, map_add (f := _), map_nsmul, key]

private theorem inAf_mem' {p : ℕ} [Fact p.Prime] (D : Datum p) (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, fun v => by rw [map_one]; exact one_mem _, rfl⟩

private theorem cl_cast {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {E : Type} [Field E] [NumberField E]
    {gb : GBase D.toG E} {w : HeightOneSpectrum (𝓞 E)} {q : ℕ} [Fact q.Prime] {r : ℤ} {𝔴 𝔫 : Ideal (𝓞 D.F)}
    (S : Site gb w q r 𝔴 𝔫) {k : ℕ} (T : KS L gb k) (M : Lv p) {c c' : ℕ} {a a' : 𝓞 D.F} (hc : c' = c) (ha : a' = a)
    (C : S.Cl (T.M M).univ c a) : ∃ C' : S.Cl (T.M M).univ c' a', S.pi T C' = S.pi T C := by
  subst hc ha
  exact ⟨C, rfl⟩

theorem UpperTheory.Gal.FiniteEtaleModels.quotOf_holds :
    PowCart → PiInv → PiFet → PiSep → CongCRT → BaseOnto → QuotOf := by
  intro hPC hPI hPF hPS hCRT hBO p _ D G L hSc E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hK M c a hNum C
  have hM := hNum.1
  have hGen := hNum.2
  let N0 : Lv p := ⟨S.N₀, S.std.three, S.cop⟩
  have hMpos : 0 < M.1 := by have := M.2.1; omega
  have hdvd : S.N₀ ∣ M.1 := ⟨c, hM⟩
  have hup := S.upow
  have hcop : S.N₀.Coprime q := S.std.cop
  have hK₀le : K₀ ≤ L.KN S.N₀ := by
    have key : ∀ g, g ∈ K₀ → L.CongOne S.N₀ g := fun g hg => by
      have h := (hK g).1 hg
      have h2 := h.2
      rw [S.lev] at h2
      exact (((hCRT p D G L q r S.N₀ S.𝔞 hcop hup g (integ_of_mem h.1)).1).1 h2).1
    exact fun g hg => ⟨key g hg, key _ (inv_mem hg)⟩
  have hKM : L.KN M.1 ≤ K₀ := by
    intro g hg
    have h1 : g ∈ L.KN 1 := KN_anti (one_dvd _) hg
    have hcrt := hCRT p D G L q r S.N₀ S.𝔞 hcop hup g (integ_of_mem h1)
    have h2 : L.CongOne S.N₀ g := (KN_anti hdvd hg).1
    have h3 : CongId L S.𝔞 g := (hcrt.2 a M.1 hMpos M.2.2 hGen).2 fun y => hg.1 _ (inAf_mem' D _)
    exact (hK g).2 ⟨h1, by rw [S.lev]; exact hcrt.1.2 ⟨h2, h3⟩⟩
  have hX : T.X.K (T.lev M) = L.KN M.1 := T.K_eq M
  have hX0 : T.X.K (T.lev N0) = L.KN S.N₀ := T.K_eq N0
  refine ⟨?ov, ?le, ?idx, ?adm, ?inv, ?fib, ?free, ?onto⟩
  · obtain ⟨e, -⟩ := hPF p D G L E gb w q r 𝔴 𝔫 S k T M c a hNum C
    exact e
  · rw [hX]; exact hKM
  · rw [hX]
    have h := T.X.idx (T.lev M) (T.lev N0)
    rw [hX, hX0] at h
    exact fun e => h (Subgroup.relIndex_eq_zero_of_le_right hK₀le e)
  · intro u hu
    have hu1 := ((hK u).1 hu).1
    refine ⟨(T.Δ_eq u).2 (integ_of_mem hu1), fun v hv => ?_⟩
    rw [hX] at hv ⊢
    refine ⟨conj_congOne L hu1 hv.1, ?_⟩
    have e : (u * v * u⁻¹)⁻¹ = u * v⁻¹ * u⁻¹ := by group
    rw [e]; exact conj_congOne L hu1 hv.2
  · intro u hu x y
    obtain ⟨C', hC'⟩ := cl_cast (a' := ((1 : ℕ) : 𝓞 D.F) * a) S T M (_root_.mul_one c) (by simp) C
    have h := hPI p D G L E gb w q r 𝔴 𝔫 S k T K₀ hK M M 1 c a (_root_.mul_one _).symm hNum C' C u hu x y
    rwa [hC'] at h
  · intro Ω _ _ x y h
    exact hPS p D G L E gb w q r 𝔴 𝔫 S k T K₀ hK M c a hNum C Ω x y h
  · intro u hu x y Ω _ _ z hz
    exact T.X.free _ (T.lev N0) (by rw [hX, hX0]; exact KN_anti hdvd) u (by rw [hX0]; exact hK₀le hu) x y Ω z hz
  · intro Ω _ _ y σ hy
    obtain ⟨x₀, hx₀, -⟩ := hBO p D G L hSc E gb w q r 𝔴 𝔫 S k T M c a hNum C Ω (y ≫ (GlobalTheory.KS.pow S.Y.univ.A k).hom) σ
      (by simpa using hy)
    have hpb := (hPC _ _ _ (T.M M).univ.A S.Y.univ.A S.Y.univ.A C.j (𝟙 _) C.m.φ (𝟙 _) C.m.cart.1.w (by simp) k).1 C.m.cart.1
    refine ⟨hpb.lift y x₀ hx₀.symm ≫ (T.e M).inv, ?_⟩
    simp only [Site.pi, Cls.pw, Category.assoc, Iso.inv_hom_id_assoc]
    exact hpb.lift_fst _ _ _
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PBaseFet
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.FiniteEtaleModels

private theorem of_section {𝒞 : Type*} [Category 𝒞] [HasPullbacks 𝒞] (W : MorphismProperty 𝒞) [W.IsStableUnderBaseChange]
    {Y X P P' Z B V : 𝒞} (pk : P ⟶ Y) (pk' : P' ⟶ X) (j : X ⟶ Y) (pw : P' ⟶ P) (hp : IsPullback pw pk' pk j)
    (ε : Y ⟶ P) (hε : ε ≫ pk = 𝟙 Y) (sY : Y ⟶ B) (g : V ⟶ B) (sX : X ⟶ V) (ov : j ≫ sY = sX ≫ g)
    (e : Z ≅ P') (q : Z ⟶ V) (hq : e.hom ≫ pk' ≫ sX = q) (h : (e.hom ≫ pw) ≫ pk ≫ sY = q ≫ g)
    (hF : W (pullback.lift (e.hom ≫ pw) q h)) : W (pullback.lift j sX ov) := by
  have hε' : (j ≫ ε) ≫ pk = 𝟙 X ≫ j := by simp [hε]
  let ε₀ : X ⟶ P' := hp.lift (j ≫ ε) (𝟙 X) hε'
  have h₁ : ε₀ ≫ pw = j ≫ ε := hp.lift_fst _ _ _
  have h₂ : ε₀ ≫ pk' = 𝟙 X := hp.lift_snd _ _ _
  have hE : (pullback.fst sY g ≫ ε) ≫ pk ≫ sY = pullback.snd sY g ≫ g := by
    rw [Category.assoc, reassoc_of% hε, pullback.condition]
  let εE : pullback sY g ⟶ pullback (pk ≫ sY) g := pullback.lift (pullback.fst sY g ≫ ε) (pullback.snd sY g) hE
  have F₁ : pullback.lift (e.hom ≫ pw) q h ≫ pullback.fst _ _ = e.hom ≫ pw := pullback.lift_fst _ _ _
  have F₂ : pullback.lift (e.hom ≫ pw) q h ≫ pullback.snd _ _ = q := pullback.lift_snd _ _ _
  have f₁ : pullback.lift j sX ov ≫ pullback.fst _ _ = j := pullback.lift_fst _ _ _
  have f₂ : pullback.lift j sX ov ≫ pullback.snd _ _ = sX := pullback.lift_snd _ _ _
  have E₁ : εE ≫ pullback.fst _ _ = pullback.fst sY g ≫ ε := pullback.lift_fst _ _ _
  have E₂ : εE ≫ pullback.snd _ _ = pullback.snd sY g := pullback.lift_snd _ _ _
  have sq : IsPullback (ε₀ ≫ e.inv) (pullback.lift j sX ov) (pullback.lift (e.hom ≫ pw) q h) εE := by
    have hcomm : (ε₀ ≫ e.inv) ≫ pullback.lift (e.hom ≫ pw) q h = pullback.lift j sX ov ≫ εE := by
      apply pullback.hom_ext
      · simp only [Category.assoc, F₁, E₁, Iso.inv_hom_id_assoc, h₁]
        rw [reassoc_of% f₁]
      · simp only [Category.assoc, F₂, E₂, f₂]
        rw [← hq, Iso.inv_hom_id_assoc, reassoc_of% h₂]
    refine ⟨⟨hcomm⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ e.hom ≫ pk') ?_ ?_ ?_⟩⟩
    · intro s
      have c := s.condition
      have c₁ : s.fst ≫ e.hom ≫ pw = s.snd ≫ pullback.fst sY g ≫ ε := by
        simpa only [Category.assoc, F₁, E₁] using c =≫ pullback.fst _ _
      have c₃ : s.fst ≫ e.hom ≫ pk' ≫ j = s.snd ≫ pullback.fst sY g := by
        have := c₁ =≫ pk
        simpa only [Category.assoc, hp.w, hε, Category.comp_id] using this
      have key : (s.fst ≫ e.hom ≫ pk') ≫ ε₀ = s.fst ≫ e.hom := by
        apply hp.hom_ext
        · simp only [Category.assoc, h₁]
          rw [reassoc_of% c₃, c₁]
        · simp only [Category.assoc, h₂, Category.comp_id]
      rw [← Category.assoc, key, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · intro s
      have c := s.condition
      have c₁ : s.fst ≫ e.hom ≫ pw = s.snd ≫ pullback.fst sY g ≫ ε := by
        simpa only [Category.assoc, F₁, E₁] using c =≫ pullback.fst _ _
      have c₂ : s.fst ≫ q = s.snd ≫ pullback.snd sY g := by
        simpa only [Category.assoc, F₂, E₂] using c =≫ pullback.snd _ _
      have c₃ : s.fst ≫ e.hom ≫ pk' ≫ j = s.snd ≫ pullback.fst sY g := by
        have := c₁ =≫ pk
        simpa only [Category.assoc, hp.w, hε, Category.comp_id] using this
      apply pullback.hom_ext
      · simpa only [Category.assoc, f₁] using c₃
      · simp only [Category.assoc, f₂]
        rw [hq]; exact c₂
    · intro s m h₃ _
      have := h₃ =≫ (e.hom ≫ pk')
      simp only [Category.assoc, Iso.inv_hom_id_assoc, h₂, Category.comp_id] at this
      exact this
  exact MorphismProperty.of_isPullback sq hF

theorem baseFet_holds : PowCart → PiFet → BaseFet := by
  intro hPow hPi p _ D G L _ E _ _ gb w q _ r 𝔴 𝔫 S k T M c a hN C
  obtain ⟨e, hfin, het⟩ := hPi p D G L E gb w q r 𝔴 𝔫 S k T M c a hN C
  have hp : IsPullback (C.pw k) (GlobalTheory.KS.pow (T.M M).univ.A k).hom (GlobalTheory.KS.pow S.Y.univ.A k).hom C.j :=
    ((hPow _ _ _ _ _ _ C.j (𝟙 _) C.m.φ (𝟙 _) C.m.cart.1.w (by simp) k).1 C.m.cart.1)
  let ε : S.Y.X ⟶ (GlobalTheory.KS.pow S.Y.univ.A k).left :=
    (Pi.lift (fun _ : Fin k => (1 : 𝟙_ (Over S.Y.X) ⟶ S.Y.univ.A))).left
  have hε : ε ≫ (GlobalTheory.KS.pow S.Y.univ.A k).hom = 𝟙 _ := Over.w (Pi.lift (fun _ : Fin k => (1 : 𝟙_ (Over S.Y.X) ⟶ S.Y.univ.A)))
  have key : ∀ (W : MorphismProperty Scheme.{0}) [W.IsStableUnderBaseChange],
      W (pullback.lift (S.pi T C) (T.X.q _) e) → W (pullback.lift C.j (T.M M).s C.ov) := fun W _ hF =>
    of_section W _ _ C.j (C.pw k) hp ε hε S.Y.s (gen (Ow w) E) (T.M M).s C.ov (T.e M) _ (T.e_q M) e hF
  exact ⟨key @IsFinite hfin, key @Etale het⟩

end UpperTheory.Gal.FiniteEtaleModels
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PFEtExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

private theorem card_of_pb {K : Type} [Field K] [IsAlgClosed K] {Y Y' : Scheme.{0}} (s : Y' ⟶ Y)
    (x : Spec (CommRingCat.of K) ⟶ Y) (B : Type) [CommRing B] [Algebra K B] [Module.Finite K B] [Algebra.Etale K B]
    (f : Spec (CommRingCat.of B) ⟶ Y')
    (h : IsPullback f (Spec.map (CommRingCat.ofHom (algebraMap K B))) s x) :
    Nat.card {y : Spec (CommRingCat.of K) ⟶ Y' // y ≫ s = x} = Module.finrank K B := by
  have hcomp : ∀ g : B →ₐ[K] K, Spec.map (CommRingCat.ofHom (g : B →+* K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K B)) = 𝟙 _ := by
    intro g
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (g : B →+* K).comp (algebraMap K B) = RingHom.id K := by
      ext z; simp
    rw [this]
    exact Spec.map_id _
  let F : (B →ₐ[K] K) → {y : Spec (CommRingCat.of K) ⟶ Y' // y ≫ s = x} := fun g =>
    ⟨Spec.map (CommRingCat.ofHom (g : B →+* K)) ≫ f, by
      rw [Category.assoc, h.w, ← Category.assoc, hcomp, Category.id_comp]⟩
  have hF : Function.Bijective F := by
    constructor
    · intro g g' e
      have e1 : Spec.map (CommRingCat.ofHom (g : B →+* K)) ≫ f = Spec.map (CommRingCat.ofHom (g' : B →+* K)) ≫ f :=
        congrArg Subtype.val e
      have e2 : Spec.map (CommRingCat.ofHom (g : B →+* K)) = Spec.map (CommRingCat.ofHom (g' : B →+* K)) :=
        h.hom_ext e1 ((hcomp g).trans (hcomp g').symm)
      have e3 := Spec.map_injective e2
      have e4 : (g : B →+* K) = (g' : B →+* K) := by
        simpa using congrArg CommRingCat.Hom.hom e3
      exact AlgHom.coe_ringHom_injective e4
    · rintro ⟨y, hy⟩
      let t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of B) := h.lift y (𝟙 _) (by rw [hy, Category.id_comp])
      have ht1 : t ≫ f = y := h.lift_fst _ _ _
      have ht2 : t ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) = 𝟙 _ := h.lift_snd _ _ _
      let g0 : CommRingCat.of B ⟶ CommRingCat.of K := Spec.preimage t
      have hg0 : Spec.map g0 = t := Spec.map_preimage t
      have hc : CommRingCat.ofHom (algebraMap K B) ≫ g0 = 𝟙 _ := by
        apply Spec.map_injective
        rw [Spec.map_comp, hg0, ht2, Spec.map_id]
      let g : B →ₐ[K] K := { g0.hom with
        commutes' := fun r => by
          have := congrArg (fun u => u.hom r) hc
          simpa using this }
      have hgg : CommRingCat.ofHom (g : B →+* K) = g0 := by
        ext z; rfl
      refine ⟨g, Subtype.ext ?_⟩
      change Spec.map (CommRingCat.ofHom (g : B →+* K)) ≫ f = y
      rw [hgg, hg0, ht1]
  rw [← Nat.card_congr (Equiv.ofBijective F hF)]
  obtain ⟨hfin, hsp⟩ := UpperTheory.Gal.crystallineComparison.splitsField_of K B K inferInstance
  haveI := Fintype.ofFinite (B →ₐ[K] K)
  let e : (TensorProduct K K B) ≃ₗ[K] ((B →ₐ[K] K) → K) :=
    LinearEquiv.ofBijective (UpperTheory.Gal.crystallineComparison.splitMap (fun z : B →ₐ[K] K => z)).toLinearMap hsp
  have e1 := e.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card, (TensorProduct.lid K B).finrank_eq] at e1
  exact e1.symm

private theorem card_lifts {K : Type} [Field K] [IsAlgClosed K] {Y Y' : Scheme.{0}} (s : Y' ⟶ Y) [IsFinite s] [Etale s]
    (x : Spec (CommRingCat.of K) ⟶ Y) (z : Spec (CommRingCat.of K)) :
    Nat.card {y : Spec (CommRingCat.of K) ⟶ Y' // y ≫ s = x} = Scheme.Hom.finrank s (x z) := by
  haveI : Etale (pullback.snd s x) := inferInstance
  haveI : IsAffine (pullback s x) := isAffine_of_isAffineHom (pullback.snd s x)
  let e := (pullback s x).isoSpec
  let φ : CommRingCat.of K ⟶ Γ(pullback s x, ⊤) := Spec.preimage (e.inv ≫ pullback.snd s x)
  have hφ : Spec.map φ = e.inv ≫ pullback.snd s x := Spec.map_preimage _
  have hfinφ : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hetφ : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  letI : Algebra K Γ(pullback s x, ⊤) := φ.hom.toAlgebra
  haveI : Module.Finite K Γ(pullback s x, ⊤) := ((IsFinite.SpecMap_iff φ).mp hfinφ : φ.hom.Finite)
  haveI : Algebra.Etale K Γ(pullback s x, ⊤) :=
    RingHom.etale_algebraMap.mp (HasRingHomProperty.Spec_iff.mp hetφ : φ.hom.Etale)
  have hpb : IsPullback (e.inv ≫ pullback.fst s x) (Spec.map φ) s x := by
    rw [hφ]
    exact IsPullback.of_iso_pullback ⟨by simp [pullback.condition]⟩ e.symm (by simp) (by simp)
  rw [card_of_pb s x Γ(pullback s x, ⊤) _ hpb]
  have h1 := Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb z
  rw [← h1]
  have h2 := Scheme.Hom.finrank_SpecMap_algebraMap K Γ(pullback s x, ⊤) z
  rw [Module.rankAtStalk_eq_finrank_of_free] at h2
  exact h2.symm

theorem UpperTheory.Gal.FiniteEtaleModels.fEtExt_holds :
    FEtExt := by
  intro O E _ _ _ _ _ Y Y' pY s d hfl hfin het hd
  have key : ∀ y₀ : Y, Scheme.Hom.finrank s y₀ = d := by
    intro y₀
    have hg := Flat.generalizingMap pY
    have hsp : (⊥ : PrimeSpectrum O) ⤳ pY y₀ := (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
    obtain ⟨y₁, h1, h2⟩ := hg hsp
    obtain ⟨k, _, _, a, ha⟩ := GlobalTheory.FinEt.exists_algClosed_point Y y₁
    let pt : Spec (CommRingCat.of k) := (⊥ : PrimeSpectrum k)
    have ha1 : a pt = y₁ := by
      have : a pt ∈ Set.range a := ⟨pt, rfl⟩
      rw [ha] at this
      exact this
    let f : CommRingCat.of O ⟶ CommRingCat.of k := Spec.preimage (a ≫ pY)
    have hf : Spec.map f = a ≫ pY := Spec.map_preimage _
    have hpt : (Spec.map f) pt = (⊥ : PrimeSpectrum O) := by
      rw [hf, Scheme.Hom.comp_apply, ha1, h2]
    have hinj : Function.Injective f.hom := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro r hr
      have h3 : r ∈ (PrimeSpectrum.comap f.hom (⊥ : PrimeSpectrum k)).asIdeal := by
        simpa [PrimeSpectrum.comap_asIdeal] using hr
      have h4 : PrimeSpectrum.comap f.hom (⊥ : PrimeSpectrum k) = (⊥ : PrimeSpectrum O) := hpt
      rw [h4] at h3
      simpa using h3
    let g : E →+* k := IsFractionRing.lift hinj
    let σ : sp k ⟶ sp E := Spec.map (CommRingCat.ofHom g)
    have hσ : a ≫ pY = σ ≫ gen O E := by
      rw [← hf, gen, ← Spec.map_comp]
      congr 1
      ext z
      simp [g]
    have h3 := hd k a σ hσ
    rw [card_lifts s a pt, ha1] at h3
    have h5 := h1.map (Scheme.Hom.isLocallyConstant_finrank s).continuous
    rw [← h3]
    exact (specializes_iff_eq.mp h5).symm
  refine ⟨hfin, het, fun K _ _ x => ?_⟩
  rw [card_lifts s x (⊥ : PrimeSpectrum K), key]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PNormExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

private theorem exists_affine_irreducible_open_nhd (S : Scheme) [IsLocallyNoetherian S]
    (hd : ∀ x : S, IsDomain (S.presheaf.stalk x)) (x : S) :
    ∃ V : S.Opens, IsAffineOpen V ∧ x ∈ V ∧ IsIrreducible (V : Set S) := by
  have hG : IsIrreducible {y : S | y ⤳ x} := by
    rw [← Scheme.range_fromSpecStalk]
    haveI := hd x
    simpa [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ _).image _ (S.fromSpecStalk x).continuous.continuousOn
  obtain ⟨N, hN, hxN, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
    (show x ∈ (⊤ : S.Opens) from trivial)
  haveI : IsNoetherianRing Γ(S, N) := IsLocallyNoetherian.component_noetherian ⟨N, hN⟩
  haveI : TopologicalSpace.NoetherianSpace N := noetherianSpace_of_isAffineOpen N hN
  let x' : N := ⟨x, hxN⟩
  let C : Set (Set N) := {Z | Z ∈ irreducibleComponents N ∧ x' ∉ Z}
  have hCfin : C.Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset (fun Z hZ => hZ.1)
  let O : Set N := (⋃₀ C)ᶜ
  have hO : IsOpen O := by
    refine isOpen_compl_iff.mpr ?_
    rw [Set.sUnion_eq_biUnion]
    exact hCfin.isClosed_biUnion (fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1)
  have hxO : x' ∈ O := fun ⟨Z, hZ, hxZ⟩ => hZ.2 hxZ
  let O' : Set S := Subtype.val '' O
  have hO' : IsOpen O' := N.isOpen.isOpenMap_subtype_val O hO
  have hsub : O' ⊆ closure {y : S | y ⤳ x} := by
    rintro _ ⟨y, hyO, rfl⟩
    obtain ⟨Z, hZ, hyZ⟩ : ∃ Z ∈ irreducibleComponents N, y ∈ Z := by
      have h := Set.mem_univ y
      rw [← sUnion_irreducibleComponents] at h
      obtain ⟨Z, hZ, hyZ⟩ := h
      exact ⟨Z, hZ, hyZ⟩
    have hxZ : x' ∈ Z := by
      by_contra h
      exact hyO ⟨Z, ⟨hZ, h⟩, hyZ⟩
    have hT : IsIrreducible (Subtype.val '' Z) := hZ.1.image _ continuous_subtype_val.continuousOn
    have hgen := hT.isGenericPoint_genericPoint_closure
    have h1 : hT.genericPoint ⤳ x := hgen.specializes (subset_closure ⟨x', hxZ, rfl⟩)
    have h2 : (y : S) ∈ closure {hT.genericPoint} :=
      specializes_iff_mem_closure.mp (hgen.specializes (subset_closure ⟨y, hyZ, rfl⟩))
    exact closure_mono (Set.singleton_subset_iff.mpr h1) h2
  obtain ⟨V, hV, hxV, hVO⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
    (show x ∈ (⟨O', hO'⟩ : S.Opens) from ⟨x', hxO, rfl⟩)
  exact ⟨V, hV, hxV, ⟨x, hxV⟩, hG.closure.2.open_subset V.isOpen (fun z hz => hsub (hVO hz))⟩

private theorem injective_germ_of_generic_in_open (X : Scheme) [IsReduced X] (W : X.Opens) (x : X) (hx : x ∈ W)
    (hgen : ∀ y ∈ W, x ⤳ y) : Function.Injective (X.presheaf.germ W x hx).hom := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro s hs
  rw [← basicOpen_eq_bot_iff]
  refine eq_bot_iff.mpr (fun y hy => ?_)
  have hyW : y ∈ W := X.basicOpen_le s hy
  have hxb : x ∈ X.basicOpen s := (hgen y hyW).mem_open (X.basicOpen s).isOpen hy
  rw [Scheme.mem_basicOpen X s x hx] at hxb
  rw [hs] at hxb
  exact absurd hxb not_isUnit_zero

private theorem normalization_affine_open_irreducible_of_normal {U S : Scheme} (i : U ⟶ S) [IsOpenImmersion i] [IsDominant i]
    (hd : ∀ x : S, IsDomain (S.presheaf.stalk x))
    (hc : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (V : S.Opens) (hV : IsAffineOpen V) (hirr : IsIrreducible (V : Set S)) :
    letI := (i.app V).hom.toAlgebra
    Function.Bijective (algebraMap Γ(S, V) (integralClosure Γ(S, V) Γ(U, i ⁻¹ᵁ V))) := by
  letI := (i.app V).hom.toAlgebra
  haveI : ∀ x : S, _root_.IsReduced (S.presheaf.stalk x) := fun x => by
    haveI := hd x
    infer_instance
  haveI : IsReduced S := isReduced_of_isReduced_stalk S
  haveI : IsReduced U := isReduced_of_isOpenImmersion i
  have hgen := hirr.isGenericPoint_genericPoint_closure
  have hηV : hirr.genericPoint ∈ V := (hgen.mem_open_set_iff V.isOpen).mpr
    ⟨hirr.1.some, subset_closure hirr.1.some_mem, hirr.1.some_mem⟩
  have hsp : ∀ y ∈ V, hirr.genericPoint ⤳ y := fun y hy => hgen.specializes (subset_closure hy)
  obtain ⟨u, hu⟩ : hirr.genericPoint ∈ Set.range i := by
    obtain ⟨z, hzV, hzr⟩ := i.denseRange.inter_open_nonempty V V.isOpen hirr.1
    exact (hsp z hzV).mem_open i.isOpenEmbedding.isOpen_range hzr
  have hiuV : i u ∈ V := hu ▸ hηV
  have hspS : ∀ y ∈ V, i u ⤳ y := fun y hy => hu ▸ hsp y hy
  have huV : u ∈ i ⁻¹ᵁ V := hiuV
  have hspU : ∀ y ∈ i ⁻¹ᵁ V, u ⤳ y := fun y hy => by
    rw [← i.isOpenEmbedding.isInducing.specializes_iff]
    exact hspS _ hy
  have hφ : i.app V ≫ (U.presheaf.germ (i ⁻¹ᵁ V) u huV ≫ inv (i.stalkMap u)) =
      S.presheaf.germ V (i u) hiuV := by
    rw [← cancel_mono (i.stalkMap u), Category.assoc, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id]
    exact (i.germ_stalkMap V u hiuV).symm
  have hg0inj : Function.Injective (S.presheaf.germ V (i u) hiuV).hom :=
    injective_germ_of_generic_in_open S V (i u) hiuV hspS
  have hφinj : Function.Injective
      (U.presheaf.germ (i ⁻¹ᵁ V) u huV ≫ inv (i.stalkMap u)).hom := by
    have h1 := injective_germ_of_generic_in_open U (i ⁻¹ᵁ V) u huV hspU
    have h2 : Function.Injective (inv (i.stalkMap u)).hom :=
      ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).1
    rw [CommRingCat.hom_comp, RingHom.coe_comp]
    exact h2.comp h1
  haveI : IsDomain (S.presheaf.stalk (i u)) := hd _
  haveI : IsDomain Γ(S, V) := Function.Injective.isDomain _ hg0inj
  letI : Algebra Γ(S, V) (S.presheaf.stalk (i u)) :=
    TopCat.Presheaf.algebra_section_stalk S.presheaf (⟨i u, hiuV⟩ : V)
  have hloc := hV.isLocalization_stalk ⟨i u, hiuV⟩
  have hP : (hV.primeIdealOf ⟨i u, hiuV⟩).asIdeal = ⊥ := by
    refine eq_bot_iff.mpr (fun a ha => ?_)
    have hnu : ¬ IsUnit (algebraMap Γ(S, V) (S.presheaf.stalk (i u)) a) := by
      rw [IsLocalization.AtPrime.isUnit_to_map_iff _ (hV.primeIdealOf ⟨i u, hiuV⟩).asIdeal]
      exact fun h => h ha
    have hnot : i u ∉ S.basicOpen a := by
      rw [Scheme.mem_basicOpen S a (i u) hiuV]
      exact hnu
    rw [Submodule.mem_bot, ← basicOpen_eq_bot_iff]
    exact eq_bot_iff.mpr (fun y hy =>
      hnot ((hspS y (S.basicOpen_le a hy)).mem_open (S.basicOpen a).isOpen hy))
  haveI hfr : IsFractionRing Γ(S, V) (S.presheaf.stalk (i u)) := by
    have e : (hV.primeIdealOf ⟨i u, hiuV⟩).asIdeal.primeCompl = nonZeroDivisors Γ(S, V) := by
      ext a
      simp [Ideal.primeCompl, hP, mem_nonZeroDivisors_iff_ne_zero]
    unfold IsLocalization.AtPrime at hloc
    rw [e] at hloc
    exact hloc
  haveI : IsIntegrallyClosed Γ(S, V) := by
    refine IsIntegrallyClosed.of_localization_maximal ?_
    intro p _ hpm
    let q : PrimeSpectrum Γ(S, V) := ⟨p, hpm.isPrime⟩
    have hq : hV.fromSpec q ∈ V := by
      show hV.fromSpec q ∈ (V : Set S)
      rw [← hV.range_fromSpec]
      exact ⟨q, rfl⟩
    letI : Algebra Γ(S, V) (S.presheaf.stalk (hV.fromSpec q)) :=
      TopCat.Presheaf.algebra_section_stalk S.presheaf (⟨hV.fromSpec q, hq⟩ : V)
    haveI : IsLocalization p.primeCompl (S.presheaf.stalk (hV.fromSpec q)) :=
      hV.isLocalization_stalk' q hq
    haveI := hc (hV.fromSpec q)
    exact IsIntegrallyClosed.of_equiv (IsLocalization.algEquiv p.primeCompl
      (S.presheaf.stalk (hV.fromSpec q)) (Localization.AtPrime p)).toRingEquiv
  constructor
  · intro a b hab
    apply hg0inj
    have hab' : (i.app V).hom a = (i.app V).hom b := congrArg Subtype.val hab
    rw [← hφ, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.comp_apply, hab']
  · rintro ⟨t, ht⟩
    have hint : IsIntegral Γ(S, V)
        ((U.presheaf.germ (i ⁻¹ᵁ V) u huV ≫ inv (i.stalkMap u)).hom t) := by
      refine IsIntegral.map_of_comp_eq (RingHom.id _) _ ?_ ht
      ext a
      exact (congrArg (fun f => CommRingCat.Hom.hom f a) hφ).symm
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    refine ⟨r, Subtype.ext (hφinj ?_)⟩
    rw [← hr]
    exact congrArg (fun f => CommRingCat.Hom.hom f r) hφ

private theorem isIso_fromNormalization_of_normal_noetherian {U S : Scheme} (i : U ⟶ S) [IsOpenImmersion i] [IsDominant i]
    [IsLocallyNoetherian S]
    (hd : ∀ x : S, IsDomain (S.presheaf.stalk x))
    (hc : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x)) :
    IsIso i.fromNormalization := by
  have hcov : iSup (fun V : {V : S.Opens // IsAffineOpen V ∧ IsIrreducible (V : Set S)} => V.1) = ⊤ := by
    refine eq_top_iff.mpr (fun x _ => ?_)
    obtain ⟨V, hV, hxV, hirr⟩ := exists_affine_irreducible_open_nhd S hd x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV, hirr⟩, hxV⟩
  rw [← MorphismProperty.isomorphisms.iff,
    IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) _ hcov]
  rintro ⟨V, hV, hirr⟩
  let W : S.AffineZariskiSite := ⟨V, hV⟩
  haveI : IsOpenImmersion (i.normalizationOpenCover.f W) := i.normalizationOpenCover.map_prop W
  let e := IsOpenImmersion.isoOfRangeEq (i.fromNormalization ⁻¹ᵁ V).ι
    (i.normalizationOpenCover.f W)
    (by
      rw [Scheme.Opens.range_ι]
      exact congr($(i.fromNormalization_preimage ⟨V, hV⟩).1))
  rw [← MorphismProperty.cancel_left_of_respectsIso (MorphismProperty.isomorphisms Scheme) e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso (MorphismProperty.isomorphisms Scheme) _
      hV.isoSpec.hom]
  have hb := normalization_affine_open_irreducible_of_normal i hd hc V hV hirr
  haveI : IsIso (i.normalizationDiagramMap.app (.op V)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact hb
  rw [MorphismProperty.isomorphisms.iff]
  have key : e.inv ≫ (i.fromNormalization ∣_ V) ≫ hV.isoSpec.hom =
      (Spec.map (i.normalizationDiagramMap.app (.op V)) :
        i.normalizationOpenCover.X W ⟶ Spec Γ(S, V)) := by
    refine (cancel_mono hV.fromSpec).mp ?_
    simp [IsAffineOpen.isoSpec_hom, e, Scheme.Hom.ι_fromNormalization]
    exact i.ι_fromNormalization ⟨V, hV⟩
  show IsIso (e.inv ≫ (i.fromNormalization ∣_ V) ≫ hV.isoSpec.hom)
  rw [key]
  exact (inferInstance : IsIso (Spec.map (i.normalizationDiagramMap.app (.op V))))

theorem UpperTheory.Gal.FiniteEtaleModels.normExt_holds :
    NormExt := by
  unfold UpperTheory.Gal.FiniteEtaleModels.NormExt
  intro U S Y B i f g y hi hdom hnoeth hdst hic hfin hcomm
  haveI := hi
  haveI := hdom
  haveI := hnoeth
  haveI := hfin
  haveI : IsIso i.fromNormalization := isIso_fromNormalization_of_normal_noetherian i hdst hic
  have H : i = pullback.lift y i hcomm ≫ pullback.snd g f := (pullback.lift_snd _ _ _).symm
  refine ⟨inv i.fromNormalization ≫
    i.normalizationDesc (pullback.lift y i hcomm) (pullback.snd g f) H ≫ pullback.fst g f, ?_, ?_⟩
  · have h1 : i ≫ inv i.fromNormalization = i.toNormalization := by
      rw [IsIso.comp_inv_eq, Scheme.Hom.toNormalization_fromNormalization]
    rw [reassoc_of% h1, Scheme.Hom.toNormalization_normalizationDesc_assoc, pullback.lift_fst]
  · rw [Category.assoc, Category.assoc, pullback.condition,
      Scheme.Hom.normalizationDesc_comp_assoc, IsIso.inv_hom_id_assoc]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PDegGen
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open UpperTheory.Gal.G3 (sp)

namespace UpperTheory.Gal.FiniteEtaleModels

theorem degGen_holds : DegGen := by
  intro E _ Γ _ X O _ _ K₀ K₁ i Y Y' pY π' s h01 hQ0 hQ1 Ω _ _ y σ hy
  let T : ∀ u : Γ, u ∈ K₀ → (X.Z i ⟶ X.Z i) := fun u hu => X.tr i i u (hQ0.adm u hu).1 (hQ0.adm u hu).2
  have hT : ∀ a b (ha : a ∈ K₀) (hb : b ∈ K₀), T a ha ≫ T b hb = T (b * a) (K₀.mul_mem hb ha) :=
    fun a b ha hb => X.tr_mul _ _ _ _ _ _ _ _ _ _ _
  have hTc : ∀ a b (ha : a ∈ K₀) (hb : b ∈ K₀), a = b → T a ha = T b hb := by
    rintro a b ha hb rfl
    rfl
  have h1 : ∀ h1 : (1 : Γ) ∈ K₀, T 1 h1 = 𝟙 _ := fun h1 => X.tr_self _ _ _ _ (X.K i).one_mem
  have hinv1 : ∀ w (hw : w ∈ K₀), w ∈ K₁ → T w hw ≫ π' = π' := fun w hw hw1 =>
    hQ1.inv w hw1 _ _
  have hinv0 : ∀ w (hw : w ∈ K₀), T w hw ≫ π' ≫ s = π' ≫ s := fun w hw => hQ0.inv w hw _ _
  obtain ⟨x, hx⟩ := hQ0.onto Ω y σ hy
  let f : K₀ → { y' // y' ≫ s = y } := fun u =>
    ⟨x ≫ T (u : Γ)⁻¹ (K₀.inv_mem u.2) ≫ π', by
      rw [Category.assoc, Category.assoc, hinv0 _ (K₀.inv_mem u.2), hx]⟩
  have key : ∀ u v : K₀, f u = f v ↔ (u : Γ)⁻¹ * v ∈ K₁ := by
    intro u v
    constructor
    · intro h
      have hv : (x ≫ T (u : Γ)⁻¹ (K₀.inv_mem u.2)) ≫ π' = (x ≫ T (v : Γ)⁻¹ (K₀.inv_mem v.2)) ≫ π' := by
        simpa [f] using congrArg Subtype.val h
      obtain ⟨w, hw1, a, b, he⟩ := hQ1.fib Ω _ _ hv
      have hw0 := h01 hw1
      have he' : x ≫ T (v : Γ)⁻¹ (K₀.inv_mem v.2) = x ≫ T (w * (u : Γ)⁻¹) (K₀.mul_mem hw0 (K₀.inv_mem u.2)) := by
        rw [he, Category.assoc]
        exact congrArg (x ≫ ·) (hT _ _ (K₀.inv_mem u.2) hw0)
      have hm : v.1 * w * (u : Γ)⁻¹ ∈ K₀ := K₀.mul_mem (K₀.mul_mem v.2 hw0) (K₀.inv_mem u.2)
      have hfix : x ≫ T (v.1 * w * (u : Γ)⁻¹) hm = x := by
        have p1 : w * (u : Γ)⁻¹ ∈ K₀ := K₀.mul_mem hw0 (K₀.inv_mem u.2)
        have e1 : T (v.1 * w * (u : Γ)⁻¹) hm = T (w * (u : Γ)⁻¹) p1 ≫ T v.1 v.2 :=
          (hTc _ _ hm (K₀.mul_mem v.2 p1) (by group)).trans (hT _ _ p1 v.2).symm
        have e2 : T (v : Γ)⁻¹ (K₀.inv_mem v.2) ≫ T v.1 v.2 = 𝟙 _ :=
          (hT _ _ (K₀.inv_mem v.2) v.2).trans
            ((hTc _ _ (K₀.mul_mem v.2 (K₀.inv_mem v.2)) K₀.one_mem (by group)).trans (h1 K₀.one_mem))
        rw [e1, ← Category.assoc, ← he', Category.assoc, e2, Category.comp_id]
      have ht := hQ0.free _ hm _ _ Ω x hfix
      have hc := (hQ0.adm _ (K₀.inv_mem u.2)).2 _ ht
      have := K₁.mul_mem (hQ1.le hc) (K₁.inv_mem hw1)
      convert this using 1
      group
    · intro h
      apply Subtype.ext
      show x ≫ T (u : Γ)⁻¹ (K₀.inv_mem u.2) ≫ π' = x ≫ T (v : Γ)⁻¹ (K₀.inv_mem v.2) ≫ π'
      have hk : ((u : Γ)⁻¹ * v)⁻¹ ∈ K₀ := h01 (K₁.inv_mem h)
      have e : T (v : Γ)⁻¹ (K₀.inv_mem v.2) = T (u : Γ)⁻¹ (K₀.inv_mem u.2) ≫ T _ hk :=
        (hTc _ _ (K₀.inv_mem v.2) (K₀.mul_mem hk (K₀.inv_mem u.2)) (by group)).trans
          (hT _ _ (K₀.inv_mem u.2) hk).symm
      rw [e, Category.assoc, hinv1 _ hk (K₁.inv_mem h)]
  let F : K₀ ⧸ K₁.subgroupOf K₀ → { y' // y' ≫ s = y } := Quotient.lift f (fun u v huv =>
    (key u v).2 (Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp huv)))
  have hinj : Function.Injective F := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H u =>
      induction b using QuotientGroup.induction_on with
      | H v =>
        intro h
        exact QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr ((key u v).1 h))
  have hsurj : Function.Surjective F := by
    rintro ⟨y', hy'⟩
    obtain ⟨x', hx'⟩ := hQ1.onto Ω y' σ (by rw [← Category.assoc, hy', hy])
    obtain ⟨u, hu, a, b, hxe⟩ := hQ0.fib Ω x x' (by rw [hx, ← Category.assoc, hx', hy'])
    refine ⟨QuotientGroup.mk ⟨u⁻¹, K₀.inv_mem hu⟩, ?_⟩
    apply Subtype.ext
    show x ≫ T (u⁻¹)⁻¹ (K₀.inv_mem (K₀.inv_mem hu)) ≫ π' = y'
    rw [hTc (u⁻¹)⁻¹ u (K₀.inv_mem (K₀.inv_mem hu)) hu (inv_inv u), ← Category.assoc]
    rw [← hx', hxe]
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  exact (Nat.card_congr (Equiv.ofBijective F ⟨hinj, hsurj⟩)).symm

end UpperTheory.Gal.FiniteEtaleModels
end
end

namespace UpperTheory.Gal.FiniteEtaleModels

open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.CovMain UpperTheory.Gal.crystallineComparison.Mod

theorem stepA : StepA := stepA_holds (multUnit_of mIn) (latGen_of mIn) (clsEx_of mIn) (trEta_of mIn) (trBack_of mIn) (qComp_of mIn)

theorem baseFet : BaseFet := baseFet_holds (powCart_of mIn) (piFet_of mIn)

theorem stepB : StepB :=
  stepB_of (tjExG_of esNorm_link esGen_link objTri_holds pullIsog_holds pullKer_holds)
    (bRead_of (isogG_of (trEta_of mIn) (trBack_of mIn) (multUnit_of mIn) (trTj_of mIn)) (qObj_of mIn) (qComp_of mIn) objTri_holds)
    (bKer_of (secInjG_of pulledEx_holds pulledRead_holds pullKer_holds kerFromU_holds isoOfKer_holds) (trEtaPt_of mIn))
    (bLev_of latB_holds etaPtB_holds etInj_holds) (descExt_of normExt_holds) baseFet O.baseOnto pulledEx_holds

theorem quotOf : QuotOf := quotOf_holds (powCart_of mIn) (piInv_of mIn) (piFet_of mIn) (piSep_of mIn) (congCRT_of mIn) O.baseOnto

theorem extEx : ExtEx := extEx_holds mIn (powProj_of mIn)

theorem ksGood_holds : KSGood :=
  ksGood_of (siteEx_of mIn) (numEx_of mIn) (clsEx_of mIn) ksCover_holds (piInv_of mIn) (powCart_of mIn) extEx quotOf stepA stepB O.stepF
    degGen_holds fEtExt_holds liesAbs_holds

end UpperTheory.Gal.FiniteEtaleModels
