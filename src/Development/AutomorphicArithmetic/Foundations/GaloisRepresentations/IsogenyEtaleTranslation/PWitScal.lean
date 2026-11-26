module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.EtCancel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLattice

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PWitScal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ)

private theorem ev_nsmul {G : GDatum} {k : Type} [Field k] {Q : Type} [Group Q] {act : G.O → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : GTateIso G k Q act e) (n : ℕ) (hn : 0 < n) (d : ℕ) (x : G.La) :
    I.ev n (d • x) = I.ev n x ^ d := by
  have h0 : I.ev n 0 = 1 := by
    have := I.add n 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  induction d with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ d ih => rw [succ_nsmul, I.add, ih, pow_succ]

private theorem isMonHom_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    IsMonHom ((𝟙 A) ^ n : A ⟶ A) := by
  constructor
  · rw [MonObj.comp_pow, Category.comp_id, MonObj.one_eq_one, one_pow]
  · rw [MonObj.comp_pow, Category.comp_id, MonObj.mul_eq_mul, MonObj.comp_mul, tensorHom_fst,
      tensorHom_snd, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, Category.comp_id, mul_pow]

private theorem pow_comp_hom {S : Scheme.{0}} {A B Z : Over S} [MonObj A] [MonObj B] (f : A ⟶ B) [IsMonHom f]
    (x : Z ⟶ A) (n : ℕ) : (x ^ n) ≫ f = (x ≫ f) ^ n := MonObj.pow_comp x n f

theorem UpperTheory.Gal.FixZ.witScal_of :
    UpperTheory.Gal.G3.RelComp → UpperTheory.Gal.FixZ.WitScal := by
  intro hR p _ D G L gb N X d z hd hdp hz
  obtain ⟨-, hact, hmul⟩ := hz
  have hid : ∃ m : GObjMap X.univ X.univ (𝟙 X.X), m.φ = 𝟙 _ :=
    ⟨{ φ := 𝟙 _, φ₂ := 𝟙 _, cart := GlobalTheory.SiegLower.isGrpPullback_id X.univ.A, sq := ⟨by simp, by simp⟩,
       act := fun c => by simp, pol := GlobalTheory.SiegLower.lbIso_pull_id X.univ.isLB, eta := fun y => by simp }, rfl⟩
  obtain ⟨m, hm⟩ := hid
  have hmon : IsMonHom ((𝟙 X.univ.A) ^ d) := isMonHom_pow _ d
  have hcomm : ∀ c : D.O, X.univ.act.act c ≫ ((𝟙 X.univ.A) ^ d) = ((𝟙 X.univ.A) ^ d) ≫ X.univ.act.act c := by
    intro c
    haveI := X.univ.act.hom c
    rw [MonObj.comp_pow, pow_comp_hom, Category.comp_id, Category.id_comp]
  refine ⟨Category.id_comp _, X.univ, (𝟙 X.univ.A) ^ d, m, ?_, by rw [hm]; simp⟩
  refine ⟨hmon, hcomm, ⟨𝟙 _, d, inferInstance, fun c => ?_, Category.comp_id _, Category.id_comp _, hdp⟩,
    ⟨d ^ 2, hdp.pow_left 2, ⟨GlobalTheory.T.lbIso_lbPow_sq_pull_sq2_of_isGen_of_relAmple _ _ X.univ.ab X.univ.P X.univ.isLB X.univ.rig₁ X.univ.rig₂ X.univ.ample d⟩, hmul⟩,
    fun k _ _ t β ht => ?_⟩
  · rw [Category.comp_id, Category.id_comp]
  · obtain ⟨I, hI⟩ := X.univ.geom k t β ht
    refine ⟨I, I, hI, hI, fun n hn hnp x y => ?_⟩
    have h1 := (hR p D G L ℂ gb X.X X.s _ _ _ X.univ X.univ X.univ k t I I I (𝟙 _) (𝟙 _) 1 1 inferInstance inferInstance
      (UpperTheory.Gal.Int.Geo.integ_of_mem (one_mem _))).1 n hn hnp (d • x) y
    have hev : I.ev n x ≫ ((𝟙 X.univ.A) ^ d) = I.ev n (d • x) ≫ 𝟙 _ := by
      rw [MonObj.comp_pow, Category.comp_id, Category.comp_id]
      exact (ev_nsmul I n hn d x).symm
    have hin : inAf D (d • x) = d • inAf D x := GlobalTheory.AdelicSim.inAf_nsmul D d x
    rw [hev, h1]
    simp only [map_one, Module.End.one_apply, hin, hact]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PAlFEt
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo

namespace UpperTheory.Gal.FixZ

private theorem act_nat {S : Scheme.{0}} {O : Type} [Ring O] {A : Over S} [GrpObj A] (act : OActN O A) (n : ℕ) :
    act.act (n : O) = (𝟙 A) ^ n := by
  induction n with
  | zero => simp [KS.Model.act_zero]
  | succ n ih => rw [Nat.cast_succ, act.add, ih, act.one, _root_.pow_succ]

private theorem list_prod_ofFn_eq_of_eq_one_of_ne' {M : Type*} [Monoid M] :
    ∀ {m : ℕ} (f : Fin m → M) (i : Fin m), (∀ j, j ≠ i → f j = 1) → (List.ofFn f).prod = f i := by
  intro m
  induction m with
  | zero => intro f i; exact i.elim0
  | succ m ih =>
    intro f i hf
    rw [List.ofFn_succ, List.prod_cons]
    cases i using Fin.cases with
    | zero =>
      rw [List.prod_eq_one, _root_.mul_one]
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      exact hf _ (Fin.succ_ne_zero j)
    | succ i =>
      rw [hf 0 (Fin.succ_ne_zero i).symm, _root_.one_mul]
      exact ih (fun j => f j.succ) i (fun j hj => hf _ (fun h => hj (Fin.succ_injective _ h)))

private theorem matEnd_diagonal_pr {S : Scheme.{0}} {O : Type} [Ring O] {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ}
    (d : Fin m → O) (i : Fin m) :
    GlobalTheory.KS.matEnd act (Matrix.diagonal d) ≫ GlobalTheory.KS.pr A i = GlobalTheory.KS.pr A i ≫ act.act (d i) := by
  change (Pi.lift (fun i => (List.ofFn fun j => GlobalTheory.KS.pr A j ≫
    act.act (if i = j then d i else 0)).prod)) ≫ GlobalTheory.KS.pr A i = _
  rw [Pi.lift_comp_π]
  rw [list_prod_ofFn_eq_of_eq_one_of_ne' _ i]
  · simp
  · intro j hj
    simp [Ne.symm hj, KS.Model.act_zero, comp_one]

end UpperTheory.Gal.FixZ

open UpperTheory.Gal.FixZ in
theorem UpperTheory.Gal.FixZ.alFEt_of :
    UpperTheory.Gal.G3.IsogFEt → UpperTheory.Gal.FixZ.PowFEt → UpperTheory.Gal.FixZ.AlFEt := by
  intro hIsog hPow p _ D G L gb k T N α hα
  have hc : ∀ a : 𝓞 D.toG.F, a ≠ 0 → ∃ b : 𝓞 D.toG.F, ∃ d : ℕ, 0 < d ∧ a * b = (d : 𝓞 D.toG.F) := by
    intro a ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
    refine ⟨b, Ideal.absNorm (Ideal.span {a}), Nat.pos_of_ne_zero ?_, ?_⟩
    · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact ha
    · rw [← hb, mul_comm]
  set U := (T.M N).univ with hU
  letI := U.grp
  letI := U.comm
  have key : ∀ x y : 𝓞 D.toG.F, ∀ d : ℕ, x * y = d →
      U.act.act (algebraMap (𝓞 D.toG.F) D.toG.O y) ≫ U.act.act (algebraMap (𝓞 D.toG.F) D.toG.O x)
        = 𝟙 U.A ^ d := by
    intro x y d h
    rw [← U.act.mul, ← map_mul, h, map_natCast, act_nat]
  have hf : ∀ s : Fin k, IsFinite (Over.Hom.left (U.act.act (algebraMap (𝓞 D.toG.F) D.toG.O (α s)))) ∧
      Etale (Over.Hom.left (U.act.act (algebraMap (𝓞 D.toG.F) D.toG.O (α s)))) ∧
      Surjective (Over.Hom.left (U.act.act (algebraMap (𝓞 D.toG.F) D.toG.O (α s)))) := by
    intro s
    obtain ⟨b, d, hd, hab⟩ := hc (α s) (hα s)
    have e1 := key b (α s) d ((mul_comm b (α s)).trans hab)
    have e2 := key (α s) b d hab
    exact hIsog ℂ (T.M N).X (T.M N).s U.A U.A U.ab U.ab _ _ d hd (U.act.hom _) (U.act.hom _) e1 e2
  have hg := hPow _ U.A k (fun s => U.act.act (algebraMap (𝓞 D.toG.F) D.toG.O (α s))) hf
    (KS.matEnd U.act (LocalSmoothExtension.diagO D α)) (fun i => matEnd_diagonal_pr U.act _ i)
  obtain ⟨h1, h2, -⟩ := hg
  show IsFinite ((T.e N).hom ≫ _ ≫ (T.e N).inv) ∧ Etale ((T.e N).hom ≫ _ ≫ (T.e N).inv)
  exact ⟨inferInstance, inferInstance⟩

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.TrEqRe
open NumberField Polynomial GlobalTheory.UPel.HT GlobalTheory.LKGeo GlobalTheory.LKTrip

namespace UpperTheory.Gal.FixZ

variable {p : ℕ} [Fact p.Prime]

private lemma conj_ne (D : Datum p) : (starRingEnd ℂ) D.ρc ≠ D.ρc := by
  intro h
  have him : D.ρc.im = 0 := Complex.conj_eq_iff_im.mp h
  have hre : D.ρc = (D.ρc.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hroot := D.ρc_root
  rw [hre] at hroot
  have hr : D.ρc.re ^ 2 - (D.tr : ℝ) * D.ρc.re + (D.nm : ℝ) = 0 := by
    exact_mod_cast hroot
  have hd : ((D.tr : ℝ)) ^ 2 - 4 * (D.nm : ℝ) < 0 := by exact_mod_cast D.disc_neg
  nlinarith [sq_nonneg (2 * D.ρc.re - (D.tr : ℝ))]

private lemma tr_eq_re (D : Datum p) : (D.tr : ℂ) = D.ρc + (starRingEnd ℂ) D.ρc := by
  have hne : D.ρc - (starRingEnd ℂ) D.ρc ≠ 0 := sub_ne_zero.mpr (Ne.symm (conj_ne D))
  have h1 := D.ρc_root
  have h2 : ((starRingEnd ℂ) D.ρc) ^ 2 - (D.tr : ℂ) * (starRingEnd ℂ) D.ρc + (D.nm : ℂ) = 0 := by
    have := congrArg (starRingEnd ℂ) h1
    simpa using this
  apply mul_left_cancel₀ hne
  linear_combination h2 - h1

private lemma eps_eq (D : Datum p) : W2.epsD D = LocalSmoothExtension.epsOf D := by
  funext τ
  have hω : ((D.ω : D.F)) ^ 2 - (D.tr : D.F) * (D.ω : D.F) + (D.nm : D.F) = 0 := by
    have h1 : (D.ω : 𝓞 D.F) ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
      rw [← D.tr_eq, ← D.nm_eq]; ring
    have h2 := congrArg (algebraMap (𝓞 D.F) D.F) h1
    simpa only [map_sub, map_add (f := _), map_mul, map_pow, map_intCast, map_zero] using h2
  have hτ : (τ (D.ω : D.F)) ^ 2 - (D.tr : ℂ) * τ (D.ω : D.F) + (D.nm : ℂ) = 0 := by
    have := congrArg τ hω
    simpa using this
  have hfac : (τ (D.ω : D.F) - D.ρc) * (τ (D.ω : D.F) - (starRingEnd ℂ) D.ρc) = 0 := by
    have h1 := D.ρc_root
    have h2 := tr_eq_re D
    rw [h2] at h1 hτ
    linear_combination hτ - h1
  unfold W2.epsD LocalSmoothExtension.epsOf
  by_cases h : τ (D.ω : D.F) = D.ρc
  · have : τ (D.ω : D.F) ≠ (starRingEnd ℂ) D.ρc := by
      rw [h]; exact Ne.symm (conj_ne D)
    simp [h, Ne.symm (conj_ne D)]
  · have h' : τ (D.ω : D.F) = (starRingEnd ℂ) D.ρc := by
      rcases mul_eq_zero.mp hfac with h0 | h0
      · exact absurd (sub_eq_zero.mp h0) h
      · exact sub_eq_zero.mp h0
    rw [if_neg h, if_pos h']

private lemma map_inv {K K' : Type} [Field K] [Field K'] (f : K →+* K') (P : K[X]) :
    (W2.invPoly P).map f = LocalSmoothExtension.invPol (P.map f) := by
  unfold W2.invPoly LocalSmoothExtension.invPol
  rw [Polynomial.map_mul, Polynomial.map_C, map_inv₀, Polynomial.coeff_map]
  congr 1
  simp only [Polynomial.reverse, Polynomial.natDegree_map, Polynomial.reflect_map]

private lemma kap_iff {D : Datum p} {G : HTGroup p} (L : Link D G) (ha : D.a = 1) (i₀ : Fin D.a)
    (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1) :
    (∀ x, v.embedding (L.e x) = D.tau i₀ x) ↔ v.embedding (L.e (D.ω : D.F)) = D.ρc := by
  refine ⟨fun h => (h _).trans (D.tau_ω i₀), fun h => ?_⟩
  obtain ⟨i, hi⟩ := (L.sig v).mp hv
  have hii : i = i₀ := by
    haveI : Subsingleton (Fin D.a) := by rw [ha]; infer_instance
    exact Subsingleton.elim _ _
  subst hii
  have hs : ∀ x, (G.iotaC.comp (L.s i)) (L.e x) = D.tau i x := fun x => L.s_C i x
  rcases InfinitePlace.embedding_mk_eq (G.iotaC.comp (L.s i)) with e | e
  · intro x
    rw [hi, e]
    exact hs x
  · exfalso
    rw [hi, e, ComplexEmbedding.conjugate_coe_eq, hs, D.tau_ω] at h
    exact conj_ne D h

private lemma kap_eq {D : Datum p} {G : HTGroup p} (L : Link D G) (ha : D.a = 1) (i₀ : Fin D.a)
    (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1) (μ : ℂ) :
    (W2.kap L v (D.tau i₀) μ)⁻¹ = LocalSmoothExtension.markOf L v μ := by
  unfold W2.kap LocalSmoothExtension.markOf
  by_cases h : v.embedding (L.e (D.ω : D.F)) = D.ρc
  · rw [if_pos ((kap_iff L ha i₀ v hv).mpr h), if_pos h]
  · rw [if_neg (fun h' => h ((kap_iff L ha i₀ v hv).mp h')), if_neg h]

end UpperTheory.Gal.FixZ

theorem UpperTheory.Gal.FixZ.wtEq_of :
    UpperTheory.Gal.FixZ.WtEq := by
  intro p _ D G L ha i₀ v hv k α y
  funext P μ
  unfold UpperTheory.Gal.W2.wtFix UpperTheory.Gal.LocalSmoothExtension.cW UpperTheory.Gal.LocalSmoothExtension.endPol
  rw [UpperTheory.Gal.FixZ.eps_eq, UpperTheory.Gal.FixZ.map_inv, UpperTheory.Gal.FixZ.kap_eq L ha i₀ v hv μ]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PPowFEt
open AlgebraicGeometry CategoryTheory Limits

namespace UpperTheory.Gal.FixZ

section Coord

variable {C : Type*} [Category C] {A : C} {k : ℕ} [HasProduct (fun _ : Fin k => A)]

private noncomputable def coordMap (j : Fin k) (φ : A ⟶ A) :
    (∏ᶜ fun _ : Fin k => A) ⟶ ∏ᶜ fun _ : Fin k => A :=
  Pi.lift fun i => if i = j then Pi.π (fun _ : Fin k => A) j ≫ φ else Pi.π (fun _ : Fin k => A) i

private lemma coordMap_π (j i : Fin k) (φ : A ⟶ A) :
    coordMap j φ ≫ Pi.π (fun _ : Fin k => A) i =
      if i = j then Pi.π (fun _ : Fin k => A) j ≫ φ else Pi.π (fun _ : Fin k => A) i := by
  simp [coordMap]

private lemma coordMap_isPullback (j : Fin k) (φ : A ⟶ A) :
    IsPullback (coordMap j φ) (Pi.π (fun _ : Fin k => A) j) (Pi.π (fun _ : Fin k => A) j) φ := by
  refine ⟨⟨by simp [coordMap_π]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => Pi.lift fun i => if i = j then s.snd else s.fst ≫ Pi.π (fun _ : Fin k => A) i)
    ?_ ?_ ?_⟩⟩
  · intro s
    refine Pi.hom_ext _ _ fun i => ?_
    rw [Category.assoc, coordMap_π]
    by_cases h : i = j
    · subst h
      simpa using s.condition.symm
    · simp [h]
  · intro s
    simp
  · intro s m h₁ h₂
    refine Pi.hom_ext _ _ fun i => ?_
    by_cases h : i = j
    · subst h
      simpa using h₂
    · have := congrArg (· ≫ Pi.π (fun _ : Fin k => A) i) h₁
      simpa [coordMap_π, h] using this

end Coord

private lemma pow_prop (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] {S : Scheme.{0}} (A : Over S) (k : ℕ) (f : Fin k → (A ⟶ A))
    (hf : ∀ i, P (f i).left) (g : GlobalTheory.KS.pow A k ⟶ GlobalTheory.KS.pow A k)
    (hg : ∀ i, g ≫ GlobalTheory.KS.pr A i = GlobalTheory.KS.pr A i ≫ f i) : P g.left := by
  have step : ∀ j : ℕ, j ≤ k → ∃ h : GlobalTheory.KS.pow A k ⟶ GlobalTheory.KS.pow A k, P h.left ∧
      ∀ i : Fin k, h ≫ GlobalTheory.KS.pr A i =
        if i.val < j then GlobalTheory.KS.pr A i ≫ f i else GlobalTheory.KS.pr A i := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨𝟙 _, by simpa using P.id_mem _, fun i => by simp⟩
    | succ j ih =>
      intro hj
      obtain ⟨h, hP, hh⟩ := ih (by omega)
      let j' : Fin k := ⟨j, by omega⟩
      have hb : IsPullback (coordMap j' (f j')).left (GlobalTheory.KS.pr A j').left
          (GlobalTheory.KS.pr A j').left (f j').left :=
        (coordMap_isPullback j' (f j')).map (Over.forget S)
      have he : P (coordMap j' (f j')).left := P.of_isPullback hb.flip (hf j')
      refine ⟨h ≫ coordMap j' (f j'), ?_, fun i => ?_⟩
      · rw [Over.comp_left]
        exact P.comp_mem _ _ hP he
      · rw [Category.assoc, GlobalTheory.KS.pr, coordMap_π]
        by_cases hi : i = j'
        · subst hi
          have h0 : h ≫ Pi.π (fun _ : Fin k => A) j' = Pi.π (fun _ : Fin k => A) j' := by
            have := hh j'
            simpa [GlobalTheory.KS.pr, j'] using this
          rw [if_pos rfl, if_pos (by simp [j']), ← Category.assoc, h0]
        · have hne : i.val ≠ j := fun e => hi (Fin.ext e)
          have := hh i
          simp only [GlobalTheory.KS.pr] at this
          simp only [hi, if_false, this]
          by_cases hlt : i.val < j
          · simp [hlt, Nat.lt_succ_of_lt hlt]
          · have : ¬ i.val < j + 1 := by omega
            simp [hlt, this]
  obtain ⟨h, hP, hh⟩ := step k le_rfl
  have : g = h := Pi.hom_ext _ _ fun i => by
    have := hh i
    simp only [i.isLt, if_true] at this
    exact (hg i).trans this.symm
  rw [this]
  exact hP

theorem powFEt_of : PowFEt := by
  intro S A k f hf g hg
  exact ⟨pow_prop @IsFinite A k f (fun i => (hf i).1) g hg,
    pow_prop @Etale A k f (fun i => (hf i).2.1) g hg,
    pow_prop @Surjective A k f (fun i => (hf i).2.2) g hg⟩

end UpperTheory.Gal.FixZ
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PBridge
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo (KS Lv Sc Integ IsTrans)
open UpperTheory.Gal.LocalSmoothExtension (qAt al leg cW CxFin StdC)

namespace UpperTheory.Gal.FixZ

private theorem lev_eq {G : Type} [Group G] (K : Subgroup G) (h : G) :
    GlobalTheory.HeckeCorr.heckeLevel K h⁻¹ = G3.lev K h := by
  ext x
  simp only [GlobalTheory.HeckeCorr.heckeLevel, G3.lev, Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_comap]
  constructor
  · rintro ⟨hx, y, hy, rfl⟩
    refine ⟨hx, ?_⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · rintro ⟨hx, hy⟩
    refine ⟨hx, _, hy, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

private theorem ind_eq {G : Type} [Group G] (K : Subgroup G) (g : G) :
    Formalism.UG.dosetInd ℂ K g = G3.ind ℂ K g := by
  rfl

private theorem smooth_iso {A B C : Scheme.{0}} (e : A ≅ B) (s : B ⟶ C) (n : ℕ)
    (h : SmoothOfRelativeDimension n s) : SmoothOfRelativeDimension n (e.hom ≫ s) := by
  haveI := h
  have := smoothOfRelativeDimension_comp (n := 0) (m := n) e.hom s
  rwa [Nat.zero_add] at this

end UpperTheory.Gal.FixZ

open UpperTheory.Gal UpperTheory.Gal.FixZ in
theorem UpperTheory.Gal.FixZ.bridge_of :
    UpperTheory.Gal.FixZ.TrFEt → UpperTheory.Gal.FixZ.AlFEt → UpperTheory.Gal.FixZ.LegOf → UpperTheory.Gal.FixZ.WtEq → UpperTheory.Gal.FixZ.TanIso → UpperTheory.Gal.FixZ.DimUniq → UpperTheory.Gal.FixZ.CxFinOf → UpperTheory.Gal.FixZ.Bridge := by
  intro hTr hAl hLeg hWt hTan hDim hCx h0 hZ p _ D G L hSc gb hStd i₀ v hv k T N' N hdvd d hsm h a b hreg α hα
  have hτ : ∀ i, D.tau i = D.tau i₀ := fun i => by
    have : Subsingleton (Fin D.a) := by rw [hSc.a1]; infer_instance
    rw [Subsingleton.elim i i₀]
  have hAdm : ∀ u ∈ L.KN N'.1, h * u * h⁻¹ ∈ L.KN N.1 := fun u hu => by
    have := b.2 u (by rw [T.K_eq]; exact hu)
    rwa [T.K_eq] at this
  have hLe : L.KN N'.1 ≤ L.KN N.1 := fun u hu => by
    have := a.2 u (by rw [T.K_eq]; exact hu)
    rw [T.K_eq] at this
    simpa using this
  have hLev : W2.LevOk L N.1 N'.1 h := ⟨N.2.1, N.2.2, N'.2.1, N'.2.2, hdvd, hAdm⟩
  obtain ⟨c₁, hc₁, -⟩ := hLeg p D G L gb k T N' N 1 a
  obtain ⟨c₂, -, hc₂'⟩ := hLeg p D G L gb k T N' N h b
  have hc₂ := hc₂' α
  have hregZ : ∀ g, h * g ∈ L.KN N.1 → GlobalTheory.LKCx.RegAf G g := fun g hg => hreg g (by
    have hm : g ∈ DoubleCoset.doubleCoset h⁻¹ (L.KN N.1 : Set G.GAf) (L.KN N.1) :=
      DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, h * g, hg, by simp⟩
    rw [G3.ind, Set.indicator_of_mem hm]
    exact one_ne_zero)
  have heq : ∀ M : Lv p, (T.e M).hom ≫ W2.sZ (T.M M) k = qAt T M := T.e_q
  have hpw : c₁.pw k = (T.e N').inv ≫ T.X.tr _ _ 1 a.1 a.2 ≫ (T.e N).hom := by
    rw [hc₁, Iso.inv_hom_id_assoc]
  have htw : c₂.tw α = (T.e N').inv ≫ leg T N' N h b α ≫ (T.e N).hom := by
    rw [hc₂, Iso.inv_hom_id_assoc]
  have hEt : Etale (c₁.pw k) := by
    haveI := T.X.etale (T.lev N') (T.lev N) a.1 a.2
    rw [hpw]
    infer_instance
  have h₁ : c₁.pw k ≫ W2.sZ (T.M N) k = W2.sZ (T.M N') k := by
    rw [hpw, Category.assoc, Category.assoc, heq N, T.X.tr_q, Iso.inv_comp_eq]
    exact (heq N').symm
  have h₂ : c₂.tw α ≫ W2.sZ (T.M N) k = W2.sZ (T.M N') k := by
    rw [htw, Category.assoc, Category.assoc, heq N, LocalSmoothExtension.leg_q, Iso.inv_comp_eq]
    exact (heq N').symm
  obtain ⟨-, -, -, -, -, hfin, hone, -⟩ := h0 p D G L hSc.a1 hSc.m1 v hv (D.tau i₀) hτ gb hStd N.1 N'.1 h hLev
    (T.M N) (T.M N') c₁ c₂ hregZ k α (fun s => (hα s).2) hEt h₁ h₂
  obtain ⟨hsm₀, Fx, At, hFx, hAt, hSum⟩ := hZ p D G L hSc.a1 hSc.m1 v hv (D.tau i₀) hτ gb hStd N.1 N'.1 h hLev
    (T.M N) (T.M N') c₁ c₂ hregZ k α (fun s => (hα s).2) hEt h₁ h₂
  have hRHS : ∀ y : ℂ, ∑ x ∈ Fx, W2.lefTerm (At x) y =
      (((L.KN N'.1).relIndex (G3.lev (L.KN N.1) h) : ℕ) : ℂ) *
        GlobalTheory.RootSumWeights.cxTotalM G v (cW L i₀ v α y) (L.KN N.1) (G3.ind ℂ (L.KN N.1) h⁻¹) (LocalSmoothExtension.Kp G) (LocalSmoothExtension.oneP G) := by
    intro y
    rw [hSum y, hWt p D G L hSc.a1 i₀ v hv k α y, lev_eq, ind_eq]
    rfl
  have hFT := hTr p D G L gb k T N' N h b.1 b.2
  have hFA := hAl p D G L gb k T N α (fun s => (hα s).1)
  have hlegF : IsFinite (leg T N' N h b α) := by
    haveI := hFT.1
    haveI := hFA.1
    unfold leg
    infer_instance
  have hlegE : Etale (leg T N' N h b α) := by
    haveI := hFT.2
    haveI := hFA.2
    unfold leg
    infer_instance
  refine ⟨hCx p G v (L.KN N.1) (L.KN N'.1) h hLe hAdm hfin hone, hlegF, hlegE, ?_⟩
  by_cases hne : Nonempty (T.X.Z (T.lev N))
  · have hsm₁ : SmoothOfRelativeDimension (D.n - 1 + k * D.g) (qAt T N) := by
      rw [← heq N]
      exact smooth_iso _ _ _ hsm₀
    have hd : d = D.n - 1 + k * D.g := hDim _ (qAt T N) _ _ hsm hsm₁ hne
    subst hd
    obtain ⟨E, -, hE2, hE3⟩ := hTan _ _ _ _ (qAt T N) (qAt T N') (W2.sZ (T.M N) k) (W2.sZ (T.M N') k) (T.e N) (T.e N')
      (heq N) (heq N') (D.n - 1 + k * D.g) (T.X.tr _ _ 1 a.1 a.2) (leg T N' N h b α) (c₁.pw k) (c₂.tw α)
      (T.X.tr_q _ _ 1 a.1 a.2) (LocalSmoothExtension.leg_q T N' N h b α) h₁ h₂ hc₁ hc₂
    have hmem : ∀ x, x ∈ Fx.map E.symm.toEmbedding ↔ E x ∈ Fx := fun x => by
      rw [Finset.mem_map_equiv, Equiv.symm_symm]
    refine ⟨Fx.map E.symm.toEmbedding, fun x => At (E x), fun x => ?_, fun x hx => ?_, fun y => ?_⟩
    · rw [hmem, hFx, hE2]
    · have := hAt _ ((hmem x).1 hx)
      exact ⟨hE3 x _ this.1, this.2⟩
    · rw [← hRHS y, Finset.sum_map]
      simp
  · have hpt : ∀ _ : Sp ℂ ⟶ T.X.Z (T.lev N'), False := fun x =>
      hne ⟨(x ≫ T.X.tr _ _ 1 a.1 a.2) (IsLocalRing.closedPoint ℂ)⟩
    have hFx0 : Fx = ∅ := Finset.eq_empty_of_forall_notMem fun x _ => hpt (x.1 ≫ (T.e N').inv)
    refine ⟨∅, fun _ => 0, fun x => (hpt x.1).elim, fun x => (hpt x.1).elim, fun y => ?_⟩
    rw [← hRHS y, hFx0, Finset.sum_empty, Finset.sum_empty]

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PTrFEt
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo (KS Lv Integ)

namespace UpperTheory.Gal.FixZ

private lemma tr_comp {B : Scheme.{0}} {Γ : Type} [Group Γ] (X : G3.Tower B Γ) {i j m : X.ι} {h h' g : Γ} (a b a' b')
    (e : h' * h = g) (c d) : X.tr i j h a b ≫ X.tr j m h' a' b' = X.tr i m g c d := by
  subst e
  exact X.tr_mul i j m h h' a b a' b' c d

private lemma lofp_cancel {A B S : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ S) [LocallyOfFinitePresentation (f ≫ g)]
    [LocallyOfFiniteType g] : LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation)
    (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finitePresentation_holdsForLocalizationAway).1]
  intro x
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g (f x))) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW : U ≤ g ⁻¹ᵁ W⟩ :=
    B.isBasis_affineOpens.exists_subset_of_mem_open hxW (g ⁻¹ᵁ W).isOpen
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V ≤ f ⁻¹ᵁ U⟩ :=
    A.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).isOpen
  refine ⟨⟨U, hU⟩, ⟨V, hV⟩, hxV, hVU, RingHom.FinitePresentation.of_comp_finiteType
    (g.appLE W U hUW).hom ?_ (g.finiteType_appLE hW hU hUW)⟩
  rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
  exact (f ≫ g).finitePresentation_appLE hW hV _

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {gb : GBase D.toG ℂ} {k : ℕ}

private lemma q_props (hP : G3.PowSm) (T : KS L gb k) (N : Lv p) :
    Smooth (T.X.q (T.lev N)) ∧ IsSeparated (T.X.q (T.lev N)) := by
  obtain ⟨h1, h2, -⟩ := hP p D ℂ gb N (T.M N) k
  rw [← T.e_q N]
  exact ⟨inferInstance, inferInstance⟩

private lemma tr_props (hP : G3.PowSm) (T : KS L gb k) (N' N : Lv p) (h : G.GAf) (a b) :
    IsSeparated (T.X.tr (T.lev N') (T.lev N) h a b) ∧ LocallyOfFinitePresentation (T.X.tr (T.lev N') (T.lev N) h a b) := by
  obtain ⟨s1, s2⟩ := q_props hP T N'
  obtain ⟨s3, s4⟩ := q_props hP T N
  have e := T.X.tr_q (T.lev N') (T.lev N) h a b
  constructor
  · rw [← e] at s2
    exact IsSeparated.of_comp _ (T.X.q (T.lev N))
  · rw [← e] at s1
    exact lofp_cancel _ (T.X.q (T.lev N))

private lemma scal_fe (hS : TrScal) (T : KS L gb k) (P Q : Lv p) (d : ℕ) (z : G.GAf) (hd : 0 < d) (hc : d.Coprime p)
    (hz : IsScal L d z) (a b) (a₁ : (1 : G.GAf) ∈ T.X.Δ)
    (b₁ : ∀ u ∈ T.X.K (T.lev P), 1 * u * 1⁻¹ ∈ T.X.K (T.lev Q)) (a₂ : z ∈ T.X.Δ)
    (b₂ : ∀ u ∈ T.X.K (T.lev Q), z * u * z⁻¹ ∈ T.X.K (T.lev Q)) :
    IsFinite (T.X.tr (T.lev P) (T.lev Q) z a b) ∧ Etale (T.X.tr (T.lev P) (T.lev Q) z a b) := by
  have e := tr_comp T.X a₁ b₁ a₂ b₂ (mul_one z) a b
  obtain ⟨f1, f2⟩ := hS p D G L gb k T Q d z hd hc hz a₂ b₂
  have f3 := T.X.fin _ _ a₁ b₁
  have f4 := T.X.etale _ _ a₁ b₁
  rw [← e]
  exact ⟨inferInstance, inferInstance⟩

theorem trFEt_of : G3.PowSm → ScalEx → TrScal → EtCancel → DescEt → DescFin → TrFEt := by
  classical
  intro hP hSc hTS hEC hDE hDF p _ D G L gb k T N' N h a b
  obtain ⟨d, z, hd, hc, hz, hzi, hzh⟩ := hSc p D G L h ((T.Δ_eq h).1 a)
  have hcen := hz.1
  have zΔ : z ∈ T.X.Δ := (T.Δ_eq z).2 hzi
  have h'Δ : z * h⁻¹ ∈ T.X.Δ := (T.Δ_eq _).2 hzh
  have oΔ : (1 : G.GAf) ∈ T.X.Δ := one_mem _
  have zc : ∀ u : G.GAf, z * u * z⁻¹ = u := fun u => by rw [hcen u, mul_inv_cancel_right]
  have e1 : h * (z * h⁻¹) = z := by rw [← mul_assoc, ← hcen h, mul_inv_cancel_right]
  have e2 : z * h⁻¹ * h = z := by rw [inv_mul_cancel_right]

  obtain ⟨m, -, -, hm⟩ := T.X.deep (T.lev N') {(T.lev N, 1), (T.lev N', z * h⁻¹)}
  obtain ⟨m', -, -, hm'⟩ := T.X.deep (T.lev N') {(m, h), (T.lev N', 1)}
  obtain ⟨M, rfl⟩ := T.lev.surjective m
  obtain ⟨M', rfl⟩ := T.lev.surjective m'
  have b1 : ∀ u ∈ T.X.K (T.lev M), 1 * u * 1⁻¹ ∈ T.X.K (T.lev N) := hm (T.lev N, 1) (by simp)
  have b2 : ∀ u ∈ T.X.K (T.lev M), z * h⁻¹ * u * (z * h⁻¹)⁻¹ ∈ T.X.K (T.lev N') := hm (T.lev N', z * h⁻¹) (by simp)
  have b3 : ∀ u ∈ T.X.K (T.lev M'), h * u * h⁻¹ ∈ T.X.K (T.lev M) := hm' (T.lev M, h) (by simp)
  have b4 : ∀ u ∈ T.X.K (T.lev M'), 1 * u * 1⁻¹ ∈ T.X.K (T.lev N') := hm' (T.lev N', 1) (by simp)
  have b5 : ∀ u ∈ T.X.K (T.lev M), z * u * z⁻¹ ∈ T.X.K (T.lev N) := fun u hu => by
    have := b1 u hu
    simpa [zc] using this
  have b6 : ∀ u ∈ T.X.K (T.lev M'), z * u * z⁻¹ ∈ T.X.K (T.lev N') := fun u hu => by
    have := b4 u hu
    simpa [zc] using this
  have b7 : ∀ u ∈ T.X.K (T.lev N), z * u * z⁻¹ ∈ T.X.K (T.lev N) := fun u hu => by rwa [zc]
  have b8 : ∀ u ∈ T.X.K (T.lev N'), z * u * z⁻¹ ∈ T.X.K (T.lev N') := fun u hu => by rwa [zc]
  have b9 : ∀ u ∈ T.X.K (T.lev M'), h * u * h⁻¹ ∈ T.X.K (T.lev N) := fun u hu => by
    have := b1 _ (b3 u hu)
    simpa using this

  have c1 : T.X.tr _ _ (z * h⁻¹) h'Δ b2 ≫ T.X.tr _ _ h a b = T.X.tr _ _ z zΔ b5 :=
    tr_comp T.X h'Δ b2 a b e1 zΔ b5
  have c2 : T.X.tr _ _ h a b3 ≫ T.X.tr _ _ (z * h⁻¹) h'Δ b2 = T.X.tr _ _ z zΔ b6 :=
    tr_comp T.X a b3 h'Δ b2 e2 zΔ b6
  obtain ⟨f1, f2⟩ := scal_fe hTS T M N d z hd hc hz zΔ b5 oΔ b1 zΔ b7
  obtain ⟨f3, f4⟩ := scal_fe hTS T M' N' d z hd hc hz zΔ b6 oΔ b4 zΔ b8
  rw [← c1] at f1 f2
  rw [← c2] at f3 f4
  obtain ⟨-, s1⟩ := tr_props hP T M N' (z * h⁻¹) h'Δ b2
  have t1 : LocallyOfFiniteType (T.X.tr _ _ (z * h⁻¹) h'Δ b2) := inferInstance
  obtain ⟨f5, f6⟩ := hEC _ _ _ _ (T.X.tr _ _ h a b3) (T.X.tr _ _ (z * h⁻¹) h'Δ b2) (T.X.tr _ _ h a b) t1 f3 f4 f1 f2

  have c3 : T.X.tr _ _ 1 oΔ b4 ≫ T.X.tr _ _ h a b = T.X.tr _ _ h a b9 :=
    tr_comp T.X oΔ b4 a b (mul_one h) a b9
  have c4 : T.X.tr _ _ h a b3 ≫ T.X.tr _ _ 1 oΔ b1 = T.X.tr _ _ h a b9 :=
    tr_comp T.X a b3 oΔ b1 (one_mul h) a b9
  have g1 := T.X.fin _ _ oΔ b1
  have g2 := T.X.etale _ _ oΔ b1
  have g3 : IsFinite (T.X.tr _ _ 1 oΔ b4 ≫ T.X.tr _ _ h a b) := by
    rw [c3, ← c4]; infer_instance
  have g4 : Etale (T.X.tr _ _ 1 oΔ b4 ≫ T.X.tr _ _ h a b) := by
    rw [c3, ← c4]; infer_instance
  obtain ⟨s2, s3⟩ := tr_props hP T N' N h a b
  have g5 := hDE _ _ _ _ _ (T.X.etale _ _ oΔ b4) (T.X.onto _ _ oΔ b4) s3 g4
  exact ⟨hDF _ _ _ _ _ (T.X.onto _ _ oΔ b4) s2 g5 g3, g5⟩

end UpperTheory.Gal.FixZ

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PTanIso
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential

namespace UpperTheory.Gal.FixZ

private def secEquiv {Y Y' : Scheme.{0}} {t : Y ⟶ Sp ℂ} {t' : Y' ⟶ Sp ℂ} (e : Y ≅ Y')
    (ht : e.hom ≫ t' = t) (V : Y'.Opens) : Sec t' V ≃ₐ[ℂ] Sec t (e.hom ⁻¹ᵁ V) :=
  AlgEquiv.ofBijective
    { appSec t' t e.hom V with
      commutes' := fun r => (semiHom_appSec ht V).map_algebraMap r }
    (ConcreteCategory.bijective_of_isIso (e.hom.app V))

private theorem eq_self_of_fix_D_of_linear_kaehler {A : Type} [CommRing A] [Algebra ℂ A] (g : Ω[A⁄ℂ] →ₗ[ℂ] Ω[A⁄ℂ])
    (hD : ∀ a, g (D ℂ A a) = D ℂ A a) (hs : ∀ (a : A) (ω : Ω[A⁄ℂ]), g (a • ω) = a • g ω)
    (ω : Ω[A⁄ℂ]) : g ω = ω := by
  have hω : ω ∈ Submodule.span A (Set.range (D ℂ A)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact hD a
  | zero => exact map_zero g
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | smul a x _ hx => rw [hs, hx]

private theorem exists_kaehler_map_D_of_algHom {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) :
    ∃ Ψ : Ω[A⁄ℂ] →ₗ[ℂ] Ω[B⁄ℂ], (∀ a, Ψ (D ℂ A a) = D ℂ B (f a)) ∧
      ∀ (a : A) (ω : Ω[A⁄ℂ]), Ψ (a • ω) = f a • Ψ ω := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  haveI : SMulCommClass ℂ A B := ⟨fun r a b => by
    change r • (f a * b) = f a * (r • b)
    rw [mul_smul_comm]⟩
  refine ⟨(KaehlerDifferential.map ℂ ℂ A B).restrictScalars ℂ, fun a => ?_, fun a ω => ?_⟩
  · exact KaehlerDifferential.map_D ℂ ℂ A B a
  · rw [LinearMap.restrictScalars_apply, LinearMap.map_smul, ← algebraMap_smul (A := B) a]
    rfl

private theorem exists_kaehler_equiv_D_of_algEquiv {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A ≃ₐ[ℂ] B) :
    ∃ Ψ : Ω[A⁄ℂ] ≃ₗ[ℂ] Ω[B⁄ℂ], (∀ a, Ψ (D ℂ A a) = D ℂ B (f a)) ∧
      ∀ (a : A) (ω : Ω[A⁄ℂ]), Ψ (a • ω) = f a • Ψ ω := by
  obtain ⟨Ψ, h1, h2⟩ := exists_kaehler_map_D_of_algHom (f : A →ₐ[ℂ] B)
  obtain ⟨Φ, g1, g2⟩ := exists_kaehler_map_D_of_algHom (f.symm : B →ₐ[ℂ] A)
  have l : ∀ ω, Φ (Ψ ω) = ω := eq_self_of_fix_D_of_linear_kaehler (Φ ∘ₗ Ψ)
    (fun a => by simp [h1, g1]) (fun a ω => by simp [h2, g2])
  have r : ∀ η, Ψ (Φ η) = η := eq_self_of_fix_D_of_linear_kaehler (Ψ ∘ₗ Φ)
    (fun a => by simp [h1, g1]) (fun a ω => by simp [h2, g2])
  exact ⟨LinearEquiv.ofLinear Ψ Φ (LinearMap.ext r) (LinearMap.ext l), h1, h2⟩

private theorem valR_comp_eq_valR_app {X W : Scheme} (x : Sp ℂ ⟶ X) (f : X ⟶ W) (V : W.Opens)
    (g : Γ(W, V)) :
    valR (x ≫ f) V g = valR x (f ⁻¹ᵁ V) (f.app V g) := by
  unfold valR
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (f ⁻¹ᵁ V)
  · have h' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ V := h
    rw [dite_eq_left h', dite_eq_left h]
    simp [Scheme.Hom.comp_appLE]
  · have h' : ¬ ⊤ ≤ (x ≫ f) ⁻¹ᵁ V := h
    rw [dite_eq_right h', dite_eq_right h]

private theorem preimage_le_preimage_preimage_of_comm_iso {Y Y' Z Z' : Scheme} (eY : Y ≅ Y') (eZ : Z ≅ Z') (c : Y ⟶ Z)
    (c' : Y' ⟶ Z') (hc : c ≫ eZ.hom = eY.hom ≫ c') (U' : Z'.Opens) (V' : Y'.Opens)
    (h : V' ≤ c' ⁻¹ᵁ U') : eY.hom ⁻¹ᵁ V' ≤ c ⁻¹ᵁ eZ.hom ⁻¹ᵁ U' := by
  rw [← Scheme.Hom.comp_preimage, hc, Scheme.Hom.comp_preimage]
  exact fun p hp => h hp

private theorem appSec_res_appSec_eq_of_comm_iso {Y Y' Z Z' : Scheme} {s : Z ⟶ Sp ℂ} {t : Y ⟶ Sp ℂ}
    {s' : Z' ⟶ Sp ℂ} {t' : Y' ⟶ Sp ℂ} (eY : Y ≅ Y') (eZ : Z ≅ Z') (c : Y ⟶ Z) (c' : Y' ⟶ Z')
    (hc : c ≫ eZ.hom = eY.hom ≫ c') (U' : Z'.Opens) (V' : Y'.Opens) (hV' : V' ≤ c' ⁻¹ᵁ U')
    (hV : eY.hom ⁻¹ᵁ V' ≤ c ⁻¹ᵁ eZ.hom ⁻¹ᵁ U') (τ : Sec s' U') :
    appSec t' t eY.hom V' (Sec.res t' hV' (appSec s' t' c' U' τ)) =
      Sec.res t hV (appSec s t c (eZ.hom ⁻¹ᵁ U') (appSec s' s eZ.hom U' τ)) := by
  have key : ∀ (g₁ g₂ : Y ⟶ Z') (_ : g₁ = g₂) (W : Y.Opens) (e₁ : W ≤ g₁ ⁻¹ᵁ U')
      (e₂ : W ≤ g₂ ⁻¹ᵁ U'), g₁.appLE U' W e₁ = g₂.appLE U' W e₂ := by
    rintro _ _ rfl _ _ _; rfl
  have e1 : eY.hom ⁻¹ᵁ V' ≤ (eY.hom ≫ c') ⁻¹ᵁ U' := by
    rw [Scheme.Hom.comp_preimage]; exact fun p hp => hV' hp
  have e2 : eY.hom ⁻¹ᵁ V' ≤ (c ≫ eZ.hom) ⁻¹ᵁ U' := by
    rw [Scheme.Hom.comp_preimage]; exact hV
  have L : appSec t' t eY.hom V' (Sec.res t' hV' (appSec s' t' c' U' τ)) =
      (eY.hom ≫ c').appLE U' _ e1 τ := by
    change eY.hom.app V' (Y'.presheaf.map (homOfLE hV').op (c'.app U' τ)) = _
    rw [Scheme.Hom.comp_appLE, Scheme.Hom.app_eq_appLE]
    simp only [CommRingCat.comp_apply]
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  have R : Sec.res t hV (appSec s t c (eZ.hom ⁻¹ᵁ U') (appSec s' s eZ.hom U' τ)) =
      (c ≫ eZ.hom).appLE U' _ e2 τ := by
    change Y.presheaf.map (homOfLE hV).op (c.app _ (eZ.hom.app U' τ)) = _
    rw [Scheme.Hom.comp_appLE]
    rfl
  rw [L, R, key _ _ hc.symm]

theorem tanIso_of :
    UpperTheory.Gal.FixZ.TanIso := by
  intro Z Y Z' Y' s t s' t' eZ eY hs ht d c₁ c₂ c₁' c₂' h₁ h₂ h₁' h₂' hc₁ hc₂
  refine ⟨?E, ?_⟩
  case E =>
    unfold CxPts Points.PtsOver
    exact
      { toFun := fun x => ⟨x.1 ≫ eY.hom, by rw [Category.assoc, ht]; exact x.2⟩
        invFun := fun y => ⟨y.1 ≫ eY.inv, by rw [Category.assoc, ← ht, eY.inv_hom_id_assoc]; exact y.2⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun y => Subtype.ext (by simp) }
  refine ⟨fun x => rfl, fun x => ?_, fun x A hT => ?_⟩
  · change x.1 ≫ c₁ = x.1 ≫ c₂ ↔ (x.1 ≫ eY.hom) ≫ c₁' = (x.1 ≫ eY.hom) ≫ c₂'
    rw [Category.assoc, Category.assoc, ← hc₁, ← hc₂, ← Category.assoc, ← Category.assoc x.1,
      cancel_mono]
  · obtain ⟨U', V', hV1', hV2', τ, hx, hU', hV', φ', hsm, hd1, hd2, hker⟩ := hT
    set σ := secEquiv eY ht V' with hσ
    have hσa : ∀ g, σ g = appSec t' t eY.hom V' g := fun g => rfl
    have EV : ∀ g : Sec t' V', CxPts.ev t' (RingHom.id ℂ) V' g
        (⟨x.1 ≫ eY.hom, by rw [Category.assoc, ht]; exact x.2⟩ : CxPts t' (RingHom.id ℂ)) =
        CxPts.ev t (RingHom.id ℂ) (eY.hom ⁻¹ᵁ V') (σ g) x := fun g =>
      valR_comp_eq_valR_app x.1 eY.hom V' g
    obtain ⟨Ψ, hΨD, hΨs⟩ := exists_kaehler_equiv_D_of_algEquiv σ.symm
    have hW1 := preimage_le_preimage_preimage_of_comm_iso eY eZ c₁ c₁' hc₁ U' V' hV1'
    have hW2 := preimage_le_preimage_preimage_of_comm_iso eY eZ c₂ c₂' hc₂ U' V' hV2'
    have q1 : ∀ l, σ.symm (Sec.res t hW1 (appSec s t c₁ (eZ.hom ⁻¹ᵁ U')
        (appSec s' s eZ.hom U' (τ l)))) = Sec.res t' hV1' (appSec s' t' c₁' U' (τ l)) := fun l =>
      σ.injective (by rw [AlgEquiv.apply_symm_apply, hσa, appSec_res_appSec_eq_of_comm_iso eY eZ c₁ c₁' hc₁ U' V' hV1' hW1 (τ l)])
    have q2 : ∀ l, σ.symm (Sec.res t hW2 (appSec s t c₂ (eZ.hom ⁻¹ᵁ U')
        (appSec s' s eZ.hom U' (τ l)))) = Sec.res t' hV2' (appSec s' t' c₂' U' (τ l)) := fun l =>
      σ.injective (by rw [AlgEquiv.apply_symm_apply, hσa, appSec_res_appSec_eq_of_comm_iso eY eZ c₂ c₂' hc₂ U' V' hV2' hW2 (τ l)])
    refine ⟨eZ.hom ⁻¹ᵁ U', eY.hom ⁻¹ᵁ V', hW1, hW2, fun l => appSec s' s eZ.hom U' (τ l), hx,
      hU'.preimage_of_isIso eZ.hom, hV'.preimage_of_isIso eY.hom, φ' ∘ₗ Ψ.toLinearMap,
      ?_, ?_, ?_, ?_⟩
    · intro b ω
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hΨs, hsm]
      erw [EV]
      rw [AlgEquiv.apply_symm_apply]
    · intro l
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hΨD, q1]
      exact hd1 l
    · intro j
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hΨD, q2]
      exact hd2 j
    · intro ω hω
      obtain ⟨m, b, ω', hb, hsum⟩ := hker (Ψ ω) hω
      refine ⟨m, fun i => σ (b i), fun i => Ψ.symm (ω' i), fun i => ?_, ?_⟩
      · rw [← EV]; exact hb i
      · apply Ψ.injective
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hsum, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hΨs, AlgEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

end UpperTheory.Gal.FixZ

end
end
