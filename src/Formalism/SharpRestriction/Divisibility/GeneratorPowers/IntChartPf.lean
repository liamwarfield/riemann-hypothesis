module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDPf

@[expose] public section

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartPf
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem intChart_of_cut (hA : ChartDataGSt) (hB : FrameSt) (hC : FBIdSt) (hGF : GlobalFnsSt) :
    IntChartStatement := by
  intro E _ _ _ H V _ _ _ hc t hprop κ _ tg htan hbas _ hstar
  obtain ⟨d, G, A, uvec, x, hd, hu, hch⟩ := hA E H (Sp V) t V (𝟙 (Sp V)) tg htan hbas
  obtain ⟨e, wP, ph1, ph2, sy, ad, hfr, hpr, htr, hfa, had, hrig⟩ :=
    hB E H (Sp V) t V (𝟙 (Sp V)) d G A κ tg uvec x hch
  have hPow := globalFnsDvr_of_globalFns hGF E H V hc t hprop
  obtain ⟨hax, hr⟩ := hC E H (Sp V) t hPow hstar V (𝟙 (Sp V)) d G A κ tg uvec x e ph1 ph2 sy ad hch hfr hfa had
  refine ⟨d, mkFB G A ph1 ph2 sy ad hax hr, uvec, x, e, wP, hd, hu, hch, hfr, hpr, htr, hrig, fun k F => ?_⟩
  exact germSt_holds E H (Sp V) t V (𝟙 (Sp V)) d G.F A.act κ tg uvec x ph1 ph2 sy ad e wP hch hfr hpr htr k F

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBSer
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

attribute [local instance] Over.cartesianMonoidalCategory

section JetSubst

variable {S : Type} [CommRing S] {κ κ' : Type}

theorem jetSubstP_congr (m : ℕ) (φ ψ : κ → MvPolynomial κ' S) (h : ∀ i, φ i - ψ i ∈ orig S κ' ^ (m + 1)) :
    (jetSubstP m φ : Jet S κ m →ₐ[S] Jet S κ' m) = jetSubstP m ψ := by
  unfold jetSubstP jetMap
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk]
  rw [Ideal.Quotient.eq]
  have hc : MvPolynomial.constantCoeff (φ i) = MvPolynomial.constantCoeff (ψ i) := by
    have h1 : φ i - ψ i ∈ orig S κ' := Ideal.pow_le_self (Nat.succ_ne_zero m) (h i)
    have h2 : orig S κ' ≤ RingHom.ker (MvPolynomial.constantCoeff (R := S) (σ := κ')) := by
      unfold orig
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      simp
    have h3 := h2 h1
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h3
    exact h3
  rw [hc]
  convert h i using 1
  ring

theorem jetSubstP_trunc (m : ℕ) (φ : κ → MvPolynomial κ' S) :
    (jetTrunc : Jet S κ' (m + 1) →ₐ[S] Jet S κ' m).comp (jetSubstP (m + 1) φ) =
      (jetSubstP m φ).comp (jetTrunc : Jet S κ (m + 1) →ₐ[S] Jet S κ m) := by
  unfold jetSubstP jetMap jetTrunc liftJet
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  rfl

theorem rename_mem_orig_pow {κ'' : Type} (f : κ' → κ'') (n : ℕ) {p : MvPolynomial κ' S} (hp : p ∈ orig S κ' ^ n) :
    MvPolynomial.rename f p ∈ orig S κ'' ^ n := by
  have hle : Ideal.map (MvPolynomial.rename f : MvPolynomial κ' S →ₐ[S] MvPolynomial κ'' S) (orig S κ') ≤
      orig S κ'' := by
    unfold orig
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨f j, (MvPolynomial.rename_X f j).symm⟩
  have hm := Ideal.mem_map_of_mem (MvPolynomial.rename f : MvPolynomial κ' S →ₐ[S] MvPolynomial κ'' S) hp
  rw [Ideal.map_pow] at hm
  exact Ideal.pow_right_mono hle n hm

theorem psIn_succ_sub {d n n' : ℕ} (m : ℕ) (r : Fin n → Fin n') (g : MvPowerSeries (Fin n × Fin d) S) :
    psIn d (m + 1) r g - psIn d m r g ∈ orig S (Fin n' × Fin d) ^ (m + 1) := by
  unfold psIn
  rw [← map_sub]
  apply rename_mem_orig_pow
  unfold psTrunc
  have memD : ∀ (k : ℕ) (e : (Fin n × Fin d) →₀ ℕ),
      e ∈ (degLE k : Finset ((Fin n × Fin d) →₀ ℕ)) ↔ (e.sum fun _ a => a) ≤ k := by
    intro k e
    unfold degLE
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      refine ⟨⟨fun i => ⟨e i, ?_⟩, ?_⟩, h⟩
      · have hle : e i ≤ e.sum fun _ a => a := by
          rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
          exact Finset.single_le_sum (f := fun j => e j) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      · ext i
        simp
  have monoMem : ∀ (k : ℕ) (e : (Fin n × Fin d) →₀ ℕ) (c : S), k ≤ (e.sum fun _ a => a) →
      MvPolynomial.monomial e c ∈ orig S (Fin n × Fin d) ^ k := by
    intro k e c hk
    have hmem : (e.prod fun i a => MvPolynomial.X i ^ a) ∈ orig S (Fin n × Fin d) ^ (e.sum fun _ a => a) := by
      simp only [Finsupp.prod, Finsupp.sum]
      rw [← Finset.prod_pow_eq_pow_sum]
      apply Ideal.prod_mem_prod
      intro i _
      apply Ideal.pow_mem_pow
      unfold orig
      exact Ideal.subset_span ⟨i, rfl⟩
    rw [MvPolynomial.monomial_eq]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hk hmem)
  have hsub : (degLE m : Finset ((Fin n × Fin d) →₀ ℕ)) ⊆ degLE (m + 1) := by
    intro e he
    rw [memD] at he ⊢
    omega
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  apply Ideal.sum_mem
  intro e he
  rw [Finset.mem_sdiff, memD, memD] at he
  apply monoMem
  omega

end JetSubst

section Series

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ)

theorem val_scale {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (u : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι)
    (hJ : Good t.PP.L z J) : val (scaleGenG t φ ε u g) r z J = gm r z ⊤ u * val g r z J := by
  unfold scaleGenG val gm
  have hz : r z ∈ t.PP.L.wchart φ fun k => J (r ≫ φ k) := by
    unfold Good at hJ
    unfold LB.wchart
    show r z ∈ (⋂ k, ⇑(φ k) ⁻¹' ↑(t.PP.L.U (J (r ≫ φ k))) : Set _)
    rw [Set.mem_iInter]
    intro k
    have hk := hJ (r ≫ φ k)
    simpa using hk
  rw [dite_eq_left hz, dite_eq_left (show r z ∈ (⊤ : Y.Opens) from trivial)]
  dsimp only
  refine (MonoidHom.map_mul _ _ _).trans ?_
  congr 1
  apply Units.ext
  unfold pullU res
  have hz' : z ∈ r ⁻¹ᵁ (t.PP.L.wchart φ fun k => J (r ≫ φ k)) := hz
  have ht : z ∈ r ⁻¹ᵁ (⊤ : Y.Opens) := trivial
  have key := congrArg (fun f => CommRingCat.Hom.hom f (u : Γ(Y, ⊤)))
    (show Y.presheaf.map (homOfLE (le_top : t.PP.L.wchart φ (fun k => J (r ≫ φ k)) ≤ ⊤)).op ≫
        Scheme.Hom.app r (t.PP.L.wchart φ fun k => J (r ≫ φ k)) ≫
        Z.presheaf.germ (r ⁻¹ᵁ t.PP.L.wchart φ fun k => J (r ≫ φ k)) z hz' =
        Scheme.Hom.app r ⊤ ≫ Z.presheaf.germ (r ⁻¹ᵁ ⊤) z ht by
      rw [Scheme.Hom.naturality_assoc, TopCat.Presheaf.germ_res]
      all_goals rfl)
  first
    | exact key
    | (simp only [CommRingCat.hom_comp, RingHom.comp_apply] at key
       simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
       exact key)

abbrev ρn (n m : ℕ) : jOG x0 d m n ⟶ jOG x0 d (m + 1) n :=
  homAt x0 (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] Jet S (Fin n × Fin d) m)

theorem exists_series {n : ℕ} {K K' : Type} [Fintype K] [Fintype K']
    (φ : ∀ m, K → ((jOG x0 d m n).left ⟶ t.G.left)) (ε : K → ℤ)
    (φ' : ∀ m, K' → ((jOG x0 d m n).left ⟶ t.G.left)) (ε' : K' → ℤ)
    (A : ∀ m, LB.Gen (LB.LinComb t.PP.L (φ m) ε)) (hA : ∀ m, (A m).IsGen)
    (B : ∀ m, LB.Gen (LB.LinComb t.PP.L (φ' m) ε')) (hB : ∀ m, (B m).IsGen)
    (hF : ∀ m, FormEq (φ m) ε (φ' m) ε')
    (hAt : ∀ m y J, Good t.PP.L y J → val (A (m + 1)) (ρn x0 d n m).left y J = val (A m) (𝟙 _) y J)
    (hBt : ∀ m y J, Good t.PP.L y J → val (B (m + 1)) (ρn x0 d n m).left y J = val (B m) (𝟙 _) y J) :
    ∃ ph : MvPowerSeries (Fin n × Fin d) S, ∀ m, ∃ u : (Jet S (Fin n × Fin d) m)ˣ,
      (u : Jet S (Fin n × Fin d) m) = psJet m ph ∧
      LB.Gen.Corr t.PP.L _ _ _ _ (A m) (scaleGenG t _ _ (unitΓ u) (B m)) := by
  have hL := t.PP.isLB
  choose U hU using fun m => exists_ratio t.PP.L hL (hF m) (A m) (hA m) (B m) (hB m)
  have hv : ∀ m, ∃ v : (Jet S (Fin n × Fin d) m)ˣ, unitΓ v = U m := fun m =>
    ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of (Jet S (Fin n × Fin d) m))).hom.hom.toMonoidHom (U m),
      Units.ext (congrArg (fun f => CommRingCat.Hom.hom f (U m).val)
        (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of (Jet S (Fin n × Fin d) m)))))⟩
  choose v hv using hv
  have hUc : ∀ m, U m = pullU (ρn x0 d n m).left ⊤ (U (m + 1)) := by
    intro m
    refine unit_ext (V := ⊤) fun y _ => ?_
    choose I hI using fun χ : (jOG x0 d m n).left ⟶ t.G.left => exists_chart hL (χ y)
    have e1 := hU m _ (𝟙 _) y I hI
    have e2 := hU (m + 1) _ (ρn x0 d n m).left y I hI
    have e3 := gm_pull (𝟙 _) (ρn x0 d n m).left y ⊤ trivial (U (m + 1))
    rw [Category.id_comp] at e3
    refine Eq.trans ?_ e3.symm
    exact (mul_inv_eq_iff_eq_mul.2 e1).symm.trans ((congrArg₂ (fun a b => a * b⁻¹) (hAt m y I hI).symm
      (hBt m y I hI).symm).trans (mul_inv_eq_iff_eq_mul.2 e2))
  have hac : ∀ m, (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] _) (v (m + 1)) = v m := by
    intro m
    apply toΓ_injective
    have e1 := congrArg Units.val (hv m)
    have e2 := congrArg Units.val (hv (m + 1))
    have nat := congrArg (fun f => CommRingCat.Hom.hom f ((v (m + 1) : Jet S (Fin n × Fin d) (m + 1))))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ((jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] _) :
        Jet S (Fin n × Fin d) (m + 1) →+* Jet S (Fin n × Fin d) m)))
    refine nat.trans (Eq.trans ?_ e1.symm)
    refine (congrArg (fun a => ((ρn x0 d n m).left.appTop).hom a) e2).trans ?_
    rw [hUc m]
    rfl
  obtain ⟨ph, hph⟩ := exists_ps_of_jets (fun m => (v m : Jet S (Fin n × Fin d) m)) hac
  refine ⟨ph, fun m => ⟨v m, (hph m).symm, corr_of_val hL fun y J hJ => ?_⟩⟩
  exact (hU m _ (𝟙 _) y J hJ).trans ((congrArg (fun u => gm (𝟙 _) y ⊤ u * val (B m) (𝟙 _) y J) (hv m).symm).trans
    (val_scale t _ _ _ _ _ y J hJ).symm)

theorem pe_trunc {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {e : ∀ m, FrTyG t x0 d x m} (htr : FrTrunc t x0 d x e) {n : ℕ}
    (φ : ℕ → Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S)
    (hφ : ∀ m i j, φ (m + 1) i j - φ m i j ∈ orig S (Fin n × Fin d) ^ (m + 1))
    (m : ℕ) (y : (jOG x0 d m n).left) (J : ((jOG x0 d m n).left ⟶ t.G.left) → t.PP.L.ι) (hJ : Good t.PP.L y J) :
    val (peG t x0 d x e (m + 1) (φ (m + 1))) (ρn x0 d n m).left y J = val (peG t x0 d x e m (φ m)) (𝟙 _) y J := by
  have hc : (jetSubstP m fun p : Fin 2 × Fin d => φ (m + 1) p.1 p.2 :
      Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m) = jetSubstP m fun p => φ m p.1 p.2 :=
    jetSubstP_congr m _ _ (fun p => hφ m p.1 p.2)
  have hcomp : (ρn x0 d n m).left ≫
      (homAt x0 (jetSubstP (m + 1) fun p : Fin 2 × Fin d => φ (m + 1) p.1 p.2)).left =
      (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ (m + 1) p.1 p.2)).left ≫
        (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left := by
    rw [← Over.comp_left, ← Over.comp_left, homAt_comp, homAt_comp, jetSubstP_trunc]
  unfold peG
  have h1 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull hJ (e (m + 1))
    (homAt x0 (jetSubstP (m + 1) fun p : Fin 2 × Fin d => φ (m + 1) p.1 p.2)).left (ρn x0 d n m).left (z := y) (J := J)
  have h2 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull hJ (e m)
    (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ m p.1 p.2)).left (𝟙 _) (z := y) (J := J)
  have h3 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull hJ (e (m + 1))
    (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left
    (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ m p.1 p.2)).left (z := y) (J := J)
  have h4 : val (LB.pullGen t.PP.L _ _ (e (m + 1))
      (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left)
      (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ m p.1 p.2)).left y J =
      val (e m) (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ m p.1 p.2)).left y J := by
    first
    | exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_corr (htr m) _
    | exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_corr hJ (htr m) _
    | exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_corr (htr m) _ hJ
  try unfold peG
  refine h1.trans ?_
  rw [hcomp, hc]
  refine h3.symm.trans (h4.trans ?_)
  refine (h2.trans ?_).symm
  rw [Category.id_comp]

end Series

end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrD
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

theorem push_inj {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} {a b : T ⟶ G'}
    (e : pushHom h T a = pushHom h T b) : a = b := by
  have e1 : a.left ≫ φ = b.left ≫ φ := congrArg (fun z => z.left) e
  have e2 : a.left ≫ G'.hom = b.left ≫ G'.hom := by
    rw [Over.w a, Over.w b]
  exact Over.OverMorphism.ext (h.1.hom_ext e1 e2)

theorem jetCoef_copy {V K : Type} [CommRing V] [CommRing K] (f : V →+* K) (d m n : ℕ) (i : Fin n) :
    (jetCoef f (Fin n × Fin d) m).comp ((jetCopy (S := V) d m i : Jet V (Fin 1 × Fin d) m →ₐ[V] Jet V (Fin n × Fin d) m) :
      Jet V (Fin 1 × Fin d) m →+* Jet V (Fin n × Fin d) m) =
    ((jetCopy (S := K) d m i : Jet K (Fin 1 × Fin d) m →ₐ[K] Jet K (Fin n × Fin d) m) :
      Jet K (Fin 1 × Fin d) m →+* Jet K (Fin n × Fin d) m).comp (jetCoef f (Fin 1 × Fin d) m) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    show Ideal.Quotient.mk (orig K (Fin n × Fin d) ^ (m + 1))
        (MvPolynomial.map f (MvPolynomial.bind₁ (fun p : Fin 1 × Fin d => MvPolynomial.X (i, p.2))
          (MvPolynomial.C r))) =
      Ideal.Quotient.mk (orig K (Fin n × Fin d) ^ (m + 1))
        (MvPolynomial.bind₁ (fun p : Fin 1 × Fin d => MvPolynomial.X (i, p.2))
          (MvPolynomial.map f (MvPolynomial.C r)))
    simp
  · intro q
    show Ideal.Quotient.mk (orig K (Fin n × Fin d) ^ (m + 1))
        (MvPolynomial.map f (MvPolynomial.bind₁ (fun p : Fin 1 × Fin d => MvPolynomial.X (i, p.2))
          (MvPolynomial.X q))) =
      Ideal.Quotient.mk (orig K (Fin n × Fin d) ^ (m + 1))
        (MvPolynomial.bind₁ (fun p : Fin 1 × Fin d => MvPolynomial.X (i, p.2))
          (MvPolynomial.map f (MvPolynomial.X q)))
    simp

section Pt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
variable (I : IntData Xo c T io y.1) {d : ℕ} (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G)

def U2 (m : ℕ) : Over.mk ((jOG (𝟙 (Sp T.Fr)) d m 2).hom ≫ spMap (algebraMap T.V T.Fr)) ⟶ jOG (𝟙 (Sp T.V)) d m 2 :=
  Over.homMk (spMap (jc (d := d) 2 m)) (by
    show spMap (jc (d := d) 2 m) ≫ spMap (algebraMap T.V (Jet T.V (Fin 2 × Fin d) m)) ≫ 𝟙 _ =
      (spMap (algebraMap T.Fr (Jet T.Fr (Fin 2 × Fin d) m)) ≫ 𝟙 _) ≫ spMap (algebraMap T.V T.Fr)
    rw [Category.comp_id, Category.comp_id, spMap_comp', spMap_comp', jetCoef_alg])

theorem push_jpt (m : ℕ) (i : Fin 2) :
    pushHom I.m2.cart _ (jptG I.t' (𝟙 (Sp T.Fr)) d (xP I xT) m i) = U2 (d := d) m ≫ jptG I.G (𝟙 (Sp T.V)) d xT m i := by
  apply Over.OverMorphism.ext
  show (spMap _ ≫ xL I xT m) ≫ I.m2.φ = spMap (jc (d := d) 2 m) ≫ spMap _ ≫ (xT m).left
  rw [Category.assoc, xL_fst, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', jetCoef_copy]

theorem xP_law (FT : Fin d → MvPowerSeries (Fin 2 × Fin d) T.V) (m : ℕ)
    (hl : Formalism.L2.Pj.homAt (𝟙 (Sp T.V)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (FT p.2)) ≫ xT m =
      jptG I.G (𝟙 (Sp T.V)) d xT m (0 : Fin 2) * jptG I.G (𝟙 (Sp T.V)) d xT m (1 : Fin 2)) :
    Formalism.L2.Pj.homAt (𝟙 (Sp T.Fr)) (jetSubstP m fun p : Fin 1 × Fin d =>
              MvPolynomial.map (algebraMap T.V T.Fr) (psTrunc m (FT p.2))) ≫ xP I xT m =
      jptG I.t' (𝟙 (Sp T.Fr)) d (xP I xT) m (0 : Fin 2) * jptG I.t' (𝟙 (Sp T.Fr)) d (xP I xT) m (1 : Fin 2) := by
  apply push_inj I.m2.cart
  rw [map_mul, push_jpt, push_jpt, ← MonObj.comp_mul, ← hl]
  apply Over.OverMorphism.ext
  show (spMap _ ≫ xL I xT m) ≫ I.m2.φ = spMap (jc (d := d) 2 m) ≫ spMap _ ≫ (xT m).left
  rw [Category.assoc, xL_fst, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', jetCoef_substP]

end Pt

end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GPowPf
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

section Pow

variable {S : Scheme.{0}} {A' A : Over S} [GrpObj A'] [GrpObj A] {n : ℕ}

theorem pow_ext (p : IsPowGrp A' A n) {T : Over S} {x y : T ⟶ A'} (h : ∀ i, x ≫ p.pr i = y ≫ p.pr i) :
    x = y :=
  p.lim.hom_ext fun ⟨i⟩ => h i

variable [IsCommMonObj A'] [IsCommMonObj A]

end Pow

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end
