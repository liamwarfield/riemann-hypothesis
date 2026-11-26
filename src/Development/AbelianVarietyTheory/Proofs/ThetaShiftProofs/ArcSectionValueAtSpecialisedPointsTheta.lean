module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNeZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermMemConvLaurent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantTermWeightZeroSectionLevelOneFormalSum
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CoeffMulFSum
noncomputable section
namespace GlobalTheory.ArcPts.WeightZero
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped LaurentSeries

variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

def chr (x : A.X) : Multiplicative (A.X →+ ℂ) →* ℂ where
  toFun l := eTwoPi (l.toAdd x)
  map_one' := AnArc.e_zero
  map_mul' l l' := AnArc.e_add _ _

theorem chr_injective : Function.Injective (chr A) := by
  intro x y hxy
  by_contra hne
  have hd : x - y ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨i, hi⟩ : ∃ i, (Module.Free.chooseBasis ℤ A.X).repr (x - y) i ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    apply hd
    apply (Module.Free.chooseBasis ℤ A.X).repr.map_eq_zero_iff.mp
    ext j
    simpa using hall j
  let k : ℤ := (Module.Free.chooseBasis ℤ A.X).repr (x - y) i
  let g : A.X →+ ℂ := (Int.castAddHom ℂ).comp ((Module.Free.chooseBasis ℤ A.X).coord i).toAddMonoidHom
  have hg : g (x - y) = k := by simp [g, k]
  have hk : (k : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hi
  let l : A.X →+ ℂ := (2 * (k : ℂ))⁻¹ • g
  have hl : l (x - y) = 1 / 2 := by
    simp only [l, AddMonoidHom.smul_apply, hg, smul_eq_mul]
    field_simp
  have h1 : eTwoPi (l x) = eTwoPi (l y) := congrArg (fun χ => χ (Multiplicative.ofAdd l)) hxy
  have h2 : eTwoPi (l x) = eTwoPi (l (x - y)) * eTwoPi (l y) := by
    rw [← AnArc.e_add, map_sub, sub_add_cancel]
  rw [hl, h1] at h2
  have h3 : eTwoPi (1 / 2) = 1 :=
    mul_right_cancel₀ (AnArc.e_ne_zero (l y)) (h2.symm.trans (one_mul _).symm)
  have h4 : eTwoPi (1 / 2) = -1 := by
    simp only [eTwoPi]
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (1 / 2) = Real.pi * Complex.I by ring, Complex.exp_pi_mul_I]
  rw [h4] at h3
  norm_num at h3

theorem coeff_zero_eq {F G : Finset A.X} {b c : A.X → ℂ} (hF : 0 ∈ F) (hG : 0 ∈ G)
    (h : ∀ l : A.X →+ ℂ, ∑ x ∈ F, b x * eTwoPi (l x) = ∑ x ∈ G, c x * eTwoPi (l x)) : b 0 = c 0 := by
  classical
  have hli : LinearIndependent ℂ (fun x : A.X =>
      ((chr A x : Multiplicative (A.X →+ ℂ) →* ℂ) : Multiplicative (A.X →+ ℂ) → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative (A.X →+ ℂ)) ℂ).comp (chr A) (chr_injective A)
  let g : A.X → ℂ := fun x => (if x ∈ F then b x else 0) - (if x ∈ G then c x else 0)
  have hsum : ∑ x ∈ F ∪ G, g x • ((chr A x : Multiplicative (A.X →+ ℂ) →* ℂ) :
      Multiplicative (A.X →+ ℂ) → ℂ) = 0 := by
    funext m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, g, sub_mul, ite_mul, zero_mul,
      Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.union_inter_cancel_left,
      Finset.union_inter_cancel_right]
    exact sub_eq_zero.mpr (h (Multiplicative.toAdd m))
  have h0 := linearIndependent_iff'.mp hli (F ∪ G) g hsum 0 (Finset.mem_union_left _ hF)
  simpa [g, hF, hG, sub_eq_zero] using h0

theorem exponent_one (α μ : A.X) : A.exponent 1 α μ = A.q (α + μ) - A.q α := by
  rw [AnArc.exponent, AnArc.q_add, A.be_symm μ α]
  push_cast
  ring

theorem FSum_shift (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (v : A.V) :
    A.FSum 1 α th v = HahnSeries.single (-A.q α) ((A.psi α : ℂ)⁻¹) * A.FSum 1 0 (fun z => th (z - A.ct α)) v := by
  ext n
  rw [HahnSeries.coeff_single_mul, AnArc.coeff_FSum, AnArc.coeff_FSum, Finset.mul_sum, sub_neg_eq_add]
  refine Finset.sum_nbij' (fun μ => α + μ) (fun ν => ν - α) ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    simp only [AnArc.mem_level, exponent_one A, zero_add, AnArc.q_zero, sub_zero] at hμ ⊢
    linarith
  · intro ν hν
    simp only [AnArc.mem_level, exponent_one A, zero_add, AnArc.q_zero, sub_zero] at hν ⊢
    rw [show α + (ν - α) = ν by abel]
    linarith
  · intro μ _
    simp
  · intro ν _
    simp
  · intro μ _
    have hu : (A.psi α : ℂ) ≠ 0 := (A.psi α).ne_zero
    have hc : v.2 + A.ct (α + μ) - A.ct α = v.2 + A.ct μ := by rw [map_add (f := _)]; abel
    simp only [AnArc.term, pow_one, one_smul, zero_add, map_zero, AnArc.e_zero, A.psi_add,
      A.T_symm α μ, hc]
    rw [eq_inv_mul_iff_mul_eq₀ hu]
    ring

theorem coeff_mul_FSum (r : ℂ⸨X⸩) (n : ℤ) : ∃ G₀ : Finset A.X, ∀ G, G₀ ⊆ G → ∀ (th : (Fin A.gB → ℂ) → ℂ) (v : A.V),
    (r * A.FSum 1 0 th v).coeff n = ∑ μ ∈ G, r.coeff (n - A.q μ) * A.term 1 0 th μ v := by
  classical
  refine ⟨(A.finite_be_le (2 * (n - r.order))).toFinset, fun G hG th v => ?_⟩
  have hq : ∀ μ, A.exponent 1 0 μ = A.q μ := fun μ => by
    rw [exponent_one A, zero_add, AnArc.q_zero, sub_zero]
  have hq0 : ∀ μ, 0 ≤ A.q μ := fun μ => by
    have h1 := A.two_mul_q μ
    have h2 := A.be_self_nonneg μ
    linarith
  have hpwo : (Set.Ici (0 : ℤ)).IsPWO := bddBelow_Ici.isWF.isPWO
  have hsupp : (A.FSum 1 0 th v).support ⊆ Set.Ici 0 := by
    intro k hk
    rw [Set.mem_Ici]
    by_contra hlt
    exact hk (A.coeff_FSum_eq_zero 1 0 th v (by simpa using not_le.mp hlt))
  rw [HahnSeries.coeff_mul_right' hpwo hsupp]
  simp only [AnArc.coeff_FSum, Finset.mul_sum]
  rw [Finset.sum_sigma']
  refine Finset.sum_bij_ne_zero (fun a _ _ => a.2) ?_ ?_ ?_ ?_
  · rintro ⟨⟨i, k⟩, μ⟩ h₁ h₂
    rw [Finset.mem_sigma, Finset.mem_antidiagonal, AnArc.mem_level, hq] at h₁
    obtain ⟨⟨-, -, hik⟩, hμ⟩ := h₁
    have ho := HahnSeries.order_le_of_coeff_ne_zero (left_ne_zero_of_mul h₂)
    apply hG
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, ← A.two_mul_q]
    simp only at hμ hik ho ⊢
    linarith
  · rintro ⟨⟨i, k⟩, μ⟩ h₁ _ ⟨⟨i', k'⟩, μ'⟩ h₁' _ heq
    simp only at heq
    subst heq
    rw [Finset.mem_sigma, Finset.mem_antidiagonal, AnArc.mem_level, hq] at h₁ h₁'
    obtain ⟨⟨-, -, hik⟩, hμ⟩ := h₁
    obtain ⟨⟨-, -, hik'⟩, hμ'⟩ := h₁'
    simp only at hik hμ hik' hμ'
    have hk : k = k' := by rw [← hμ, ← hμ']
    subst hk
    have hi : i = i' := by omega
    subst hi
    rfl
  · intro μ _ hne
    refine ⟨⟨(n - A.q μ, A.q μ), μ⟩, ?_, hne, rfl⟩
    rw [Finset.mem_sigma, Finset.mem_antidiagonal, AnArc.mem_level, hq]
    exact ⟨⟨(HahnSeries.mem_support _ _).mpr (left_ne_zero_of_mul hne), Set.mem_Ici.mpr (hq0 μ), by simp⟩, rfl⟩
  · rintro ⟨⟨i, k⟩, μ⟩ h₁ _
    rw [Finset.mem_sigma, Finset.mem_antidiagonal, AnArc.mem_level, hq] at h₁
    obtain ⟨⟨-, -, hik⟩, hμ⟩ := h₁
    simp only at hik hμ ⊢
    rw [show i = n - A.q μ by omega]

theorem eq_FSum {f : A.V → ℂ⸨X⸩} (hf : ArcPts.IsComb A 1 Set.univ f) (θ : (Fin A.gB → ℂ) → ℂ)
    (h : ∀ (z : Fin A.gB → ℂ) (n : ℤ), ∃ (F : Finset A.X) (b : A.X → ℂ), 0 ∈ F ∧ b 0 = (if n = 0 then θ z else 0) ∧
      ∀ l : A.X →+ ℂ, (f (l, z)).coeff n = ∑ x ∈ F, b x * eTwoPi (l x)) (v : A.V) : f v = A.FSum 1 0 θ v := by
  classical
  obtain ⟨m, r, α, th, -, hfe⟩ := hf
  obtain ⟨s, ph, hfe'⟩ : ∃ (s : Fin m → ℂ⸨X⸩) (ph : Fin m → (Fin A.gB → ℂ) → ℂ),
      ∀ w, f w = ∑ i, s i * A.FSum 1 0 (ph i) w :=
    ⟨fun i => r i * HahnSeries.single (-A.q (α i)) ((A.psi (α i) : ℂ)⁻¹), fun i z => th i (z - A.ct (α i)),
      fun w => by
        rw [hfe w]
        exact Finset.sum_congr rfl fun i _ => by simp only [FSum_shift A (α i) (th i) w, mul_assoc]⟩
  have hq : ∀ μ, A.exponent 1 0 μ = A.q μ := fun μ => by
    rw [exponent_one A, zero_add, AnArc.q_zero, sub_zero]
  have hexp : ∀ n : ℤ, ∃ G : Finset A.X, 0 ∈ G ∧ A.level 1 0 n ⊆ G ∧ ∀ w : A.V,
      (f w).coeff n = ∑ μ ∈ G, ∑ i, (s i).coeff (n - A.q μ) * A.term 1 0 (ph i) μ w := by
    intro n
    choose G₀ hG₀ using fun i => coeff_mul_FSum A (s i) n
    have hsub : ∀ i, G₀ i ⊆ insert 0 (A.level 1 0 n ∪ Finset.univ.biUnion G₀) := fun i =>
      (Finset.subset_biUnion_of_mem G₀ (Finset.mem_univ i)).trans
        (Finset.subset_union_right.trans (Finset.subset_insert _ _))
    refine ⟨insert 0 (A.level 1 0 n ∪ Finset.univ.biUnion G₀), Finset.mem_insert_self _ _,
      fun μ hμ => Finset.mem_insert_of_mem (Finset.mem_union_left _ hμ), fun w => ?_⟩
    rw [hfe' w, HahnSeries.coeff_sum, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => hG₀ i _ (hsub i) (ph i) w
  have hkey : ∀ (z : Fin A.gB → ℂ) (n : ℤ), ∑ i, (s i).coeff n * ph i z = if n = 0 then θ z else 0 := by
    intro z n
    obtain ⟨G, hG0, -, hG⟩ := hexp n
    obtain ⟨F, b, hF0, hb0, hFb⟩ := h z n
    have hc := coeff_zero_eq A (F := F) (G := G) (b := b)
      (c := fun μ => (A.psi μ : ℂ) * ∑ i, (s i).coeff (n - A.q μ) * ph i (z + A.ct μ)) hF0 hG0 (fun l => by
        rw [← hFb l, hG (l, z)]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [AnArc.term, pow_one, one_smul, zero_add, map_zero, AnArc.e_zero]
        ring)
    rw [← hb0, hc]
    simp
  ext n
  obtain ⟨G, -, hlev, hG⟩ := hexp n
  have hK : ∀ (μ : A.X) (g : (Fin A.gB → ℂ) → ℂ),
      A.term 1 0 g μ v = A.term 1 0 (fun _ => 1) μ v * g (v.2 + A.ct μ) := by
    intro μ g
    simp only [AnArc.term, mul_one]
  have hterm : ∀ μ, ∑ i, (s i).coeff (n - A.q μ) * A.term 1 0 (ph i) μ v =
      if A.q μ = n then A.term 1 0 θ μ v else 0 := by
    intro μ
    calc ∑ i, (s i).coeff (n - A.q μ) * A.term 1 0 (ph i) μ v
        = A.term 1 0 (fun _ => 1) μ v * ∑ i, (s i).coeff (n - A.q μ) * ph i (v.2 + A.ct μ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [hK μ (ph i)]; ring
      _ = if A.q μ = n then A.term 1 0 θ μ v else 0 := by
          rw [hkey, hK μ θ]
          by_cases hμ : A.q μ = n
          · rw [if_pos (by omega), if_pos hμ]
          · rw [if_neg (by omega), if_neg hμ, mul_zero]
  rw [hG v, AnArc.coeff_FSum]
  simp only [hterm]
  rw [← Finset.sum_filter]
  congr 1
  ext μ
  simp only [Finset.mem_filter, AnArc.mem_level, hq]
  exact ⟨fun hμ => hμ.2, fun hμ => ⟨hlev (by rw [AnArc.mem_level, hq]; exact hμ), hμ⟩⟩

end GlobalTheory.ArcPts.WeightZero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantTermWeightZeroSectionLevelOneFormalSum
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts.WeightZero

theorem valR_pullGen_spMap {A A' : Type} [CommRing A] [CommRing A'] [IsLocalRing A'] {Z : Scheme.{0}} (L : LB Z)
    {K : Type} [Fintype K] (φ : K → (Sp A ⟶ Z)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (f : A →+* A')
    (j : K → L.ι) (h : ⊤ ≤ LB.wchart L φ j) :
    valR (𝟙 (Sp A')) (LB.wchart L (fun k => spMap f ≫ φ k) j) ((LB.pullGen L φ ε t (spMap f)).s j).val =
      f (valR (𝟙 (Sp A)) (LB.wchart L φ j) (t.s j).val) := by
  have h₀ : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ LB.wchart L φ j := h
  have h₁ : ⊤ ≤ (𝟙 (Sp A')) ⁻¹ᵁ LB.wchart L (fun k => spMap f ≫ φ k) j := fun z _ =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 (h (show spMap f z ∈ (⊤ : (Sp A).Opens) from trivial)) k
  have toStkA_valR : ∀ {R : Type} [CommRing R] {T : Scheme.{0}} (f : Sp R ⟶ T)
      (U : T.Opens) (z : Sp R) (ht : ⊤ ≤ f ⁻¹ᵁ U) (a : Γ(T, U)ˣ),
      toStkA z (valR f U a.val) = (gm f z U a).val := by
    intro R _ T f U z ht a
    have hz : f z ∈ U := ht trivial
    have e1 : ∀ c, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c) = c :=
      fun c => congrArg (fun f => CommRingCat.Hom.hom f c) (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of R)))
    rw [valR, dif_pos ht, gm, dif_pos hz]
    show ((Sp R).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((f.appLE U ⊤ ht).hom a.val))) =
      ((Sp R).presheaf.germ (f ⁻¹ᵁ U) z hz).hom ((f.app U).hom a.val)
    rw [e1]
    exact TopCat.Presheaf.germ_res_apply (Sp R).presheaf (homOfLE ht) z trivial ((f.app U).hom a.val)
  have gm_pullU_eq_gm_comp {S T V : Scheme.{0}} (h : T ⟶ S) (r : V ⟶ T) (z : V) (U : S.Opens)
      (a : Γ(S, U)ˣ) : gm r z (h ⁻¹ᵁ U) (pullU h U a) = gm (r ≫ h) z U a := by
    by_cases hz : r z ∈ h ⁻¹ᵁ U
    · have hz' : (r ≫ h) z ∈ U := hz
      simp only [gm, dif_pos hz, dif_pos hz']
      all_goals first | rfl | (ext; simp [pullU, Scheme.comp_app])
    · have hz' : (r ≫ h) z ∉ U := hz
      simp only [gm, dif_neg hz, dif_neg hz', MonoidHom.one_apply]
  have gm_pullGen' {X Y Z Z' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
      (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε))
      (h : Z ⟶ Y) (r : Z' ⟶ Z) (z : Z') (j : K → L.ι) :
      gm r z (LB.wchart L (fun k => h ≫ φ k) j) ((LB.pullGen L φ ε t h).s j) =
        gm (r ≫ h) z (LB.wchart L φ j) (t.s j) := by
    by_cases hz : r z ∈ LB.wchart L (fun k => h ≫ φ k) j
    · exact (gm_res r z _ hz (pullU h _ (t.s j))).trans (gm_pullU_eq_gm_comp h r z _ _)
    · have hz' : (r ≫ h) z ∉ LB.wchart L φ j := fun H => hz (Set.mem_iInter.2 fun k => Set.mem_iInter.1 H k)
      simp only [gm, dif_neg hz, dif_neg hz', MonoidHom.one_apply]
      rfl
  apply toStkA_injective
  refine (toStkA_valR _ _ _ h₁ _).trans ((congrArg Units.val (gm_pullGen' L φ ε t (spMap f) (𝟙 _) _ j)).trans ?_)
  refine Eq.trans ?_ (congrArg _ (FormalValue.valR_spMap f _ _ h₀ _))
  refine Eq.trans ?_ (toStkA_valR _ _ _ (FormalValue.top_le_comp h₀ (spMap f)) _).symm
  rw [Category.id_comp, Category.comp_id]

theorem coordVal_zero {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I} {S : Type} [CommRing S]
    {s : Sp S ⟶ Sp R} (g : Out.GtPt D.toPre (Over.mk s)) {jM : D.toPre.P.L.ι} {jf jt : Fin 4 → D.toPre.P.L.ι}
    (h : FormalValue.CohCharts g 0 jM jf jt) : FormalValue.coordVal g 0 jt = 1 := by
  have e := g.s_zero jt PEmpty.elim (fun a b hab => h.2.2 (.inr (.inr a)) (.inr (.inr b)) hab) (fun a => a.elim)
    (fun _ a => a.elim)
  have ht : ⊤ ≤ (𝟙 (Sp S)) ⁻¹ᵁ (LB.wchart D.toPre.P.L (FormalValue.coordφ g 0) jt ⊓
      LB.wchart D.toPre.P.L (K := PEmpty) PEmpty.elim PEmpty.elim) := fun z hz =>
    ⟨h.2.1 hz, Set.mem_iInter.2 fun k => k.elim⟩
  refine (Points.valR_res (𝟙 (Sp S)) inf_le_left ht _).symm.trans ?_
  refine (congrArg (fun q => valR (𝟙 (Sp S)) _ (Units.val q)) (e.trans (map_one _))).trans ?_
  exact Points.valR_one _ _ ht

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable [Algebra (FractionRing ℂ) ℂ] {Y : Model Xo c β} {b : O →+* ℂ} {a : ArcIn D l β ℂ b} {χ : Sp ℂ⟦X⟧ ⟶ Y.X}
  {W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ} {Λ : GtAn a}
  (Ξ : ConstPts W Λ)

theorem basePt_comp (v : Λ.A.V) :
    FormalValue.basePt (Ξ.g v) ≫ W.φ = spMap (PowerSeries.C (R := ℂ)) ≫ (Λ.u.ex v.2).left :=
  ((Ξ.g_rel v 0).1 2).trans (congrArg (spMap (PowerSeries.C (R := ℂ)) ≫ ·) (Λ.ex0_b v))

theorem b_eq {v v' : Λ.A.V} (h : v.2 = v'.2) : (Ξ.g v).b = (Ξ.g v').b := by
  refine Over.OverMorphism.ext (W.spec.1.1.hom_ext ?_ ?_)
  · exact (basePt_comp Ξ v).trans (h ▸ (basePt_comp Ξ v').symm)
  · exact (Over.w (Ξ.g v).b).trans (Over.w (Ξ.g v').b).symm

theorem exists_base_charts (v : Λ.A.V) : ∃ (jM : W.P.D.toPre.P.L.ι) (j₀ : a.D₀.P.L.ι),
    ⊤ ≤ FormalValue.basePt (Ξ.g v) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) ∧
    ⊤ ≤ (Λ.u.ex v.2).left ⁻¹ᵁ a.D₀.P.L.U j₀ := by
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB (FormalValue.basePt (Ξ.g v) (cpt ℂ⟦X⟧))
  have h₀ := FrameValue.le_chartAt a.D₀.P.isLB (Λ.u.ex v.2).left
  refine ⟨jM, _, (top_le_iff_cpt _ _).2 ⟨mem_pull.2 ?_, hM⟩, h₀⟩
  exact (congrArg (fun q => q (cpt ℂ⟦X⟧) ∈ a.D₀.P.L.U _) (basePt_comp Ξ v)).mpr (FormalValue.top_le_comp h₀ _ trivial)


omit Ξ in
theorem coordinate_complexConstantPoint_eq_char_mul (z : Fin Λ.A.gB → ℂ) (x : Λ.A.X) : ∃ (j₀ : Fin 4 → a.D₀.P.L.ι) (k : ℂ), ∀ l : Λ.A.X →+ ℂ,
    ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 (l, z)).b (Λ.ε x)) j₀ ∧
      valR (𝟙 (Sp ℂ)) (LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 (l, z)).b (Λ.ε x)) j₀)
        (((Λ.ex0 (l, z)).s (Λ.ε x)).s j₀).val = eTwoPi (l x) * k := by
  refine ⟨fun k => FrameValue.chartAt a.D₀.P.isLB
    ((show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ≫ Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 (0, z)).b (Λ.ε x) k),
    FrameValue.frameProd Λ.u Out.DegPre.gtε ![Λ.A.ct x + z, Λ.A.ct x, z, 0] fun k => FrameValue.chartAt a.D₀.P.isLB
    ((show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ≫ Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 (0, z)).b (Λ.ε x) k), fun l => ?_⟩
  have hb : (Λ.ex0 (0, z)).b = (Λ.ex0 (l, z)).b :=
    Over.OverMorphism.ext ((Λ.ex0_b (0, z)).trans (Λ.ex0_b (l, z)).symm)
  rw [hb]
  refine ⟨FrameValue.le_wchart_chartAt a.D₀.P.isLB _ (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)), ?_⟩
  have key : ∀ p q r : ℂ, p / q = r → r ≠ 0 → p = r * q := fun p q r h hr =>
    (div_eq_iff (by rintro rfl; exact hr (h.symm.trans (div_zero p)))).1 h
  exact key _ _ _ (Λ.arcDict_expZero_section (l, z) x) (AnArc.e_ne_zero _)

theorem coordVal_eq (z : Fin Λ.A.gB → ℂ) (x : Λ.A.X) (jt : Fin 4 → W.P.D.toPre.P.L.ι)
    (h : ⊤ ≤ LB.wchart W.P.D.toPre.P.L (FormalValue.coordφ (Ξ.g (0, z)) (W.e (Λ.ε x))) jt) (l : Λ.A.X →+ ℂ) :
    FormalValue.coordVal (Ξ.g (l, z)) (W.e (Λ.ε x)) jt =
      PowerSeries.C (eTwoPi (l x)) * FormalValue.coordVal (Ξ.g (0, z)) (W.e (Λ.ε x)) jt := by
  obtain ⟨j₀, k, hk⟩ := coordinate_complexConstantPoint_eq_char_mul (Λ := Λ) z x
  let P : (selfR ⟶ W.P.D.toPre.P.A) → ℂ⟦X⟧ := fun p => ∏ i, valR (A := ℂ⟦X⟧)
    (Out.DegPre.gtφT W.P.D.toPre selfR p (W.e (Λ.ε x)) i) _
      ((show (Γ(W.P.D.toPre.P.A.left, (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀ i, jt i)))ˣ from
        W.w.s (fun _ => j₀ i, jt i)) ^ (-Out.DegPre.gtε i)).val
  have key : ∀ l : Λ.A.X →+ ℂ, FormalValue.coordVal (Ξ.g (l, z)) (W.e (Λ.ε x)) jt =
      P (Ξ.g (0, z)).b * PowerSeries.C (eTwoPi (l x) * k) := by
    intro l
    have hb : (Ξ.g (0, z)).b = (Ξ.g (l, z)).b := b_eq Ξ rfl
    have h' : ⊤ ≤ LB.wchart W.P.D.toPre.P.L (Out.DegPre.gtφT W.P.D.toPre selfR (Ξ.g (l, z)).b (W.e (Λ.ε x))) jt :=
      hb ▸ h
    obtain ⟨r₁, r₂⟩ := Ξ.g_rel (l, z) (Λ.ε x)
    rw [hb, ← (hk l).2]
    refine (r₂ jt j₀ fun i y hy => ⟨mem_pull.2 ?_, Set.mem_iInter.1 (h' hy) i⟩).trans (congrArg (_ * ·) ?_)
    · exact (congrArg (fun q => q y ∈ a.D₀.P.L.U (j₀ i)) (r₁ i)).mpr (Set.mem_iInter.1
        ((hk l).1 (show spMap (PowerSeries.C (R := ℂ)) y ∈ (⊤ : (Sp ℂ).Opens) from trivial)) i)
    · exact valR_pullGen_spMap (A := ℂ) a.D₀.P.L _ _ ((Λ.ex0 (l, z)).s (Λ.ε x)) _ j₀ (hk l).1
  rw [key, key]
  simp only [AddMonoidHom.zero_apply, AnArc.e_zero, _root_.one_mul, map_mul]
  ring

variable {th : a.D₀.P.L.Sec} {σ : Out.H0 W.P.U.LG.L 1} {fam : ∀ x, W.P.D.toPre.SecB 1 x}
  {θ : (Fin Λ.A.gB → ℂ) → ℂ}

theorem famVal_zero (h : ThetaHyp W th σ fam) (hθ : Λ.u.IsFn th θ) (v : Λ.A.V) {jM : W.P.D.toPre.P.L.ι}
    {j₀ : a.D₀.P.L.ι} {jf jt : Fin 4 → W.P.D.toPre.P.L.ι} (hc : FormalValue.CohCharts (Ξ.g v) 0 jM jf jt)
    (hj : ⊤ ≤ FormalValue.basePt (Ξ.g v) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM))
    (h₀ : ⊤ ≤ (Λ.u.ex v.2).left ⁻¹ᵁ a.D₀.P.L.U j₀) :
    valR (FormalValue.basePt (Ξ.g v)) _ (W.w.s (fun _ => j₀, jM)).val * FormalValue.famVal (Ξ.g v) (fam 0) jf =
      PowerSeries.C (θ v.2 * Λ.u.fr j₀ v.2) := by
  have e₁ : W.P.D.toPre.famφB 0 1 = 𝟙 _ := by
    have : (𝟙 W.P.D.toPre.P.A) * DVR.cP W.P.D.toPre W.P.D.toPre.P.A 0 = 𝟙 _ := by rw [cPoint_zero, _root_.mul_one]
    exact congrArg Over.Hom.left this
  obtain rfl : jf 1 = jM := hc.2.2 (.inr (.inl 1)) (.inl PUnit.unit)
    ((congrArg (FormalValue.basePt (Ξ.g v) ≫ ·) e₁).trans (Category.comp_id _))
  have hV : ⊤ ≤ FormalValue.basePt (Ξ.g v) ⁻¹ᵁ (LB.wchart W.P.D.toPre.P.L (W.P.D.toPre.famφB 0) jf ⊓
      (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jf 1) ⊓ W.φ ⁻¹ᵁ a.D₀.P.L.U j₀) := fun y hy =>
    ⟨⟨hc.1 hy, hj hy⟩, mem_pull.1 (hj hy).1⟩
  have e := congrArg (valR (FormalValue.basePt (Ξ.g v)) _) (h.2.2 jf j₀ _ (inf_le_left.trans inf_le_left)
    (inf_le_left.trans inf_le_right) inf_le_right
    (fun i i' hi => hc.2.2 (.inr (.inl i)) (.inr (.inl i')) (congrArg (FormalValue.basePt (Ξ.g v) ≫ ·) hi)))
  rw [Points.valR_appLE _ _ _ hV, Points.valR_mul _ _ hV, basePt_comp, FormalValue.valR_spMap _ _ _ h₀] at e
  refine (congrArg₂ (· * ·) (Points.valR_res _ _ hV _) (Points.valR_res _ _ hV _)).symm.trans (e.symm.trans ?_)
  exact congrArg _ (hθ j₀ v.2 h₀)

theorem cohCharts_congr {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I} {S : Type} [CommRing S]
    {s : Sp S ⟶ Sp R} {g g' : Out.GtPt D.toPre (Over.mk s)} (e : g.b = g'.b) {α : D.toPre.X} {jM : D.toPre.P.L.ι}
    {jf jt : Fin 4 → D.toPre.P.L.ι} (h : FormalValue.CohCharts g α jM jf jt) : FormalValue.CohCharts g' α jM jf jt := by
  dsimp only [FormalValue.CohCharts, FormalValue.basePt, FormalValue.coordφ] at h ⊢
  rw [← e]
  exact h

theorem exists_expansion (h : ThetaHyp W th σ fam) (hθ : Λ.u.IsFn th θ) {f : Λ.A.V → ℂ⸨X⸩} (hf : Ξ.Vals σ f)
    (z : Fin Λ.A.gB → ℂ) (e : ℕ) : ∃ (F : Finset Λ.A.X) (B : Λ.A.X → ℂ⟦X⟧), 0 ∈ F ∧ B 0 = PowerSeries.C (θ z) ∧
      ∀ l : Λ.A.X →+ ℂ, ∃ p : ℂ⟦X⟧, f (l, z) = algebraMap ℂ⟦X⟧ ℂ⸨X⸩ p ∧
        PowerSeries.coeff e p = PowerSeries.coeff e (∑ x ∈ F, PowerSeries.C (eTwoPi (l x)) * B x) := by
  classical
  have hJ : (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) = Ideal.span {PowerSeries.X} := by
    rw [Algebra.algebraMap_self, Ideal.map_id]
  haveI : IsAdicComplete ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) ℂ⟦X⟧ := by
    rw [hJ]; infer_instance
  haveI := isLocalRing_quotient_pow (ne_top_of_isHausdorff
    ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧))) e
  obtain ⟨F, hF⟩ := FormalValue.map_secVal_eq W.P.U.toUnifPre (h.2.1 e)
  let ι₀ : Λ.A.X ≃ W.P.D.toPre.X := (Λ.ε.trans W.e).toEquiv
  obtain ⟨jM, j₀, hj, h₀⟩ := exists_base_charts Ξ (0, z)
  have hM : ⊤ ≤ FormalValue.basePt (Ξ.g (0, z)) ⁻¹ᵁ W.P.D.toPre.P.L.U jM := fun y hy => (hj hy).2
  choose jf jt hc using FormalValue.exists_cohCharts (Ξ.g (0, z)) jM hM
  have hfr : PowerSeries.C (Λ.u.fr j₀ z)⁻¹ * PowerSeries.C (Λ.u.fr j₀ z) = (1 : ℂ⟦X⟧) := by
    rw [← map_mul, inv_mul_cancel₀ (Λ.u.fr_ne j₀ z h₀), map_one]
  obtain ⟨w, hw⟩ : ∃ w, w = valR (FormalValue.basePt (Ξ.g (0, z))) _ (W.w.s (fun _ => j₀, jM)).val := ⟨_, rfl⟩
  let B : W.P.D.toPre.X → ℂ⟦X⟧ := fun α => PowerSeries.C (Λ.u.fr j₀ z)⁻¹ * w *
    (FormalValue.famVal (Ξ.g (0, z)) (fam α) (jf α) * FormalValue.coordVal (Ξ.g (0, z)) α (jt α))
  refine ⟨insert 0 (F.map ι₀.symm.toEmbedding), fun x => B (ι₀ x), Finset.mem_insert_self _ _, ?_, fun l => ?_⟩
  · have : ι₀ 0 = 0 := map_zero (Λ.ε.trans W.e)
    have e₀ := famVal_zero Ξ h hθ (0, z) (hc 0) hj h₀
    rw [← hw, map_mul] at e₀
    simp only [this, B]
    rw [coordVal_zero _ (hc 0), _root_.mul_one, _root_.mul_assoc, e₀, mul_left_comm, hfr, _root_.mul_one]
  have hb : (Ξ.g (0, z)).b = (Ξ.g (l, z)).b := b_eq Ξ rfl
  have hb' : FormalValue.basePt (Ξ.g (0, z)) = FormalValue.basePt (Ξ.g (l, z)) := congrArg Over.Hom.left hb
  obtain ⟨jL, hL⟩ := exists_chart W.P.U.LG.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.x (l, z)).left) (cpt ℂ⟦X⟧))
  replace hL := (top_le_iff_cpt _ _).2 hL
  rw [hb'] at hj hM hw
  have e₁ := Ξ.τ_eq (l, z) jL jM j₀ hL hj
  have e₂ := hf (l, z) jL hL
  have e₃ := (hF _ _ _ (Ξ.g (l, z)) _ (Ξ.x_fm (l, z)) _ (Ideal.Quotient.mk _) Ideal.mk_ker.ge).2
    ((insert 0 (F.map ι₀.symm.toEmbedding)).map ι₀.toEmbedding) jL jM jf jt
    (fun α hα => Finset.mem_map.2 ⟨ι₀.symm α, Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ hα),
      ι₀.apply_symm_apply α⟩) hL hM (fun α _ => cohCharts_congr hb (hc α))
  replace e₁ := (congrArg (· * _) hw).trans e₁
  generalize FormalValue.tau W.P.U.toUnifPre ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧))
    (Ξ.x (l, z)).left jL jM = t at e₁ e₃
  generalize FormalValue.secVal W.P.U.toUnifPre σ (Ξ.x (l, z)).left jL = s at e₂ e₃
  rw [pow_one] at e₂ e₃
  refine ⟨PowerSeries.C (Λ.u.fr j₀ z)⁻¹ * w * t⁻¹.val * s, ?_, ?_⟩
  · have e₄ : PowerSeries.C (Λ.u.fr j₀ z)⁻¹ * w * t⁻¹.val * Ξ.τ (l, z) jL = 1 := by
      have := t.inv_mul
      linear_combination (PowerSeries.C (Λ.u.fr j₀ z)⁻¹ * t⁻¹.val) * e₁ +
        (PowerSeries.C (Λ.u.fr j₀ z)⁻¹ * PowerSeries.C (Λ.u.fr j₀ z)) * this + hfr
    rw [map_mul, e₂, mul_left_comm, ← map_mul, e₄, map_one, _root_.mul_one]
  · have e₅ := Ideal.mul_mem_left _ (PowerSeries.C (Λ.u.fr j₀ z)⁻¹ * w * t⁻¹.val) (Ideal.Quotient.eq.1 e₃)
    rw [hJ, Ideal.span_singleton_pow, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at e₅
    have e₆ := e₅ e (Nat.lt_succ_self e)
    rw [mul_sub, map_sub, sub_eq_zero] at e₆
    refine e₆.trans (congrArg _ ?_)
    rw [_root_.mul_assoc _ t⁻¹.val, Units.inv_mul_cancel_left, Finset.sum_map, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have a₁ : FormalValue.famVal (Ξ.g (l, z)) (fam (ι₀ x)) (jf (ι₀ x)) =
        FormalValue.famVal (Ξ.g (0, z)) (fam (ι₀ x)) (jf (ι₀ x)) := congrArg (fun q => valR q _ _) hb'.symm
    have a₂ : FormalValue.coordVal (Ξ.g (l, z)) (ι₀ x) (jt (ι₀ x)) =
        PowerSeries.C (eTwoPi (l x)) * FormalValue.coordVal (Ξ.g (0, z)) (ι₀ x) (jt (ι₀ x)) :=
      coordVal_eq Ξ z x _ (hc (ι₀ x)).2.1 l
    refine (congrArg (_ * ·) (congrArg₂ (· * ·) a₁ a₂)).trans ?_
    simp only [B]
    ring

theorem exists_coeff_expansion (h : ThetaHyp W th σ fam) (hθ : Λ.u.IsFn th θ) {f : Λ.A.V → ℂ⸨X⸩} (hf : Ξ.Vals σ f)
    (z : Fin Λ.A.gB → ℂ) (n : ℤ) : ∃ (F : Finset Λ.A.X) (b : Λ.A.X → ℂ), 0 ∈ F ∧ b 0 = (if n = 0 then θ z else 0) ∧
      ∀ l : Λ.A.X →+ ℂ, (f (l, z)).coeff n = ∑ x ∈ F, b x * eTwoPi (l x) := by
  obtain ⟨F, B, hF, hB, hl⟩ := exists_expansion Ξ h hθ hf z n.natAbs
  refine ⟨F, fun x => if n < 0 then 0 else PowerSeries.coeff n.natAbs (B x), hF, ?_, fun l => ?_⟩
  · simp only [hB, PowerSeries.coeff_C, Int.natAbs_eq_zero]
    split_ifs with h₁ h₂
    · omega
    all_goals rfl
  · obtain ⟨p, hp, hc⟩ := hl l
    rw [hp, LaurentSeries.coe_algebraMap, PowerSeries.coeff_coe]
    split_ifs
    · simp
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [hc, map_sum]
        exact Finset.sum_congr rfl fun x _ => by rw [PowerSeries.coeff_C_mul, mul_comm]

theorem vals_FSum : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (th : a.D₀.P.L.Sec) (σ : Out.H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x) (θ : (Fin Λ.A.gB → ℂ) → ℂ), ThetaHyp W th σ fam → θ ∈ Λ.A.Theta 1 0 → Λ.u.IsFn th θ → Ξ.Vals σ (fun v => Λ.A.FSum 1 0 θ v) := by
  intro h₁ h₂ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ th σ fam θ h _ hθ
  obtain ⟨f, hc, hf, -⟩ := GlobalTheory.ConstSpan.main h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ 1 σ
  have e : f = fun v => Λ.A.FSum 1 0 θ v := funext (eq_FSum Λ.A hc θ (exists_coeff_expansion Ξ h hθ hf))
  exact e ▸ hf

end GlobalTheory.ArcPts.WeightZero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantTermWeightZeroSectionLevelOneFormalSumStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantTermWeightZero_section_levelOne_formalSum : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (th : a.D₀.P.L.Sec) (σ : Out.H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x) (θ : (Fin Λ.A.gB → ℂ) → ℂ), ThetaHyp W th σ fam → θ ∈ Λ.A.Theta 1 0 → Λ.u.IsFn th θ → Ξ.Vals σ (fun v => Λ.A.FSum 1 0 θ v) := by
  first | exact @GlobalTheory.ArcPts.WeightZero.vals_FSum | exact GlobalTheory.ArcPts.WeightZero.vals_FSum | (intros; apply GlobalTheory.ArcPts.WeightZero.vals_FSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcSectionValueAtSpecialisedPointsTheta
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section
namespace GlobalTheory.ArcSectionValue

theorem valR_res_const_res {A K : Type} [CommRing A] [CommRing K] {Z : Scheme.{0}} (p : Z ⟶ Sp K) (f : K →+* A)
    (q : Sp A ⟶ Z) (hq : q ≫ p = spMap f) {U U' V : Z.Opens} (h : V ≤ U) (h' : V ≤ U') (hV : ⊤ ≤ q ⁻¹ᵁ V)
    (a : Γ(Z, U)) (r : K) (b : Γ(Z, U')) :
    valR q V (resG Z h a * constFn p V r * resG Z h' b) = valR q U a * f r * valR q U' b := by
  rw [← HolHom.valR_res q h a hV, ← HolHom.valR_res q h' b hV, ← valR_const p f q hq V hV]
  simp only [HolHom.valR_eq _ V hV, map_mul]

theorem germ_identity {Γ : Germs} {w : ℂ} {Z Z' : Scheme.{0}} (x : Sp (Γ.R w) ⟶ Z) (φ : Z ⟶ Z') {xF : Sp ℂ⸨X⸩ ⟶ Z}
    (hx : spMap (Γ.R w).val.toRingHom ≫ x = xF) {U₀ U₁ : Z.Opens} {U : Z'.Opens} (h₀ : ⊤ ≤ x ⁻¹ᵁ U₀)
    (h₁ : ⊤ ≤ x ⁻¹ᵁ U₁) (h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U) {a₀ : Γ(Z, U₀)} {a₁ : Γ(Z, U₁)} {s : Γ(Z', U)} {ρ : ℂ⸨X⸩}
    (e : valR xF U₀ a₀ * valR (xF ≫ φ) U s = valR xF U₁ a₁ * ρ) :
    ((valR x U₀ a₀ : Γ.R w) : ℂ⸨X⸩) * (valR (x ≫ φ) U s : Γ.R w) = (valR x U₁ a₁ : Γ.R w) * ρ := by
  subst hx
  rwa [Category.assoc, HolHom.valR_spMap _ _ _ h₀, HolHom.valR_spMap _ _ _ h₁, HolHom.valR_spMap _ _ _ h] at e

theorem ev_identity {Γ : Germs} {w : ℂ} {Z Z' : Scheme.{0}} (x : Sp (Γ.R w) ⟶ Z) (φ : Z ⟶ Z')
    {U₀ U₁ : Z.Opens} {U : Z'.Opens} (h₀ : ⊤ ≤ x ⁻¹ᵁ U₀)
    (h₁ : ⊤ ≤ x ⁻¹ᵁ U₁) (h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U) {a₀ : Γ(Z, U₀)} {a₁ : Γ(Z, U₁)} {s : Γ(Z', U)} {T T' : ℝ}
    (hw : T < w.im) (hw' : T' < w.im) (ρ : Conv.halfRing T) (F : Conv.halfRing T') {t : Γ.R w}
    (e : ((valR x U₀ a₀ : Γ.R w) : ℂ⸨X⸩) * (valR (x ≫ φ) U s : Γ.R w) = (valR x U₁ a₁ : Γ.R w) * (ρ * F * t)) :
    valAt' (spMap (Γ.ev w).toRingHom ≫ x) U₀ a₀ * valAt' ((spMap (Γ.ev w).toRingHom ≫ x) ≫ φ) U s =
      valAt' (spMap (Γ.ev w).toRingHom ≫ x) U₁ a₁ * (Conv.ev T w hw ρ * Conv.ev T' w hw' F * Γ.ev w t) := by
  have e' : valR x U₀ a₀ * valR (x ≫ φ) U s = valR x U₁ a₁ *
      (Subalgebra.inclusion (Γ.le T w hw) ρ * Subalgebra.inclusion (Γ.le T' w hw') F * t) := Subtype.ext e
  have e'' := congrArg (Γ.ev w) e'
  rw [map_mul, map_mul, map_mul, map_mul, Γ.ev_eq, Γ.ev_eq] at e''
  rw [HolHom.valAt'_eq_valR, HolHom.valAt'_eq_valR, HolHom.valAt'_eq_valR, Category.assoc,
    HolHom.valR_spMap _ _ _ h₀, HolHom.valR_spMap _ _ _ h₁, HolHom.valR_spMap _ _ _ h]
  exact e''

theorem mem_convLaurent_of_germ {Γ : Germs} {w : ℂ} {x₀ y x₁ t : Γ.R w} {ρ F : ℂ⸨X⸩}
    (e : (x₀ : ℂ⸨X⸩) * y = x₁ * (ρ * F * t)) (h₁ : IsUnit x₁) (ht : IsUnit t) (hF : F ≠ 0)
    (hF' : F ∈ Conv.convLaurent) : ρ ∈ Conv.convLaurent := by
  have u₁ : (x₁ : ℂ⸨X⸩) ≠ 0 := (h₁.map (Γ.R w).val).ne_zero
  have u₀ : (t : ℂ⸨X⸩) ≠ 0 := (ht.map (Γ.R w).val).ne_zero
  have : ρ = x₀ * y / (x₁ * F * t) := by
    rw [e]
    field_simp
  rw [this]
  exact div_mem (mul_mem (germ_mem_convLaurent Γ w _) (germ_mem_convLaurent Γ w _))
    (mul_mem (mul_mem (germ_mem_convLaurent Γ w _) hF') (germ_mem_convLaurent Γ w _))

section Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable {Y : Model Xo c β} [Algebra (FractionRing ℂ) ℂ] {bF : c.F →+* ℂ} {a : ArcIn D l β ℂ (bF.comp β)}
  {χ : Sp ℂ⟦X⟧ ⟶ Y.X}
  {W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ} {Λ : GtAn a}

theorem isProper_gen (C : Chain W Λ) : IsProper (pullback.snd W.t.G.hom gen) := by
  haveI := Y.oF.proper
  have h1 : IsPullback (pullback.fst W.t.G.hom gen ≫ W.m.φ) (pullback.snd W.t.G.hom gen) Y.t.G.hom (gen ≫ χ) :=
    (IsPullback.of_hasPullback W.t.G.hom gen).paste_horiz W.m.cart.1
  have h2 : IsPullback (pullback.fst Y.oF.t.G.hom C.yF ≫ Y.m.φ) (pullback.snd Y.oF.t.G.hom C.yF) Y.t.G.hom
      (C.yF ≫ Y.j) := (IsPullback.of_hasPullback Y.oF.t.G.hom C.yF).paste_horiz Y.m.cart.1
  rw [C.yF_j] at h2
  rw [← h1.isoIsPullback_hom_snd _ _ h2]
  infer_instance

theorem valR_section_model (hL : Out.Laws) (hL2 : Out.Laws2) (C : Chain W Λ) {σ : Out.H0 W.P.U.LG.L 1}
    {f : Λ.A.V → ℂ⸨X⸩} (hf : C.Ξ.Vals σ f) {w₂ : LB.Iso W.P.U.LG.L (Y.t.PP.L.pull W.m.φ)}
    (hw₂ : IsRigIso W.m.cm W.P.U.LG Y.t.PP w₂) {U : Y.X.Opens} (hU : ⊤ ≤ χ ⁻¹ᵁ U)
    {s : ∀ j, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j)} {r : PowerSeries ℂ} (hp : PullHyp W σ w₂ U s r)
    (v : Λ.A.V) (j : Y.t.PP.L.ι) (hj : ⊤ ≤ (C.ΦY.x v).left ⁻¹ᵁ Y.t.PP.L.U j) :
    valR (C.ΦY.x v).left _ (s j) = (r : ℂ⸨X⸩) * f v * C.ΦY.τ v j := by
  obtain ⟨k₁, hk₁⟩ := exists_chart_local (A := ℂ⟦X⟧) (C.Ξ.x v).left W.P.U.LG.isLB
  obtain ⟨w', k₂, hw', hk, hUk, hval⟩ := exists_rigIso_of_eq (A := ℂ⸨X⸩) W.m.cm W.P.bundle Y.t.PP w₂ hw₂ k₁
  obtain ⟨hx, hτ⟩ := C.isGen v
  obtain ⟨hxY, hrel⟩ := C.rel₂.2 v
  have hk₁' : ⊤ ≤ (C.ΦW.x v).left ⁻¹ᵁ W.P.U.LG.L.U k₁ := hx ▸ FormalValue.top_le_comp hk₁ _
  have hj' : ⊤ ≤ ((C.ΦW.x v).left ≫ W.m.φ) ⁻¹ᵁ Y.t.PP.L.U j := hxY ▸ hj
  have hd₁ := (le_div_iff (C.ΦW.x v).left W.m.φ Y.t.PP.L W.P.U.LG.L j k₁).2 ⟨hj', hk₁'⟩
  have hd₂ := (le_div_iff (C.ΦW.x v).left W.m.φ Y.t.PP.L W.t.PP.L j k₂).2 ⟨hj', hUk ▸ hk₁'⟩
  have hw := (GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres hL hL2 E H _ _ Y.t W.t χ W.m).2 w' C.w₂ hw' C.rig₂ _ gen (C.ΦW.x v) (isProper_gen C) j k₂ hd₂
  have hover : (C.ΦW.x v).left ≫ W.t.G.hom = gen := Over.w (C.ΦW.x v)
  have h₁ : ⊤ ≤ (C.ΦW.x v).left ⁻¹ᵁ (W.m.φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j)) := by
    have : ⊤ ≤ ((C.ΦW.x v).left ≫ W.m.φ ≫ Y.t.G.hom) ⁻¹ᵁ U := by
      rw [W.m.cart.1.w, reassoc_of% hover]
      exact FormalValue.top_le_comp hU _
    exact fun z hz => ⟨this hz, hj' hz⟩
  have h₃ : ⊤ ≤ (C.Ξ.x v).left ⁻¹ᵁ LB.wchart W.P.U.LG.L (fun _ : Fin 1 => 𝟙 W.t.G.left) (fun _ => k₁) :=
    fun z hz => Set.mem_iInter.2 fun _ => hk₁ hz
  have h₃' : ⊤ ≤ (C.ΦW.x v).left ⁻¹ᵁ LB.wchart W.P.U.LG.L (fun _ : Fin 1 => 𝟙 W.t.G.left) (fun _ => k₁) :=
    hx ▸ FormalValue.top_le_comp h₃ _
  let V : W.t.G.left.Opens := W.m.φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j) ⊓
    ((LB.div (Y.t.PP.L.pull W.m.φ) W.P.U.LG.L).U (fun _ => j, k₁) ⊓
      LB.wchart W.P.U.LG.L (fun _ : Fin 1 => 𝟙 W.t.G.left) (fun _ => k₁))
  have hV : ⊤ ≤ (C.ΦW.x v).left ⁻¹ᵁ V := fun z hz => ⟨h₁ hz, hd₁ hz, h₃' hz⟩
  have key := ((HolHom.valR_appLE _ _ _ _ _ _ hV).symm.trans (congrArg (valR (C.ΦW.x v).left V)
    (hp j k₁ V inf_le_left (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)))).trans
    (valR_res_const_res _ _ _ hover _ _ hV _ _ _)
  have hσ : valR (C.ΦW.x v).left _ (σ.f (fun _ => k₁)) = f v * C.ΦW.τ v k₂ := by
    rw [hτ k₁ k₂ hk hk₁, ← pow_one (algebraMap ℂ⟦X⟧ ℂ⸨X⸩ _), ← hf v k₁ hk₁, hx]
    exact HolHom.valR_spMap _ _ _ h₃ _
  rw [← hxY, hrel j k₂ hd₂, ← hw, ← hval]
  refine key.trans ?_
  refine (congrArg (_ * ·) hσ).trans ?_
  change _ * (r : ℂ⸨X⸩) * _ = _
  ring

theorem valR_section_generic (hL : Out.Laws) (hL2 : Out.Laws2) (C : Chain W Λ) {σ : Out.H0 W.P.U.LG.L 1}
    {f : Λ.A.V → ℂ⸨X⸩} (hf : C.Ξ.Vals σ f) {w₂ : LB.Iso W.P.U.LG.L (Y.t.PP.L.pull W.m.φ)}
    {w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)}
    {w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)}
    (hw₂ : IsRigIso W.m.cm W.P.U.LG Y.t.PP w₂) (hw₁ : IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁)
    (hw₀ : IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀) {U : Y.X.Opens} (hU : ⊤ ≤ χ ⁻¹ᵁ U)
    {s : ∀ j, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j)} {r : PowerSeries ℂ} (hp : PullHyp W σ w₂ U s r)
    (v : Λ.A.V) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι)
    (h₁ : ⊤ ≤ (C.ΦF.x v).left ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k))
    (h₀ : ⊤ ≤ (C.ΦF.x v).left ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k)) :
    valR (C.ΦF.x v).left _ (w₀.s (fun _ => j₀, k)).val * valR ((C.ΦF.x v).left ≫ Y.m.φ) _ (s j) =
      valR (C.ΦF.x v).left _ (w₁.s (fun _ => j, k)).val * ((r : ℂ⸨X⸩) * f v * C.Φ.τ v j₀) := by
  haveI := Y.oF.proper
  obtain ⟨hx₁, hr₁⟩ := C.rel₁.2 v
  have e₁ := (GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres hL hL2 E H _ _ Y.t Y.oF.t _ Y.m).2 w₁ C.w₁ hw₁ C.rig₁ _ C.yF (C.ΦF.x v) inferInstance j k h₁
  have e₀ := (GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres hL hL2 E H _ _ Xo.univ.t Y.oF.t _ Y.m0.toSABMap).2 w₀ C.w₀ hw₀ C.rig₀ _ C.yF (C.ΦF.x v)
    inferInstance j₀ k h₀
  have hj := ((le_div_iff _ _ _ _ _ _).1 h₁).1
  have e₂ := valR_section_model hL hL2 C hf hw₂ hU hp v j (hx₁ ▸ hj)
  have e₃ := hr₁ j k h₁
  have e₄ := (C.rel₀.2 v).2 j₀ k h₀
  have aux : ∀ {x₀ x₀' x₁ x₁' y ρ t t₀ t₁ : ℂ⸨X⸩}, x₁ = x₁' → x₀ = x₀' → y = ρ * t₁ → t₁ = x₁' * t → t₀ = x₀' * t →
      x₀ * y = x₁ * (ρ * t₀) := by
    rintro _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl
    ring
  exact aux e₁ e₀ ((congrArg (valR · _ (s j)) hx₁).trans e₂) e₃ e₄

variable (hL : Out.Laws) (hL2 : Out.Laws2) (C : Chain W Λ) {σ : Out.H0 W.P.U.LG.L 1}
  {f : Λ.A.V → ℂ⸨X⸩} (hf : C.Ξ.Vals σ f) {w₂ : LB.Iso W.P.U.LG.L (Y.t.PP.L.pull W.m.φ)}
  {w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)}
  {w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)}
  (hw₂ : IsRigIso W.m.cm W.P.U.LG Y.t.PP w₂) (hw₁ : IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁)
  (hw₀ : IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀) {U : Y.X.Opens} (hU : ⊤ ≤ χ ⁻¹ᵁ U)
  {s : ∀ j, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j)} {r : PowerSeries ℂ} (hp : PullHyp W σ w₂ U s r)
  {Γ : Germs} (Ψ : SpecPts C.Φ Γ) {w : ℂ} (hw : Ψ.T < w.im) (v : Λ.A.V) (xg : Sp (Γ.R w) ⟶ Y.oF.t.G.left)
  (e₀ : xg ≫ Y.m0.toSABMap.φ = (Ψ.xt w hw v).left) (eg : spMap (Γ.R w).val.toRingHom ≫ xg = (C.ΦF.x v).left)
  (hxU : ⊤ ≤ (xg ≫ Y.oF.t.G.hom) ⁻¹ᵁ (Y.j ⁻¹ᵁ U))


omit [StarRing (𝓞 E)] in
include hxU in
theorem le_section_dom {j : Y.t.PP.L.ι} (hj : ⊤ ≤ (xg ≫ Y.m.φ) ⁻¹ᵁ Y.t.PP.L.U j) :
    ⊤ ≤ (xg ≫ Y.m.φ) ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j) := by
  have : ⊤ ≤ (xg ≫ Y.m.φ ≫ Y.t.G.hom) ⁻¹ᵁ U := by
    rw [Y.m.cart.1.w]
    exact hxU
  exact fun z hz => ⟨this hz, hj hz⟩

include hL hL2 hf hw₂ hw₁ hw₀ hU hp e₀ eg hxU

theorem valR_section_germ (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι)
    (h₁ : ⊤ ≤ xg ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k))
    (h₀ : ⊤ ≤ xg ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k)) :
    ((valR xg _ (w₀.s (fun _ => j₀, k)).val : Γ.R w) : ℂ⸨X⸩) * (valR (xg ≫ Y.m.φ) _ (s j) : Γ.R w) =
      (valR xg _ (w₁.s (fun _ => j, k)).val : Γ.R w) * ((r : ℂ⸨X⸩) * f v * Ψ.τt w v j₀) := by
  have hs := le_section_dom xg hxU ((le_div_iff _ _ _ _ _ _).1 h₁).1
  have hj₀ := ((le_div_iff _ _ _ _ _ _).1 h₀).1
  rw [e₀] at hj₀
  have h₁' := FormalValue.top_le_comp h₁ (spMap (Γ.R w).val.toRingHom)
  have h₀' := FormalValue.top_le_comp h₀ (spMap (Γ.R w).val.toRingHom)
  rw [eg] at h₁' h₀'
  rw [Ψ.τt_gen w hw v j₀ hj₀]
  exact germ_identity xg Y.m.φ eg h₀ h₁ hs (valR_section_generic hL hL2 C hf hw₂ hw₁ hw₀ hU hp v j k j₀ h₁' h₀')

theorem factor_mem_convLaurent (hv : f v ≠ 0) (hv' : f v ∈ Conv.convLaurent) : (r : ℂ⸨X⸩) ∈ Conv.convLaurent := by
  have := isLocalRing_germ Γ w
  obtain ⟨j, hj⟩ := exists_chart_local (xg ≫ Y.m.φ) Y.t.PP.isLB
  obtain ⟨k, hk⟩ := exists_chart_local xg Y.oF.t.PP.isLB
  obtain ⟨j₀, hj₀⟩ := exists_chart_local (xg ≫ Y.m0.toSABMap.φ) Xo.univ.t.PP.isLB
  have h₁ := (le_div_iff _ _ _ _ _ _).2 ⟨hj, hk⟩
  have h₀ := (le_div_iff _ _ _ _ _ _).2 ⟨hj₀, hk⟩
  have e := valR_section_germ hL hL2 C hf hw₂ hw₁ hw₀ hU hp Ψ hw v xg e₀ eg hxU j k j₀ h₁ h₀
  rw [e₀] at hj₀
  exact mem_convLaurent_of_germ e (FormalValue.isUnit_valR xg _ h₁ _) ((Ψ.τt_frm w hw v).1 j₀ hj₀) hv hv'

theorem valAt_section {T₀ T₂ : ℝ} (hw0 : T₀ < w.im) (hw2 : T₂ < w.im) (hF : f v ∈ Conv.halfRing T₀)
    (hr : (r : ℂ⸨X⸩) ∈ Conv.halfRing T₂) {S : ℂ} (hS : Conv.ev T₀ w hw0 ⟨_, hF⟩ = S) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι)
    (x : Sp ℂ ⟶ Y.oF.t.G.left) (hx : x = spMap (Γ.ev w).toRingHom ≫ xg)
    (h₁ : ⊤ ≤ x ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k))
    (h₀ : ⊤ ≤ x ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k)) :
    valAt' x _ (w₀.s (fun _ => j₀, k)).val * valAt' (x ≫ Y.m.φ) _ (s j) =
      valAt' x _ (w₁.s (fun _ => j, k)).val *
        (Conv.ev T₂ w hw2 ⟨_, hr⟩ * S * Ψ.fr w j₀ v) := by
  subst hx hS
  have h₁' := le_of_ev Γ w xg h₁
  have h₀' := le_of_ev Γ w xg h₀
  exact ev_identity xg Y.m.φ h₀' h₁' (le_section_dom xg hxU ((le_div_iff _ _ _ _ _ _).1 h₁').1) hw2 hw0 ⟨_, hr⟩ ⟨_, hF⟩
    (valR_section_germ hL hL2 C hf hw₂ hw₁ hw₀ hU hp Ψ hw v xg e₀ eg hxU j k j₀ h₁' h₀')

end Generic

theorem section_value : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ) (Γ : Germs) (Ψ : SpecPts C.Φ Γ) (th : a.D₀.P.L.Sec) (σ : Out.H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x) (θ : (Fin Λ.A.gB → ℂ) → ℂ) (w₂ : LB.Iso W.P.U.LG.L (Y.t.PP.L.pull W.m.φ)) (w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)) (w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)) (U : Y.X.Opens) (s : ∀ j, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j)) (r : PowerSeries ℂ), AnFin Λ.A → ThetaHyp W th σ fam → θ ∈ Λ.A.Theta 1 0 → θ ≠ 0 → Λ.u.IsFn th θ → IsRigIso W.m.cm W.P.U.LG Y.t.PP w₂ → IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁ → IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀ → ⊤ ≤ χ ⁻¹ᵁ U → PullHyp W σ w₂ U s r → ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∃ rw : ℂ, SumsAt r w rw ∧ ∀ (v : Λ.A.V) (x : Sp ℂ ⟶ Y.oF.t.G.left) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι), x ≫ Y.m0.toSABMap.φ = (Ψ.pi w v).left → x ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap bF → ⊤ ≤ x ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k) → ⊤ ≤ x ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k) → valAt' x _ (w₀.s (fun _ => j₀, k)).val * valAt' (x ≫ Y.m.φ) _ (s j) = valAt' x _ (w₁.s (fun _ => j, k)).val * (rw * Λ.A.Sum 1 0 θ w v * Ψ.fr w j₀ v) := by
  intro hL hL2 E _ _ _ H _ D l Xo c O _ β Y _ _ bF a χ W Λ C Γ Ψ th σ fam θ w₂ w₁ w₀ U s r _ hth hθ hθ0 hfn hw₂ hw₁ hw₀
    hU hp
  have hf := GlobalTheory.T.constantTermWeightZero_section_levelOne_formalSum hL hL2 E H D l Xo c O β Y _ a χ W Λ C.Ξ th σ fam θ hth hθ hfn
  refine Λ.A.exists_isConvLine.elim fun T₀ hT₀ => ?_
  have hF : ∀ v, Λ.A.FSum 1 0 θ v ∈ Conv.halfRing T₀ := fun v _ hw => (AnArc.hasSum_coeff_FSum hT₀ hθ hw v).summable
  have hUF : ⊤ ≤ C.yF ⁻¹ᵁ (Y.j ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, C.yF_j]
    exact FormalValue.top_le_comp hU _
  refine (exists_germ_lift Y bF C.yF_over C.ΦF (fun v => (C.rel₀.2 v).1) Ψ _ hUF).elim fun T₁ hlift => ?_
  have hr : (r : ℂ⸨X⸩) ∈ Conv.convLaurent :=
    (exists_fsum_ne_zero Λ.A hθ0).elim fun v hv =>
      (hlift (((T₁ + 1 : ℝ) : ℂ) * Complex.I) (by simp)).elim fun hw hl => (hl v).elim fun xg h =>
        factor_mem_convLaurent hL hL2 C hf hw₂ hw₁ hw₀ hU hp Ψ hw v xg h.1 h.2.1 h.2.2.1 hv
          (Conv.halfRing_le_convLaurent T₀ (hF v))
  refine (Conv.mem_convLaurent_iff_halfRing.1 hr).elim fun T₂ hT₂ => ⟨max T₀ (max T₁ T₂), fun w hw' => ?_⟩
  have hw0 := (max_lt_iff.1 hw').1
  have hw1 := (max_lt_iff.1 (max_lt_iff.1 hw').2).1
  have hw2 := (max_lt_iff.1 (max_lt_iff.1 hw').2).2
  refine ⟨Conv.ev T₂ w hw2 ⟨_, hT₂⟩, Conv.sumsAt_ev hw2 hT₂, fun v x j k j₀ hx₁ hx₂ h₁ h₀ => ?_⟩
  exact (hlift w hw1).elim fun hw hl => (hl v).elim fun xg h =>
    valAt_section hL hL2 C hf hw₂ hw₁ hw₀ hU hp Ψ hw v xg h.1 h.2.1 h.2.2.1 hw0 hw2 (hF v) hT₂
      (Conv.ev_eq_of_hasSum hw0 ⟨_, hF v⟩ (AnArc.hasSum_coeff_FSum hT₀ hθ hw0 v)) j k j₀ x (h.2.2.2 x hx₁ hx₂) h₁ h₀

end GlobalTheory.ArcSectionValue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcSectionValueAtSpecialisedPointsThetaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcSection_value_at_specialised_points_theta : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ) (Γ : Germs) (Ψ : SpecPts C.Φ Γ) (th : a.D₀.P.L.Sec) (σ : Out.H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x) (θ : (Fin Λ.A.gB → ℂ) → ℂ) (w₂ : LB.Iso W.P.U.LG.L (Y.t.PP.L.pull W.m.φ)) (w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)) (w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)) (U : Y.X.Opens) (s : ∀ j, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j)) (r : PowerSeries ℂ), AnFin Λ.A → ThetaHyp W th σ fam → θ ∈ Λ.A.Theta 1 0 → θ ≠ 0 → Λ.u.IsFn th θ → IsRigIso W.m.cm W.P.U.LG Y.t.PP w₂ → IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁ → IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀ → ⊤ ≤ χ ⁻¹ᵁ U → PullHyp W σ w₂ U s r → ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∃ rw : ℂ, SumsAt r w rw ∧ ∀ (v : Λ.A.V) (x : Sp ℂ ⟶ Y.oF.t.G.left) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι), x ≫ Y.m0.toSABMap.φ = (Ψ.pi w v).left → x ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap bF → ⊤ ≤ x ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k) → ⊤ ≤ x ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k) → valAt' x _ (w₀.s (fun _ => j₀, k)).val * valAt' (x ≫ Y.m.φ) _ (s j) = valAt' x _ (w₁.s (fun _ => j, k)).val * (rw * Λ.A.Sum 1 0 θ w v * Ψ.fr w j₀ v) := by
  first | exact @GlobalTheory.ArcSectionValue.section_value | exact GlobalTheory.ArcSectionValue.section_value | (intros; apply GlobalTheory.ArcSectionValue.section_value <;> assumption)
end
