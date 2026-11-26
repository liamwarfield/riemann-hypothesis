module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagMemDoubledVacuumLatticeStabilizer
public import Formalism.MeanHeightDescent.AverageDegreeBounds.SumComponents

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormLeOneIffLogValuation
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsEigFrameOfFrPt
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.RuleVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

section Values

variable (T : Formalism.L2.Pj.CDVR)

theorem norm_eq_zpow {C : Type} [NormedField C] (j : T.Fr →+* C)
    (h1 : ∀ a : T.V, ‖j (algebraMap T.V T.Fr a)‖ ≤ 1) {π : T.V} (hπ : Irreducible π) {x : T.Fr} (hx : x ≠ 0) :
    ‖j x‖ = ‖j (algebraMap T.V T.Fr π)‖ ^ Formalism.L2.Pj.vV T.V x := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ hx
  have hu : ‖j (algebraMap T.V T.Fr u)‖ = 1 := by
    have h : ‖j (algebraMap T.V T.Fr u)‖ * ‖j (algebraMap T.V T.Fr (u⁻¹ : T.Vˣ))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    refine le_antisymm (h1 _) ?_
    calc (1 : ℝ) = _ := h.symm
      _ ≤ ‖j (algebraMap T.V T.Fr u)‖ * 1 := mul_le_mul_of_nonneg_left (h1 _) (norm_nonneg _)
      _ = _ := mul_one _
  have hv : Formalism.L2.Pj.vV T.V (u • algebraMap T.V T.Fr π ^ n) = n := by
    rw [Formalism.L2.Pj.vV, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀,
      GlobalTheory.PlaceCompletion.valV_algebraMap_of_isUnit u.isUnit,
      GlobalTheory.PlaceCompletion.valV_algebraMap_of_irreducible hπ, _root_.one_mul, ← WithZero.exp_zsmul,
      WithZero.log_exp]
    simp
  rw [hv, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, norm_mul, norm_zpow, hu, _root_.one_mul]

theorem norm_le_one_of_mem {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) (h : x ∈ 𝓞_ℂ_[p]) : ‖x‖ ≤ 1 := by
  suffices hs : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 from hs.1 h
  rw [PadicComplex.norm_eq_norm, Valuation.norm_def, ← NNReal.coe_one, NNReal.coe_le_coe,
    ← map_one (Valuation.RankOne.hom (PadicComplex.valued p).v),
    (Valuation.RankOne.strictMono _).le_iff_le, Valuation.restrict_le_one_iff]
  rfl

theorem exists_embed (hT : T.FinRes) :
    ∃ (p : Nat.Primes) (j : T.Fr →+* ℂ_[p]), ∀ a : T.Fr, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap T.V T.Fr).range := by
  obtain ⟨p, hp, k, kO, hk⟩ := GlobalTheory.CompleteDvrEmbedding.exists_embedding_padicComplexInt T hT
  have h1 : ∀ a : T.V, ‖k (algebraMap T.V T.Fr a)‖ ≤ 1 := fun a => by
    rw [← hk]
    exact (norm_le_one_of_mem _ (kO a).2)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  have hc0 : CharZero T.Fr := charZero_of_injective_ringHom (IsFractionRing.injective T.V T.Fr)
  have hlt : ‖k (algebraMap T.V T.Fr π)‖ < 1 := by
    by_contra hc
    have he : ‖k (algebraMap T.V T.Fr π)‖ = 1 := le_antisymm (h1 π) (not_lt.mp hc)
    have := norm_eq_zpow T k h1 hπ (x := (p : T.Fr)) (Nat.cast_ne_zero.2 hp.out.ne_zero)
    rw [he, one_zpow, map_natCast] at this
    have h3 : ‖(p : ℂ_[p])‖ < 1 := by
      have e : ((p : ℕ) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
      rw [e, norm_algebraMap']
      exact Padic.norm_p_lt_one
    exact h3.ne this
  have hpos : 0 < ‖k (algebraMap T.V T.Fr π)‖ := norm_pos_iff.2 ((map_ne_zero k).2
    ((map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 hπ.ne_zero))
  refine ⟨⟨p, hp.out⟩, k, fun x => ⟨fun hx => ?_, by rintro ⟨a, rfl⟩; exact h1 a⟩⟩
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  rcases ValuationRing.isInteger_or_isInteger T.V x with ⟨a, ha⟩ | ⟨a, ha⟩
  · exact ⟨a, ha⟩
  · by_cases hu : IsUnit a
    · obtain ⟨u, rfl⟩ := hu
      refine ⟨(u⁻¹ : T.Vˣ), ?_⟩
      have : algebraMap T.V T.Fr (u⁻¹ : T.Vˣ) * algebraMap T.V T.Fr u = 1 := by
        rw [← map_mul]; simp
      rw [ha] at this
      field_simp at this
      exact this
    · exfalso
      have hm : a ∈ Ideal.span {π} := by rw [← hπ.maximalIdeal_eq]; exact hu
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.1 hm
      have h3 : ‖k x⁻¹‖ < 1 := by
        rw [← ha, map_mul, map_mul, norm_mul]
        calc _ ≤ ‖k (algebraMap T.V T.Fr π)‖ * 1 := mul_le_mul_of_nonneg_left (h1 b) (norm_nonneg _)
          _ < 1 := by simpa using hlt
      rw [map_inv₀, norm_inv] at h3
      have hp' : 0 < ‖k x‖ := norm_pos_iff.2 ((map_ne_zero k).2 h0)
      have := (inv_lt_one₀ hp').1 h3
      linarith

theorem exists_log_norm {C : Type} [NormedField C] (j : T.Fr →+* C)
    (hj : ∀ a : T.Fr, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap T.V T.Fr).range) :
    ∃ ρ : ℝ, ρ < 0 ∧ ∀ x : T.Fr, x ≠ 0 → Real.log ‖j x‖ = Formalism.L2.Pj.vV T.V x * ρ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  have h1 : ∀ a : T.V, ‖j (algebraMap T.V T.Fr a)‖ ≤ 1 := fun a => (hj _).2 ⟨a, rfl⟩
  have hne : algebraMap T.V T.Fr π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 hπ.ne_zero
  have hpos : 0 < ‖j (algebraMap T.V T.Fr π)‖ := norm_pos_iff.2 ((map_ne_zero j).2 hne)
  have hlt : ‖j (algebraMap T.V T.Fr π)‖ < 1 := by
    refine lt_of_le_of_ne (h1 π) fun he => ?_
    have : ‖j (algebraMap T.V T.Fr π)⁻¹‖ ≤ 1 := by rw [map_inv₀, norm_inv, he, inv_one]
    obtain ⟨b, hb⟩ := (hj _).1 this
    refine hπ.not_isUnit (IsUnit.of_mul_eq_one b ?_)
    apply IsFractionRing.injective T.V T.Fr
    rw [map_mul, hb, map_one, mul_inv_cancel₀ hne]
  refine ⟨Real.log ‖j (algebraMap T.V T.Fr π)‖, Real.log_neg hpos hlt, fun x hx => ?_⟩
  rw [norm_eq_zpow T j h1 hπ hx, Real.log_zpow]

end Values

section Pre

variable {S : Scheme.{0}} {A B G : Over S} [GrpObj G]

theorem pre_one (g : A ⟶ B) : g ≫ (1 : B ⟶ G) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (g ≫ toUnit B) (toUnit A)]

theorem pre_prod (g : A ⟶ B) {m : ℕ} (u : Fin m → (B ⟶ G)) :
    g ≫ (List.ofFn u).prod = (List.ofFn fun i => g ≫ u i).prod := by
  let f : (B ⟶ G) →* (A ⟶ G) :=
    { toFun := (g ≫ ·), map_one' := pre_one g, map_mul' := fun a b => by
        show g ≫ (a * b) = (g ≫ a) * (g ≫ b)
        rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift] }
  have := map_list_prod f (List.ofFn u)
  simpa [List.map_ofFn, f, Function.comp_def] using this

end Pre

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem mult_conj (τ : E →+* ℂ) (h : τ (H.rt : E) = H.rt0) : D.mult (ComplexEmbedding.conjugate τ) = D.q := by
  have hd : (H.d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  have hd' : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h0 := H.sqrt_neg_disc_sq
  have hre := congrArg Complex.re h0
  have him := congrArg Complex.im h0
  simp [pow_two] at hre him
  have hr : H.rt0.re = 0 := by
    by_contra hne
    have h1 : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [h1] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  have hi : H.rt0.im ≠ 0 := by
    intro h1
    rw [hr, h1] at hre
    simp at hre
    exact H.d_prime.ne_zero hre
  unfold Datum.mult
  rw [if_neg]
  rw [ComplexEmbedding.conjugate_coe_eq, h]
  intro h2
  exact hi (by have := congrArg Complex.im h2; simp at this; linarith)

theorem exists_vecs {K : Type} [Field K] [Algebra c.F K] (z : Formalism.L2.Pj.FrPt Xo c K) {x : Sp K ⟶ Xo.X}
    (hx : x = z.x) (τ' : E →+* ℂ) {n : ℕ} (hn : D.mult τ' = n) :
    ∃ v : Fin n → (epsAt x ⟶ Xo.univ.t.G), ∀ i, (v i).left = z.u τ' (i.cast hn.symm) := by
  subst hx
  exact ⟨fun i => Over.homMk (z.u τ' (i.cast hn.symm)) (z.tan τ' _).1, fun i => rfl⟩

theorem isEigFrame_of_frPt {K : Type} [Field K] [Algebra c.F K] (z : Formalism.L2.Pj.FrPt Xo c K) {x : Sp K ⟶ Xo.X}
    (hx : x = z.x) (τ' : E →+* ℂ) {n : ℕ} (hn : D.mult τ' = n) (v : Fin n → (epsAt x ⟶ Xo.univ.t.G))
    (hv : ∀ i, (v i).left = z.u τ' (i.cast hn.symm)) :
    IsEigFrame Xo.univ.t.act x ((algebraMap c.F K).comp (tauIn c τ')) v := by
  subst hx
  subst hn
  have hv' : ∀ i, (v i).left = z.u τ' i := fun i => by simpa using hv i
  refine ⟨fun i => ⟨?_, fun a => ?_⟩, fun w hw => ?_⟩
  · show _ ≫ (v i).left = _
    rw [hv']
    exact (z.tan τ' i).2
  · rw [Over.comp_left, hv']
    exact z.eig τ' i a
  · have hb := z.basis τ' w.left ⟨Over.w w, hw.1⟩ (fun a => hw.2 a)
    obtain ⟨a, ⟨u, hu1, hu2⟩, huniq⟩ := hb
    refine ⟨a, ⟨u, fun i => ?_, ?_⟩, fun b hb => huniq b ?_⟩
    · rw [hv']; exact hu1 i
    · exact Over.OverMorphism.ext hu2.symm
    · obtain ⟨u', h1, h2⟩ := hb
      exact ⟨u', fun i => by rw [h1 i, hv']; rfl, congrArg (·.left) h2.symm⟩

theorem exists_cast {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f g : S' ⟶ S} (h : f = g)
    (m : SABMap t' t f) : ∃ m' : SABMap t' t g, m'.φ = m.φ := by
  subst h
  exact ⟨m, rfl⟩

theorem exists_lift_int (T : Formalism.L2.Pj.CDVR) (f : 𝓞 E →+* T.Fr) :
    ∃ σ : 𝓞 E →+* T.V, (algebraMap T.V T.Fr).comp σ = f := by
  have h : ∀ a, f a ∈ (algebraMap T.V T.Fr).range := fun a => by
    have hi : IsIntegral ℤ a := RingOfIntegers.isIntegral a
    have hV : IsIntegral T.V (f a) := by
      obtain ⟨q, hqm, hq⟩ := hi
      refine ⟨q.map (Int.castRingHom T.V), hqm.map _, ?_⟩
      rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap T.V T.Fr).comp (Int.castRingHom T.V))
        (f.comp (algebraMap ℤ (𝓞 E))), ← Polynomial.hom_eval₂, hq, map_zero]
    exact IsIntegrallyClosed.isIntegral_iff.1 hV
  let e : T.V ≃+* (algebraMap T.V T.Fr).range := RingEquiv.ofBijective (algebraMap T.V T.Fr).rangeRestrict
    ⟨fun a b hab => IsFractionRing.injective T.V T.Fr (congrArg Subtype.val hab),
      (algebraMap T.V T.Fr).rangeRestrict_surjective⟩
  refine ⟨(e.symm : _ →+* _).comp (f.codRestrict _ h), RingHom.ext fun a => ?_⟩
  have := e.apply_symm_apply (f.codRestrict _ h a)
  exact congrArg Subtype.val this

theorem eps_hom (V : Type) [CommRing V] : spMap (algebraMap V (DualNumber V)) ≫ 𝟙 (Sp V) =
    spMap ((algebraMap V (DualNumber V)).comp (algebraMap V V)) := by
  rw [Category.comp_id, Algebra.algebraMap_self, RingHom.comp_id]

theorem pt_hom (V : Type) [CommRing V] : spMap (algebraMap V V) = 𝟙 (Sp V) := by
  rw [Algebra.algebraMap_self]
  exact (congrArg Spec.map CommRingCat.ofHom_id).trans (Spec.map_id _)

def toAt (V : Type) [CommRing V] : epsOver V V ⟶ epsAt (𝟙 (Sp V)) :=
  Over.homMk (𝟙 _) ((Category.id_comp _).trans (eps_hom V))

def ofAt (V : Type) [CommRing V] : epsAt (𝟙 (Sp V)) ⟶ epsOver V V :=
  Over.homMk (𝟙 _) ((Category.id_comp _).trans (eps_hom V).symm)

theorem ofAt_toAt (V : Type) [CommRing V] : ofAt V ≫ toAt V = 𝟙 _ :=
  Over.OverMorphism.ext (Category.comp_id _)

def ptAt (V : Type) [CommRing V] : Over.mk (𝟙 (Sp V)) ⟶ ptOver V V :=
  Over.homMk (𝟙 _) ((Category.id_comp _).trans (pt_hom V))

theorem one_left_at (V : Type) [CommRing V] (G : Over (Sp V)) [GrpObj G] :
    (1 : Over.mk (𝟙 (Sp V)) ⟶ G).left = (1 : ptOver V V ⟶ G).left := by
  have h : ptAt V ≫ (1 : ptOver V V ⟶ G) = 1 := pre_one _
  rw [← h, Over.comp_left]
  exact Category.id_comp _

end Frames

end GlobalTheory.CompanionTheory.Ar.Flat.RuleVal
end
end

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.RuleVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem ofAt_left (V : Type) [CommRing V] {G : Over (Sp V)} (f : epsOver V V ⟶ G) :
    (ofAt V ≫ f).left = f.left := Category.id_comp _

theorem toAt_left (V : Type) [CommRing V] {G : Over (Sp V)} (f : epsAt (𝟙 (Sp V)) ⟶ G) :
    (toAt V ≫ f).left = f.left := Category.id_comp _

theorem isIntFrame_of_basis (T : Formalism.L2.Pj.CDVR) (io : c.F →+* T.Fr) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr))
    {y' : Sp T.Fr ⟶ Xo.XF c} (m : SABMap t' Xo.univ.t (under y'))
    (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))) (τ' : E →+* ℂ) {N n : ℕ} (hn : N = n)
    (ub : Fin N → (epsOver T.V T.V ⟶ G.G)) (htan : ∀ i, IsTan (ub i))
    (heig : ∀ i, Formalism.L2.Pj.IsEigV c io G τ' (ub i))
    (hbas : ∀ w : epsOver T.V T.V ⟶ G.G, IsTan w → Formalism.L2.Pj.IsEigV c io G τ' w →
      ∃! a : Fin N → T.V, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsComb ub a w)
    (v : Vecs y' n)
    (hv : ∀ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ t'.G.left, u' ≫ m.φ = (v i).left ∧
      u' ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ (ub (i.cast hn.symm)).left) :
    IsIntFrame m m2 (io.comp (tauIn c τ')) v := by
  subst hn
  obtain ⟨σV, hσ⟩ := exists_lift_int T (io.comp (tauIn c τ'))
  have hσa : ∀ a, algebraMap T.V T.Fr (σV a) = io (tauIn c τ' a) := fun a => RingHom.congr_fun hσ a
  have hinj := IsFractionRing.injective T.V T.Fr
  refine ⟨σV, fun i => ofAt T.V ≫ ub i, hσ, ⟨fun i => ⟨?_, fun a => ?_⟩, fun w hw => ?_⟩, fun a => ?_⟩
  · show _ ≫ (ofAt T.V ≫ ub i).left = _
    rw [ofAt_left, one_left_at]
    exact htan i
  · rw [Category.assoc, ofAt_left, ofAt_left]
    exact heig i a (σV a) (hσa a)
  · have htan' : IsTan (toAt T.V ≫ w) := by
      show _ ≫ (toAt T.V ≫ w).left = _
      rw [toAt_left, ← one_left_at]
      exact hw.1
    have heig' : Formalism.L2.Pj.IsEigV c io G τ' (toAt T.V ≫ w) := fun a z hz => by
      have hz' : z = σV a := hinj (hz.trans (hσa a).symm)
      subst hz'
      rw [Category.assoc, toAt_left, toAt_left]
      exact hw.2 a
    obtain ⟨a, ⟨u, hu1, hu2⟩, huniq⟩ := hbas _ htan' heig'
    refine ⟨a, ⟨fun i => ofAt T.V ≫ u i, fun i => ?_, ?_⟩, fun b hb => huniq b ?_⟩
    · rw [ofAt_left, ofAt_left]
      exact hu1 i
    · rw [← pre_prod, ← hu2, ← Category.assoc, ofAt_toAt, Category.id_comp]
    · obtain ⟨u', h1, h2⟩ := hb
      refine ⟨fun i => toAt T.V ≫ u' i, fun i => ?_, ?_⟩
      · rw [toAt_left, h1, ofAt_left]
        rfl
      · rw [← pre_prod, ← h2]
  · obtain ⟨u', h1, h2⟩ := hv a
    refine ⟨u', h1, ?_⟩
    rw [ofAt_left, h2]
    rfl

theorem exists_factor (f : Formalism.L2.Pj.Rul Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : Formalism.L2.Pj.FrPt Xo c S)
    (h : Formalism.L2.Pj.FromTest (K := c.F) (fun S _ _ => Formalism.L2.Pj.FrPt Xo c S)
      (fun φ y z => Formalism.L2.Pj.FrMap φ y z) y) :
    ∃ (p : Formalism.L2.Pj.TRing c.F) (ψ : p.R →ₐ[c.F] S) (z : Formalism.L2.Pj.FrPt Xo c p.R),
      Formalism.L2.Pj.FrMap ψ z y ∧ Formalism.L2.Pj.evR Xo c f y = ψ (f p z) :=
  ⟨_, _, _, h.choose_spec.choose_spec.choose_spec, by
    unfold Formalism.L2.Pj.evR Formalism.L2.Pj.evalAt
    rw [dite_eq_left h]⟩

theorem norm_le_one_iff_log_valuation (la : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F)) (a : c.F) (ha : a ≠ 0)
    {e : ℕ} (he : 0 < e) {ρ r : ℝ} (hρ : ρ < 0) (hr : 0 < r)
    (h : Real.log r = ((e : ℤ) * Formalism.L2.Pj.vLa la a : ℤ) * ρ) :
    la.valuation c.F a ≤ 1 ↔ r ≤ 1 := by
  have h0 : la.valuation c.F a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  have c1 : la.valuation c.F a ≤ 1 ↔ 0 ≤ Formalism.L2.Pj.vLa la a := by
    rw [← WithZero.log_le_log h0 one_ne_zero, WithZero.log_one, Formalism.L2.Pj.vLa]
    omega
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hc : 0 < (e : ℝ) * (-ρ) := mul_pos he' (neg_pos.2 hρ)
  have h' : Real.log r = ((e : ℝ) * (-ρ)) * (-(Formalism.L2.Pj.vLa la a : ℝ)) := by
    rw [h]; push_cast; ring
  rw [c1]
  constructor
  · intro hL
    have hL' : (0 : ℝ) ≤ Formalism.L2.Pj.vLa la a := by exact_mod_cast hL
    have : Real.log r ≤ 0 := by rw [h']; nlinarith [mul_nonneg hc.le hL']
    by_contra hgt
    have := Real.log_pos (not_le.1 hgt)
    linarith
  · intro hr1
    have hl : Real.log r ≤ 0 := Real.log_nonpos hr.le hr1
    by_contra hL
    have hL' : (Formalism.L2.Pj.vLa la a : ℝ) < 0 := by exact_mod_cast not_le.1 hL
    have := mul_pos hc (neg_pos.2 hL')
    linarith

end GlobalTheory.CompanionTheory.Ar.Flat.RuleVal

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem GlobalTheory.CompanionTheory.Ar.Flat.nval_flat_rule : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (s : Formalism.L2.Pj.Rul Xo c) (t : ∀ p : Nat.Primes, (c.F →+* ℂ_[p]) → ℝ), τ (H.rt : E) = H.rt0 → IsLineFn U τ φ → (∀ (p : Formalism.L2.Pj.TRing c.F) (z : Formalism.L2.Pj.FrPt Xo c p.R) (F : Type) [Field F] (ψ : p.R →+* F) (y : Sp F ⟶ Xo.XF c), under y = spMap ψ ≫ z.x → y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F p.R)) → Set.range y ⊆ U → ∀ (v : Vecs y D.p) (w : Vecs y D.q) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q), (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) → (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) → ψ (s p z) = φ F y v w) → (∀ p κ, HasFinNorm U τ φ p κ (t p κ)) → ∀ (la : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F)) (T : Formalism.L2.Pj.CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : Formalism.L2.Pj.IntFr Xo c T io) (y' : Sp T.Fr ⟶ Xo.XF c), Formalism.L2.Pj.OverLa la T.V io e → y.IsAlg → under y' = (letI := io.toAlgebra; y.1.x) → y' ≫ pullback.snd _ _ = spMap io → Set.range y' ⊆ U → ∃ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ a‖ ≤ 1) ∧ ∀ π : c.F, la.valuation c.F π = WithZero.exp (-1 : ℤ) → Formalism.L2.Pj.nval T.V e (Formalism.L2.Pj.evI y s) = ((t p κ / Real.log ‖κ π‖ : ℝ) : EReal) := by
  intro E _ _ _ H D l Xo c U τ φ s t hτ hφ hs hN la T io e y y' ho halg hy hyo hyU
  letI := io.toAlgebra
  obtain ⟨p, j, hj⟩ := RuleVal.exists_embed T halg
  obtain ⟨ρ, hρ, hlog⟩ := RuleVal.exists_log_norm T j hj
  have hI : Formalism.L2.Pj.Integral T io y.1 := y.2.2
  obtain ⟨G, t', m1, m2, ⟨ub, htan, heig, hbas, hlift⟩, -⟩ := hI
  obtain ⟨m, hm⟩ := RuleVal.exists_cast hy.symm m1
  have hp : D.mult τ = D.p := if_pos hτ
  have hq : D.mult (ComplexEmbedding.conjugate τ) = D.q := RuleVal.mult_conj τ hτ
  obtain ⟨v, hv⟩ := RuleVal.exists_vecs y.1 hy τ hp
  obtain ⟨w, hw⟩ := RuleVal.exists_vecs y.1 hy (ComplexEmbedding.conjugate τ) hq
  have hfr : IsFramed U τ io y' v w :=
    ⟨hyo, hyU, RuleVal.isEigFrame_of_frPt y.1 hy τ hp v hv, RuleVal.isEigFrame_of_frPt y.1 hy _ hq w hw⟩
  have hi1 : IsIntFrame m m2 (io.comp (tauIn c τ)) v :=
    RuleVal.isIntFrame_of_basis T io G t' m m2 τ hp (ub τ) (htan τ) (heig τ) (hbas τ) v fun i => by
      obtain ⟨u', h1, h2⟩ := hlift τ (i.cast hp.symm)
      exact ⟨u', by rw [hm, h1, hv], h2⟩
  have hi2 : IsIntFrame m m2 (io.comp (tauIn c (ComplexEmbedding.conjugate τ))) w :=
    RuleVal.isIntFrame_of_basis T io G t' m m2 _ hq (ub _) (htan _) (heig _) (hbas _) w fun i => by
      obtain ⟨u', h1, h2⟩ := hlift (ComplexEmbedding.conjugate τ) (i.cast hq.symm)
      exact ⟨u', by rw [hm, h1, hw], h2⟩
  have hval : Real.log ‖j (φ T.Fr y' v w)‖ = t p (j.comp io) :=
    hN p (j.comp io) T.V T.Fr j io y' v w G t' m m2 hj rfl hfr hi1 hi2
  have hev : Formalism.L2.Pj.evI y s = φ T.Fr y' v w := by
    obtain ⟨pz, ψ, z, hm', he⟩ := RuleVal.exists_factor s y.1 y.2.1
    have hcomp : ψ.toRingHom.comp (algebraMap c.F pz.R) = io := ψ.comp_algebraMap
    refine he.trans (hs pz z T.Fr ψ.toRingHom y' (hy.trans hm'.1) (by rw [hcomp]; exact hyo) hyU v w hp hq
      (fun i => (hv i).trans (hm'.2.1 τ _)) (fun i => (hw i).trans (hm'.2.1 _ _)))
  have hne : φ T.Fr y' v w ≠ 0 := hφ.ne T.Fr io y' v w hfr
  refine ⟨p, j.comp io, fun a => ?_, fun π hπ => ?_⟩
  · by_cases ha : a = 0
    · subst ha
      simp
    have hio : io a ≠ 0 := (map_ne_zero io).2 ha
    refine RuleVal.norm_le_one_iff_log_valuation la a ha ho.1 hρ (norm_pos_iff.2 ((map_ne_zero j).2 hio)) ?_
    rw [RingHom.comp_apply, hlog _ hio, ho.2 a]
  · have hπ0 : π ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hπ
      exact WithZero.exp_ne_zero hπ.symm
    have hio : io π ≠ 0 := (map_ne_zero io).2 hπ0
    have hvL : Formalism.L2.Pj.vLa la π = 1 := by
      rw [Formalism.L2.Pj.vLa, hπ, WithZero.log_exp]
      simp
    have he' : (e : ℝ) ≠ 0 := by exact_mod_cast ho.1.ne'
    have h1 : Real.log ‖(j.comp io) π‖ = (e : ℝ) * ρ := by
      rw [RingHom.comp_apply, hlog _ hio, ho.2 π, hvL]
      simp
    rw [hev, Formalism.L2.Pj.nval_of_ne hne, ← hval, h1, hlog _ hne]
    congr 1
    field_simp [hρ.ne]
end
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.KappaIntegralBound
namespace Bl.KappaIntegralBound

private lemma kappaIntBound {K : Type} [Field K] [NumberField K] (p : Nat.Primes)
    (κ : K →+* PadicComplex p.val) (r : NumberField.RingOfIntegers K) :
    ‖κ (algebraMap (NumberField.RingOfIntegers K) K r)‖ ≤ 1 := by
  let w : Valuation K NNReal := (NormedField.valuation (K := PadicComplex p.val)).comap κ
  have hi : IsIntegral ℤ (algebraMap (NumberField.RingOfIntegers K) K r) :=
    NumberField.RingOfIntegers.isIntegral_coe r
  have hO : IsIntegral w.integer (algebraMap (NumberField.RingOfIntegers K) K r) := hi.tower_top
  have hm : algebraMap (NumberField.RingOfIntegers K) K r ∈ w.integer :=
    (Valuation.integer.integers w).mem_of_integral hO
  rw [Valuation.mem_integer_iff] at hm
  have h2 : ‖κ (algebraMap (NumberField.RingOfIntegers K) K r)‖₊ ≤ 1 := hm
  exact_mod_cast h2

theorem goal1 :
  ∀ {K : Type} [inst : Field.{0} K] [inst_1 : NumberField.{0} K] (p : Nat.Primes)
  (κ : RingHom.{0, 0} K (PadicComplex (Subtype.val.{1} p))),
  Exists.{1} fun (la : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K)) ↦
    ∀ (a : K),
      Iff (LE.le.{0} (DFunLike.coe.{1, 1, 1} (IsDedekindDomain.HeightOneSpectrum.valuation.{0, 0} K la) a) 1)
        (LE.le.{0} (Norm.norm.{0} (DFunLike.coe.{1, 1, 1} κ a)) 1) := by
  intro K _ _ p κ
  have hle : ∀ r : NumberField.RingOfIntegers K,
      ‖κ (algebraMap (NumberField.RingOfIntegers K) K r)‖ ≤ 1 := fun r => kappaIntBound p κ r
  let I : Ideal (NumberField.RingOfIntegers K) :=
    { carrier := {r | ‖κ (algebraMap (NumberField.RingOfIntegers K) K r)‖ < 1}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq, map_add (f := _)] at ha hb ⊢
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, norm_mul] at ha ⊢
        calc ‖κ (algebraMap _ K c)‖ * ‖κ (algebraMap _ K a)‖
            ≤ 1 * ‖κ (algebraMap _ K a)‖ := mul_le_mul_of_nonneg_right (hle c) (norm_nonneg _)
          _ < 1 := by rw [one_mul]; exact ha }
  have hmem : ∀ r, r ∈ I ↔ ‖κ (algebraMap (NumberField.RingOfIntegers K) K r)‖ < 1 :=
    fun r => Iff.rfl
  have hIprime : I.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one, hmem]
      simp
    · intro a b hab
      rw [hmem, map_mul, map_mul, norm_mul] at hab
      rw [hmem, hmem]
      by_contra h
      rw [not_or, not_lt, not_lt] at h
      have ha := le_antisymm (hle a) h.1
      have hb := le_antisymm (hle b) h.2
      rw [ha, hb, mul_one] at hab
      exact lt_irrefl _ hab
  have hpI : ((p.val : ℕ) : NumberField.RingOfIntegers K) ∈ I := by
    rw [hmem, map_natCast, map_natCast]
    rw [show ((p.val : ℕ) : PadicComplex p.val) = (((p.val : ℕ) : Padic p.val) : PadicComplex p.val)
      from by simp]
    rw [PadicComplex.norm_extends', Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt)
  have hne : I ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpI
    have h2 := congrArg (algebraMap (NumberField.RingOfIntegers K) K) hpI
    rw [map_natCast, map_zero, Nat.cast_eq_zero] at h2
    exact p.2.ne_zero h2
  let la : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) := ⟨I, hIprime, hne⟩
  refine ⟨la, fun a => ?_⟩
  obtain ⟨n, d, h | h⟩ := la.exists_primeCompl_mul_eq_or_mul_eq a
  · have hd : (d : NumberField.RingOfIntegers K) ∉ la.asIdeal := d.2
    have hvd := (la.valuation_eq_one_iff_notMem (K := K)).mpr hd
    have hNd : ‖κ (algebraMap _ K (d : NumberField.RingOfIntegers K))‖ = 1 :=
      le_antisymm (hle _) (not_lt.mp hd)
    have hv : la.valuation K a = la.valuation K (algebraMap _ K n) := by
      rw [← h, map_mul, hvd, mul_one]
    have hN : ‖κ a‖ = ‖κ (algebraMap _ K n)‖ := by
      rw [← h, map_mul, norm_mul, hNd, mul_one]
    rw [hv, hN]
    exact iff_of_true (la.valuation_le_one (K := K) n) (hle n)
  · have hd : (d : NumberField.RingOfIntegers K) ∉ la.asIdeal := d.2
    have hvd := (la.valuation_eq_one_iff_notMem (K := K)).mpr hd
    have hNd : ‖κ (algebraMap _ K (d : NumberField.RingOfIntegers K))‖ = 1 :=
      le_antisymm (hle _) (not_lt.mp hd)
    have hv2 : la.valuation K a * la.valuation K (algebraMap _ K n) = 1 := by
      rw [← map_mul, h, hvd]
    have hN2 : ‖κ a‖ * ‖κ (algebraMap _ K n)‖ = 1 := by
      rw [← norm_mul, ← map_mul, h, hNd]
    have key1 : la.valuation K a ≤ 1 ↔ n ∉ la.asIdeal := by
      constructor
      · intro ha
        have h1 : 1 ≤ la.valuation K (algebraMap _ K n) := hv2 ▸ mul_le_of_le_one_left' ha
        exact (la.valuation_eq_one_iff_notMem (K := K)).mp
          (le_antisymm (la.valuation_le_one (K := K) n) h1)
      · intro hn
        have h1 := (la.valuation_eq_one_iff_notMem (K := K)).mpr hn
        rw [h1, mul_one] at hv2
        exact hv2.le
    have key2 : ‖κ a‖ ≤ 1 ↔ n ∉ la.asIdeal := by
      constructor
      · intro ha hn
        have h1 : 1 ≤ ‖κ (algebraMap _ K n)‖ := by
          rw [← hN2]; exact mul_le_of_le_one_left (norm_nonneg _) ha
        exact absurd ((hmem n).mp hn) (not_lt.mpr h1)
      · intro hn
        have h1 : ‖κ (algebraMap _ K n)‖ = 1 := le_antisymm (hle n) (not_lt.mp hn)
        rw [h1, mul_one] at hN2
        exact hN2.le
    rw [key1, key2]

end Bl.KappaIntegralBound
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

namespace PositivityTheory.Xgn.PlaceValuation

theorem exists_place {K : Type} [Field K] [NumberField K] (p : Nat.Primes) (κ : K →+* ℂ_[p]) :
    ∃ la : HeightOneSpectrum (𝓞 K), ∀ a : K, la.valuation K a ≤ 1 ↔ ‖κ a‖ ≤ 1 :=
  _root_.Bl.KappaIntegralBound.goal1 p κ

theorem place_unique {K : Type} [Field K] [NumberField K] {p : Nat.Primes} {κ : K →+* ℂ_[p]}
    {la la' : HeightOneSpectrum (𝓞 K)} (h : ∀ a : K, la.valuation K a ≤ 1 ↔ ‖κ a‖ ≤ 1)
    (h' : ∀ a : K, la'.valuation K a ≤ 1 ↔ ‖κ a‖ ≤ 1) : la = la' :=
  HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := K)
    (Valuation.isEquiv_iff_val_le_one.2 fun {a} => (h a).trans (h' a).symm)

theorem log_norm_ne_zero {K : Type} [Field K] [NumberField K] {p : Nat.Primes} {κ : K →+* ℂ_[p]}
    {la : HeightOneSpectrum (𝓞 K)} (h : ∀ a : K, la.valuation K a ≤ 1 ↔ ‖κ a‖ ≤ 1) {π : K}
    (hπ : la.valuation K π = WithZero.exp (-1 : ℤ)) : Real.log ‖κ π‖ ≠ 0 := by
  have h1 : ¬ la.valuation K π⁻¹ ≤ 1 := by
    rw [map_inv₀, hπ, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  rw [h, map_inv₀, norm_inv, not_le] at h1
  have := Real.log_pos h1
  rw [Real.log_inv] at this
  linarith

end PositivityTheory.Xgn.PlaceValuation

theorem PositivityTheory.Xgn.line_function_place_valuation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Z : Formalism.L2.Pj.Comp Xo c) (τ : GlobalTheory.AllWt.Psi H) (s : Formalism.L2.Pj.Rul Xo c) (φ : FrameFn Xo c) (ρ : HeightOneSpectrum (𝓞 c.F) → ℝ), IsLineFn (Z : Set (Xo.XF c)) τ.1 φ → Reads (Z : Set (Xo.XF c)) τ.1 s φ → (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (la : HeightOneSpectrum (𝓞 c.F)) (π : c.F), (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ a‖ ≤ 1) → la.valuation c.F π = WithZero.exp (-1 : ℤ) → HasFinNorm (Z : Set (Xo.XF c)) τ.1 φ p κ (ρ la * Real.log ‖κ π‖)) → ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, v s = (ρ la : EReal) := by
  intro E _ _ _ H D l Xo c _ Z τ s φ ρ hφ hs hN la v hv
  choose pl hpl using fun (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) => PositivityTheory.Xgn.PlaceValuation.exists_place p κ
  choose un hun using fun la : HeightOneSpectrum (𝓞 c.F) => la.valuation_exists_uniformizer c.F
  obtain ⟨⟨_, T, io, e, ho, y, hy, eta, -, rfl⟩, rfl⟩ := hv
  letI := io.toAlgebra
  obtain ⟨p, κ, hκ, hval⟩ := GlobalTheory.CompanionTheory.Ar.Flat.nval_flat_rule E H D l Xo c (Z : Set (Xo.XF c)) τ.1 φ s
    (fun p κ => ρ (pl p κ) * Real.log ‖κ (un (pl p κ))‖) τ.2 hφ hs
    (fun p κ => hN p κ (pl p κ) _ (hpl p κ) (hun _)) la T io e y (GlobalTheory.AllWt.ptF y.1) ho hy.1
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (by rintro _ ⟨x, rfl⟩; exact hy.2 x)
  have hla : pl p κ = la := PositivityTheory.Xgn.PlaceValuation.place_unique (hpl p κ) hκ
  refine (hval (un la) (hun la)).trans ?_
  rw [hla, mul_div_assoc, div_self (PositivityTheory.Xgn.PlaceValuation.log_norm_ne_zero hκ (hun la)), _root_.mul_one]
