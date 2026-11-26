module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptGoodReductionDegree
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptLabelBases

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.Imports
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HcptPull

noncomputable section

namespace LevelTowerAlt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
  {Ω Ω' : Type} [Field Ω] [Field Ω'] {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type}
  [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] {y : (Σ k, J k) → Ω} {y' : (Σ k, J' k) → Ω'}


omit [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] in
theorem emb_eq (A : HodgeCpt Y S y) (B : HodgeCpt Y S y') (h : B.X ⟶ A.X) (i : Ω →+* Ω')
    (hdom : GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i) (hf : B.f = h ≫ A.f) :
    B.emb = fun s => (i.comp A.cst).comp (labelEmb c s) := by
  have e1 : spMap (B.cst.comp (algebraMap (𝓞 c.F) c.F)) = spMap ((i.comp A.cst).comp (algebraMap (𝓞 c.F) c.F)) := by
    have e : B.ξ ≫ h = spMap i ≫ A.ξ := hdom
    rw [← B.cst_over, hf, Category.assoc, ← Category.assoc, e, Category.assoc, A.cst_over]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have e2 : B.cst.comp (algebraMap (𝓞 c.F) c.F) = (i.comp A.cst).comp (algebraMap (𝓞 c.F) c.F) :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective e1)
  funext s
  refine RingHom.ext fun a => ?_
  exact RingHom.congr_fun e2
    ⟨labelEmb c s a, (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (labelEmb c s).toIntAlgHom⟩


set_option maxHeartbeats 1000000 in
theorem exists_pull (A : HodgeCpt Y S y) (B : HodgeCpt Y S y') (h : B.X ⟶ A.X) (i : Ω →+* Ω') (x : Sp Ω ⟶ Xo.XF c)
    (hx : A.ξ ≫ A.f = x ≫ Y.j) (hS : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S)
    (hvb : ∀ p ∈ S, ∀ s, ((A.M.htOm A.t.PP.L (p ^ A.R p)).map (A.Vgen s).dualRestrict).IsVBOn {q | InFibre A.ξ p q}
      (labelRk D s) ⊤)
    (hdom : GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i) (hf : B.f = h ≫ A.f) (hR : B.R = A.R) :
    ∃ j : A.Li →+ B.Li, IsExtOver i j ∧ ∀ s, B.V s = (A.V s).pull B.ξ h j := by
  haveI : CharZero Ω := charZero_of_injective_ringHom A.cst.injective
  haveI : CharZero Ω' := charZero_of_injective_ringHom i.injective
  have hgen := A.tie.gen
  have hgen' := B.tie.gen
  obtain ⟨mh, -⟩ := GlobalTheory.CompanionTheory.Ar.CoverLie.cancel hf A.m B.m
  obtain ⟨j, hj⟩ := GlobalTheory.CompanionTheory.Ar.CoverLie.exists_hom hdom mh.cart A.M B.M
  have hsm : Smooth A.t.G.hom := A.t.semi.smooth
  obtain ⟨hext, hspan, hlat⟩ := GlobalTheory.T.lie_lattice_dominant_compat A.X B.X Ω Ω' A.ξ B.ξ h i A.t.G B.t.G mh.φ A.Li B.Li A.M B.M j hgen hgen' hdom
    mh.cart hsm hj
  have hρj : ∀ a e, j (A.ρ a e) = B.ρ a (j e) := fun a e =>
    GlobalTheory.CompanionTheory.Ar.CoverLie.map_diff mh.cart (mh.act a) hj (A.act a) (B.act a) e
  obtain ⟨jd, hjd⟩ := GlobalTheory.T.dual_map_of_field_extension Ω Ω' i A.Li B.Li j hext hspan
  have hW : ∀ s, eigSp B.ρ ((i.comp A.cst).comp (labelEmb c s)) = Submodule.span Ω' (j '' (A.Vgen s : Set A.Li)) := fun s =>
    GlobalTheory.T.eigenspace_field_extension E Ω Ω' i A.Li B.Li j A.ρ B.ρ (A.emb s) hext hspan (fun a e => (hρj a e).symm)
  have hdm := GlobalTheory.CompanionTheory.Ar.RegAtDom.regAt_dominates A.X Ω A.ξ B.X Ω' B.ξ h i hdom
  have hsp : ∀ p' : Cpt B.ξ, genPt A.ξ ⤳ h p'.1 := fun p' => (hdm p').choose
  have hreg : ∀ (p' : Cpt B.ξ), ∀ a ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩, i a ∈ regAt B.ξ p' := fun p' => (hdm p').choose_spec.1
  have hun : ∀ (p' : Cpt B.ξ), ∀ a ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩, unitAt B.ξ p' (i a) → unitAt A.ξ ⟨h p'.1, hsp p'⟩ a :=
    fun p' => (hdm p').choose_spec.2 hgen'
  have hfib : ∀ (p : ℕ) (p' : Cpt B.ξ), InFibre B.ξ p p' ↔ InFibre A.ξ p ⟨h p'.1, hsp p'⟩ := by
    intro p p'
    refine not_congr ⟨fun hu => ?_, fun ⟨a, b, d⟩ => ?_⟩
    · have hr : (p : Ω) ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩ := natCast_mem _ p
      exact hun p' _ hr (by simpa using hu)
    · refine ⟨?_, ?_, ?_⟩
      · intro e; apply a; apply i.injective; simpa using e
      · simpa using hreg p' _ b
      · simpa using hreg p' _ d
  have hnoeth := (GlobalTheory.T.regAt_noetherian_model_noetherian A.X Ω A.ξ ℤ _ _ A.tie).1
  have hnoeth' := (GlobalTheory.T.regAt_noetherian_model_noetherian B.X Ω' B.ξ ℤ _ _ B.tie).1
  have hic : ∀ q : Cpt A.ξ, IsIntegrallyClosed (A.X.presheaf.stalk q.1) := fun q => A.normal.2 q.1
  have hic' : ∀ q : Cpt B.ξ, IsIntegrallyClosed (B.X.presheaf.stalk q.1) := fun q => B.normal.2 q.1
  have htors : ∀ p ∈ S, FullTorsion B.t.G B.ξ (p ^ A.R p) := fun p hp =>
    GlobalTheory.T.full_torsion_pullback A.X B.X Ω Ω' A.ξ B.ξ h i A.t.G B.t.G mh.φ _ hdom mh.cart (A.tors p hp)
  have hint : ∀ (s) (q : Cpt A.ξ) (a : 𝓞 E), A.emb s a ∈ regAt A.ξ q := fun s q a =>
    GlobalTheory.T.integral_element_regular A.X Ω A.ξ q hgen (hic q) _ ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map (A.emb s).toIntAlgHom)

  have hω : ∀ p ∈ S, ∀ p' : Cpt B.ξ, 0 < D.p + D.q → B.M.htOm B.t.PP.L (p ^ A.R p) p' =
      Submodule.span (regAt B.ξ p') (jd '' (A.M.htOm A.t.PP.L (p ^ A.R p) ⟨h p'.1, hsp p'⟩ : Set _)) := by
    intro p hp p' hpos
    have hN : 0 < p ^ A.R p := pow_pos (A.S_prime p hp).pos _
    obtain ⟨s0, o, ⟨m0⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c _ _ Y A.X A.f A.t A.m Ω A.ξ x hx
    obtain ⟨s0', o', ⟨m0'⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c _ _ Y B.X B.f B.t B.m Ω' B.ξ (spMap i ≫ x) (by
      rw [hf, ← Category.assoc, hdom, Category.assoc, hx, Category.assoc])
    have hc1 : IsIntegrallyClosed (A.X.presheaf.stalk (h p'.1)) := hic ⟨h p'.1, hsp p'⟩
    have hn1 : IsNoetherianRing (A.X.presheaf.stalk (h p'.1)) := noeth_stalk hgen ⟨h p'.1, hsp p'⟩ (hnoeth _)
    have h1 := GlobalTheory.T.full_torsion_integrally_closed E H D l (KA l) (baseKA l) A.X Ω A.ξ s0 o A.t m0 A.Li A.M (p ^ A.R p) ⟨h p'.1, hsp p'⟩ hgen hN
      (A.tors p hp) hc1 hn1
    have h1' := GlobalTheory.T.full_torsion_integrally_closed E H D l (KA l) (baseKA l) B.X Ω' B.ξ s0' o' B.t m0' B.Li B.M (p ^ A.R p) p' hgen' hN
      (htors p hp) (hic' _) (noeth_stalk hgen' _ (hnoeth' _))
    have h2 := GlobalTheory.T.omega_lattice_dominant_compat A.X B.X Ω Ω' A.ξ B.ξ h i A.t.G B.t.G mh.φ A.Li B.Li A.M B.M j hgen hgen' hdom mh.cart hsm hj jd hjd
      (p ^ A.R p) hN p' (hsp p') hc1 hn1 (h1.2.1 hpos) h1.1
    rw [h1'.2.2, h2, pull_eq B.ξ h _ jd p' (hsp p'), h1.2.2]
  have hpos : ∀ s, 0 < labelRk D s → 0 < D.p + D.q := by
    intro s hs
    rcases s with τ | τ
    · have : 0 < D.p := hs
      omega
    · have : 0 < D.q := hs
      omega
  have hdual : ∀ p ∈ S, ∀ s, ∀ p' : Cpt B.ξ, InFibre B.ξ p p' →
      B.M.htDual B.t.PP.L (p ^ A.R p) B.ρ ((i.comp A.cst).comp (labelEmb c s)) p' =
        Submodule.span (regAt B.ξ p') (j '' (A.M.htDual A.t.PP.L (p ^ A.R p) A.ρ (A.emb s) ⟨h p'.1, hsp p'⟩ : Set A.Li)) := by
    intro p hp s p' hf
    have hq := (hfib p p').1 hf
    obtain ⟨U, hU, b, hb, hfr⟩ := hvb p hp s ⟨h p'.1, hsp p'⟩ hq
    obtain ⟨hli, hbs⟩ := hfr ⟨h p'.1, hsp p'⟩ hq hU
    exact GlobalTheory.T.dual_lattice_basis_extension Ω Ω' i (regAt A.ξ ⟨h p'.1, hsp p'⟩) (regAt B.ξ p') A.Li B.Li j jd (A.Vgen s) _
      (A.M.htOm A.t.PP.L (p ^ A.R p) ⟨h p'.1, hsp p'⟩) (B.M.htOm B.t.PP.L (p ^ A.R p) p') (labelRk D s) b hext (hreg p') hjd
      (hW s) (fun hr => hω p hp p' (hpos s hr)) hli hb hbs
  have hhtw : ∀ p ∈ S, ∀ s, ∀ p' : Cpt B.ξ, InFibre B.ξ p p' →
      B.M.htW B.t.PP.L (p ^ A.R p) B.ρ ((i.comp A.cst).comp (labelEmb c s)) (differentIdeal ℤ (𝓞 E)) p' =
        Submodule.span (regAt B.ξ p')
          (j '' (A.M.htW A.t.PP.L (p ^ A.R p) A.ρ (A.emb s) (differentIdeal ℤ (𝓞 E)) ⟨h p'.1, hsp p'⟩ : Set A.Li)) := by
    intro p hp s p' hf
    haveI := regAt_isLocalRing (ξ := A.ξ) ⟨h p'.1, hsp p'⟩
    obtain ⟨d₀, hd₀, hne, hdv⟩ := GlobalTheory.T.different_ideal_local_generator E Ω (regAt A.ξ ⟨h p'.1, hsp p'⟩) (A.emb s) (hint s _)
    exact GlobalTheory.T.different_scaled_lattice_extension Ω Ω' i (regAt A.ξ ⟨h p'.1, hsp p'⟩) (regAt B.ξ p') A.Li B.Li j (A.Vgen s) _ (𝓞 E) (A.emb s)
      (differentIdeal ℤ (𝓞 E)) d₀ (A.M.htDual A.t.PP.L (p ^ A.R p) A.ρ (A.emb s) ⟨h p'.1, hsp p'⟩)
      (B.M.htDual B.t.PP.L (p ^ A.R p) B.ρ ((i.comp A.cst).comp (labelEmb c s)) p') hext (hreg p') (hW s) hd₀ hne hdv
      (fun e he => LieModel.mem_eigSp_of_mem_htDual _ _ _ _ _ he) (hdual p hp s p' hf)
  have hV : ∀ s, Lat.patch S (B.M.eigLat B.ρ ((i.comp A.cst).comp (labelEmb c s)))
      (fun p => htLabel B.M B.t.PP.L (p ^ A.R p) B.ρ (fun s' => (i.comp A.cst).comp (labelEmb c s')) s) =
      (A.V s).pull B.ξ h j := by
    intro s
    funext p'
    rw [pull_eq B.ξ h _ j p' (hsp p')]
    by_cases hc : ∃ p ∈ S, InFibre B.ξ p p'
    · obtain ⟨p, hp, hf⟩ := hc
      rw [Lat.patch_of_unique S _ _ hp hf fun p2 hp2 h2 =>
        inFibre_unique (A.S_prime p hp) (A.S_prime p2 hp2) hf h2]
      have e1 : A.V s ⟨h p'.1, hsp p'⟩ = A.HT p s ⟨h p'.1, hsp p'⟩ :=
        Lat.patch_of_unique S _ _ hp ((hfib p p').1 hf) fun p2 hp2 h2 =>
          inFibre_unique (A.S_prime p hp) (A.S_prime p2 hp2) ((hfib p p').1 hf) h2
      rw [e1]
      rcases s with τ | τ
      · exact hhtw p hp _ p' hf
      · exact hdual p hp _ p' hf
    · have hc' : ∀ p ∈ S, ¬ InFibre B.ξ p p' := fun p hp hf => hc ⟨p, hp, hf⟩
      rw [Lat.patch_of_not S _ _ hc']
      have hc'' : ∀ p ∈ S, ¬ InFibre A.ξ p ⟨h p'.1, hsp p'⟩ := fun p hp hf => hc' p hp ((hfib p p').2 hf)
      have e1 : A.V s ⟨h p'.1, hsp p'⟩ = A.dR s ⟨h p'.1, hsp p'⟩ := Lat.patch_of_not S _ _ hc''
      rw [e1]
      have hdisc : (((NumberField.discr E : ℤ) : Ω))⁻¹ ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩ := by
        have hn0 : (NumberField.discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E)
        obtain ⟨-, -, hu⟩ := unitAt_natCast (ξ := A.ξ) ⟨h p'.1, hsp p'⟩ _ hn0 fun p hpp hd => by
          have hin := hS p hpp (Int.natCast_dvd.2 hd)
          exact not_not.1 (hc'' p hin)
        rcases Int.natAbs_eq (NumberField.discr E) with e | e
        · rw [e]; simpa using hu
        · rw [e]
          simpa using (regAt A.ξ ⟨h p'.1, hsp p'⟩).neg_mem hu
      show B.M.lat p' ⊓ _ = _
      rw [hlat, pull_eq B.ξ h _ j p' (hsp p')]
      exact GlobalTheory.T.lattice_eigen_field_extension E Ω Ω' i A.Li B.Li j A.ρ B.ρ (A.emb s) _ _ (A.M.lat ⟨h p'.1, hsp p'⟩) hext (fun a e => (hρj a e).symm) (hreg p')
        (fun a e he => GlobalTheory.T.lie_lattice_stable_under_action A.X Ω A.ξ A.t.G A.Li A.M (𝓞 E) A.t.act A.ρ A.act _ a e he) (hint s _) hdisc
  refine ⟨j, hext, fun s => Eq.trans ?_ (hV s)⟩
  have he := emb_eq A B h i hdom hf
  show Lat.patch S (B.M.eigLat B.ρ (B.emb s)) (fun p => htLabel B.M B.t.PP.L (p ^ B.R p) B.ρ B.emb s) = _
  rw [he, hR]

end LevelTowerAlt
end
end

section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsJoin
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace LevelTowerAlt

theorem exists_join {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω' ⟶ X'}
    {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type}
    [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] {y : (Σ k, J k) → Ω} {y' : (Σ k, J' k) → Ω'}
    (hT : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)
    (hT' : CoordTie ℤ ξ' fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) (g : X' ⟶ X) (i : Ω →+* Ω')
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ g i) :
    ∃ (K₃ : Type) (_ : Fintype K₃) (J₃ : K₃ → Type) (_ : ∀ k, Fintype (J₃ k)) (y₃ : (Σ k, J₃ k) → Ω') (bk : K → K₃)
      (bx : ∀ k, J k ≃ J₃ (bk k)), Nonempty K₃ ∧ Function.Injective bk ∧ (∀ k x, y₃ ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) ∧
      CoordTie ℤ ξ' fun c' : (k : K₃) → J₃ k => ∏ k, y₃ ⟨k, c' k⟩ := by
  let J₁ : K ⊕ Unit → Type := Sum.elim J fun _ => Unit
  letI : ∀ k, Fintype (J₁ k) := fun k => match k with
    | .inl k => (inferInstance : Fintype (J k))
    | .inr _ => (inferInstance : Fintype Unit)
  let s : (Σ k, J₁ k) → Ω' := fun q => match q with
    | ⟨.inl k, a⟩ => i (y ⟨k, a⟩)
    | ⟨.inr _, _⟩ => 1
  have h1 := GlobalTheory.T.coords_join_blocks X' Ω' ξ' K' J' y' (K ⊕ Unit) J₁ s hT' (by
    rintro (k | k) p
    · obtain ⟨hsp, hreg, -⟩ := GlobalTheory.CompanionTheory.Ar.RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' g i hd p
      obtain ⟨c, hc⟩ := hT.cover ⟨g p.1, hsp⟩
      refine ⟨c k, (map_ne_zero i).2 (TiePrimes.ne_of_seg hc.1 k), fun a => ?_⟩
      have := hreg _ (TiePrimes.ratio_mem hc ⟨k, a⟩)
      rw [map_div₀] at this
      exact this
    · refine ⟨(), one_ne_zero, fun a => ?_⟩
      show (1 : Ω') / 1 ∈ _
      rw [div_one]; exact one_mem _)
  let J₃ : K' ⊕ (K ⊕ Unit) → Type := Sum.elim J' J₁
  let y₃ : (Σ k, J₃ k) → Ω' := fun q => match q with
    | ⟨.inl k, a⟩ => y' ⟨k, a⟩
    | ⟨.inr k, a⟩ => s ⟨k, a⟩
  refine ⟨K' ⊕ (K ⊕ Unit), inferInstance, J₃, fun k => match k with
    | .inl k => (inferInstance : Fintype (J' k))
    | .inr k => (inferInstance : Fintype (J₁ k)), y₃, fun k => .inr (.inl k), fun k => Equiv.refl _,
    ⟨.inr (.inr ())⟩, fun a b h => by simpa using h, fun _ _ => rfl, ?_⟩
  have e : (fun c' : (k : K' ⊕ (K ⊕ Unit)) → J₃ k => ∏ k, y₃ ⟨k, c' k⟩) =
      fun c' : (k : K' ⊕ (K ⊕ Unit)) → Sum.elim J' J₁ k =>
        (∏ k, y' ⟨k, c' (Sum.inl k)⟩) * ∏ k, s ⟨k, c' (Sum.inr k)⟩ :=
    funext fun c' => Fintype.prod_sum_type _
  rw [e]; exact h1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type}
  {y : (Σ k, J k) → Ω} {y' : (Σ k, J' k) → Ω}

@[reducible] def reTie (B : HodgeCpt Y S y) (h : CoordTie ℤ B.ξ fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) :
    HodgeCpt Y S y' := { B with tie := h }

theorem flag_zero [∀ k, Fintype (J k)] (B : HodgeCpt Y S y) (d : ℕ) (hc : B.IsCover d) (h0 : D.p + D.q = 0) :
    Nonempty B.Flag := by
  have hrk : ∀ s, labelRk D s = 0 := by
    rintro (τ | τ)
    · show D.p = 0; omega
    · show D.q = 0; omega
  haveI : ∀ s, IsEmpty (Fin (labelRk D s)) := fun s => by rw [hrk s]; infer_instance
  have hV : ∀ s, B.Vgen s = ⊥ := fun s => by
    obtain ⟨U, -, b, hb, -⟩ := B.vb s ⟨_, specializes_rfl⟩ trivial
    refine hb.symm.trans ?_
    rw [Set.range_eq_empty, Submodule.span_empty]
  obtain ⟨Li₀, _, _, ⟨M₀⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists Y.X Y.t.G B.Ω₀ B.ξ₀
  obtain ⟨j, hj⟩ := GlobalTheory.T.lie_model_pullback_map Y.X B.X B.Ω₀ Ω B.ξ₀ B.ξ B.f B.fn Y.t.G B.t.G B.m.φ Li₀ B.Li M₀ B.M B.fn_over B.m.cart
  obtain ⟨hext, -, -⟩ := GlobalTheory.T.lie_lattice_dominant_compat Y.X B.X B.Ω₀ Ω B.ξ₀ B.ξ B.f B.fn Y.t.G B.t.G B.m.φ Li₀ B.Li M₀ B.M j B.gen₀
    B.tie.gen B.fn_over B.m.cart Y.t.semi.smooth hj
  refine ⟨{ b := fun _ => isEmptyElim, sub := fun s p _ => ?_, Li₀ := Li₀, M₀ := M₀, j := j, j_pt := hj,
            V₀ := fun _ => ⊥, V₀_mem := fun s e => ?_, deg := d, generic := ?_ }⟩
  · obtain ⟨U, hU, b, -, hb⟩ := B.vb s p trivial
    exact ⟨U, hU, b, fun _ => by rw [Subsingleton.elim b isEmptyElim], hb⟩
  · rw [hV, Submodule.mem_bot, Submodule.mem_bot]
    refine ⟨fun h => by rw [h, map_zero], fun h => by_contra fun hne => ?_⟩
    have := hext.2 1 (fun _ => e) (linearIndependent_unique_iff.2 hne)
    exact this.ne_zero 0 h
  · letI := B.fn.toAlgebra
    refine ⟨fun _ => isEmptyElim, fun _ => 0, fun s => ⟨linearIndependent_empty_type, ?_⟩, hext.1,
      fun _ => linearIndependent_empty_type, fun _ => linearIndependent_empty_type, fun _ => isEmptyElim,
      fun _ => isEmptyElim, fun s i => congrArg (fun b => flagStep Ω b i) (Subsingleton.elim _ _), ?_, hc.1, ?_⟩
    · rw [Set.range_eq_empty, Submodule.span_empty]
    · haveI : IsEmpty (Σ σ : CMType H ⊕ CMType H,
          {lk : Fin (labelRk D σ) × Fin (labelRk D σ) // lk.2 < lk.1}) := ⟨fun q => isEmptyElim q.2.1.1⟩
      exact algebraicIndependent_empty_type
    · haveI : IsEmpty (Σ σ : CMType H ⊕ CMType H, Fin (labelRk D σ) × Fin (labelRk D σ)) :=
        ⟨fun q => isEmptyElim q.2.1⟩
      rw [Set.range_eq_empty, IntermediateField.adjoin_empty, IntermediateField.finrank_bot']
      exact hc.2

end LevelTowerAlt
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace LevelTowerAlt

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
  {Ω : Type} [Field Ω] [CharZero Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem exists_root (A : HodgeCpt Y S y) (x : Sp Ω ⟶ Xo.XF c) (hx : A.ξ ≫ A.f = x ≫ Y.j) (hpos : 0 < D.p + D.q)
    (p : ℕ) (hp : p ∈ S) : ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ A.R p) := by
  obtain ⟨s0, o, ⟨m0⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c _ _ Y A.X A.f A.t A.m Ω A.ξ x hx
  let q : Cpt A.ξ := ⟨_, specializes_rfl⟩
  exact (GlobalTheory.T.full_torsion_integrally_closed E H D l (KA l) (baseKA l) A.X Ω A.ξ s0 o A.t m0 A.Li A.M (p ^ A.R p) q A.tie.gen
    (pow_pos (A.S_prime p hp).pos _) (A.tors p hp) (A.normal.2 q.1)
    (HcptPull.noeth_stalk A.tie.gen q ((GlobalTheory.T.regAt_noetherian_model_noetherian A.X Ω A.ξ ℤ _ _ A.tie).1 q))).2.1 hpos

theorem exists_flagged (hW : Out.WeilSt) (A : HodgeCpt Y S y) (x : Sp Ω ⟶ Xo.XF c) (hx : A.ξ ≫ A.f = x ≫ Y.j) (dg : ℕ)
    (hcov : A.IsCover dg) (hS : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) (hHT : ∀ p ∈ S, HT.HTFree A p) :
    ∃ (Ω' : Type) (_ : Field Ω') (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k))
      (y' : (Σ k, J' k) → Ω') (B : HodgeCpt Y S y') (Fl : B.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K' → ℤ)
      (e : CMType H × Fin (D.p + D.q) → Ω') (i : Ω →+* Ω') (g : B.X ⟶ A.X) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)),
      Nonempty K' ∧ Function.Injective bk ∧ (∀ k a, y' ⟨bk k, bx k a⟩ = i (y ⟨k, a⟩)) ∧
      GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ g i ∧ B.f = g ≫ A.f ∧ B.R = A.R ∧ (∀ p ∈ S, HT.HTFree B p) ∧
      Fl.RootLines xdeg e := by
  rcases Nat.eq_zero_or_pos (D.p + D.q) with h0 | hpos
  · have hd : GlobalTheory.CompanionTheory.Ar.Dominates A.ξ A.ξ (𝟙 _) (RingHom.id Ω) := by
      unfold GlobalTheory.CompanionTheory.Ar.Dominates
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, Category.comp_id]
    obtain ⟨K₃, _, J₃, _, y₃, bk, bx, hne, hinj, hy, hT⟩ := exists_join A.tie A.tie (𝟙 _) (RingHom.id Ω) hd
    obtain ⟨Fl⟩ := flag_zero (reTie A hT) dg hcov h0
    haveI : IsEmpty (CMType H × Fin (D.p + D.q)) := ⟨fun r => by have := r.2.2; omega⟩
    exact ⟨Ω, _, K₃, _, J₃, inferInstance, y₃, reTie A hT, Fl, fun _ => 0, fun _ => 1, RingHom.id Ω, 𝟙 _, bk, bx, hne, hinj, hy, hd,
      (Category.id_comp _).symm, rfl, hHT, isEmptyElim⟩
  · have hζ := exists_root A x hx hpos
    obtain ⟨Ω', _, _, i, K₂, _, J₂, _, y₂, B, g₂, b, Li₀, a₀, m₀, M₀, j, V₀, hg₂, hBf, hBR, hB, hb, hj, hV, hgen⟩ :=
      GlobalTheory.T.hodge_cpt_good_reduction_degree hW E H D l Xo c Y S Ω K J y A x dg hx hS hHT hζ hcov
    have hBy : B.ξ ≫ B.f = (spMap i ≫ x) ≫ Y.j := by
      rw [hBf, ← Category.assoc, hg₂, Category.assoc, hx, Category.assoc]
    obtain ⟨K₃, _, J₃, _, y₃, bk, bx, ⟨k₀⟩, hinj, hy, hT⟩ := exists_join A.tie B.tie g₂ i hg₂
    obtain ⟨K₄, _, J₄, _, y₄, bk', bx', C, g₃, Fl, xdeg, e, hinj', hy', hg₃, hCf, hCR, -, hC, -, -, hroot, -⟩ :=
      GlobalTheory.T.hodge_cpt_label_bases hW E H D l Xo c Y S Ω' K₃ J₃ y₃ (reTie B hT) (spMap i ≫ x) b Li₀ a₀ m₀ M₀ j V₀ dg hBy hS hB
        (fun p hp => by
          obtain ⟨ζ, hζ'⟩ := hζ p hp
          exact ⟨i ζ, by rw [show (reTie B hT).R = A.R from hBR]; exact hζ'.map_of_injective i.injective⟩) hb hj hV hgen
    refine ⟨Ω', _, K₄, _, J₄, inferInstance, y₄, C, Fl, xdeg, e, i, g₃ ≫ g₂, bk' ∘ bk, fun k => (bx k).trans (bx' (bk k)),
      ⟨bk' k₀⟩, hinj'.comp hinj, fun k a => (hy' _ _).trans (hy k a), ?_, ?_, hCR.trans hBR, hC, hroot⟩
    · have h3 : C.ξ ≫ g₃ = B.ξ := by
        have h := hg₃
        unfold GlobalTheory.CompanionTheory.Ar.Dominates at h
        rw [h, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
      show C.ξ ≫ g₃ ≫ g₂ = _
      rw [← Category.assoc, h3]
      exact hg₂
    · rw [Category.assoc, ← hBf]; exact hCf

end

theorem hodge_compact_cover_primes : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (dg : ℕ) [Fintype (CMType H)], 𝔐.IsCover dg → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) → (∀ p ∈ S, HT.HTFree 𝔐 p) → ∃ (M : Top.RootModel (CMType H) (D.p + D.q)) (𝔐' : HodgeCpt Y S M.y) (Fl : 𝔐'.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω) (i : Ω →+* M.Ω) (g : 𝔐'.X ⟶ 𝔐.X) (bk : K → M.K) (bx : ∀ k, J k ≃ M.ι (bk k)) (j : 𝔐.Li →+ 𝔐'.Li), Function.Injective bk ∧ (∀ k x, M.y ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates 𝔐'.ξ 𝔐.ξ g i ∧ (∀ p ∈ S, HT.HTFree 𝔐' p) ∧ Fl.RootLines M.xdeg e ∧ (∀ (a : Ω) v, j (a • v) = i a • j v) ∧ (∀ (n : ℕ) (v : Fin n → 𝔐.Li), LinearIndependent Ω v → LinearIndependent M.Ω fun k => j (v k)) ∧ ∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ g j := by
  intro hW E _ _ _ H D Xo l c Y S Ω _ _ K _ J _ y A dg inst hcov hS hHT
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨-, ⟨x, hx⟩, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l (Xo l) c _ _ Y S Ω K J y A hβ
  obtain ⟨Ω', _, K', _, J', _, y', B, Fl, xdeg, e, i, g, bk, bx, hne, hinj, hy, hd, hf, hR, hB, hroot⟩ :=
    exists_flagged hW A x hx dg hcov hS hHT
  obtain ⟨j, hext, hV⟩ := exists_pull A B g i x hx hS (fun p hp => (hHT p hp).2) hd hf hR
  obtain ⟨hbir, har⟩ := GlobalTheory.T.hodge_cpt_birational_arith_var E H D l (Xo l) c _ _ Y S Ω' K' J' y' B Fl hβ
  have har' : IsArithVar (mCoordIdeal y') (@Fintype.card (CMType H) inst * ((D.p + D.q) * (D.p + D.q - 1) / 2) + 1) := by
    convert har
  choose L hL using GlobalTheory.T.exists_smooth_conj_invariant_metric K' J'
  exact ⟨{ K := K', «ι» := J', Ω := Ω', y := y', arith := har', birational := hbir, xdeg := xdeg,
           x := fun _ r => L (xdeg r), x_deg := fun _ _ => (hL _).1, x_smooth := fun _ _ => (hL _).2.1,
           x_conj := fun _ _ => (hL _).2.2, kA := 1, kA_pos := one_pos, A := L 0, A_smooth := (hL _).2.1,
           A_conj := (hL _).2.2, δ := 1, δ_pos := one_pos },
    B, Fl, e, i, g, bk, bx, j, hinj, hy, hd, hB, hroot, hext.1, hext.2, hV⟩

end LevelTowerAlt
