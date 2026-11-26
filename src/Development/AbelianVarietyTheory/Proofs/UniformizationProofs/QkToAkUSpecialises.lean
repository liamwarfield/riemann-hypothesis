module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFinAffineCover
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralFamiliesSpanPullDegeneration

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralFamiliesSpanGenerateValuationRings
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralFamiliesSpanGenerateValuationRings
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FamGen

open GlobalTheory.FamSpan GlobalTheory.FieldBaseChange

theorem constVal_mul {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (a b : R) :
    constVal q z (a * b) = constVal q z a * constVal q z b := by
  rw [constVal, map_mul, gs_mul q z ⊤ trivial]; rfl

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem comb_term {S : Type} [CommRing S] (σ : R →+* S) (ιF : S →+* F)
    (ρ : TF (R := R) F ⟶ Over.mk (specOf σ)) (hρ : ρ.left = specOf ιF) (k : ℕ) (α : D.X) {m : ℕ}
    (b g : Fin m → D.SecB k α)
    (hb : IsSecBasis (T := Over.mk (specOf σ)) (A := D.P.A) _ (fun i => DVR.pullSec D.P.L (D.famφB α) (DegPre.famε k)
      (b i) (snd (Over.mk (specOf σ)) D.P.A).left))
    (r : Fin m → R) (hr : ∀ i, IsUnit (σ (r i)))
    (hg : ∀ i j, (g i).f j = resTop _ (scal D.P.A.hom (r i)) * (b i).f j)
    (G : Fin m → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)))
    (hG : ∀ i, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (G i) (D.famφB α)
      (DegPre.famε k) (g i) (DegPre.prB D F).left 1)
    (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)))
    (sg : LB.Sec (LB.LinComb D.P.L (fun i => (snd (Over.mk (specOf σ)) D.P.A).left ≫ D.famφB α i) (DegPre.famε k)))
    (hsg : GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) s
      (fun i => (snd (Over.mk (specOf σ)) D.P.A).left ≫ D.famφB α i) (DegPre.famε k) sg (ρ ▷ D.P.A).left 1) :
    ∃ c : Fin m → S, ∀ j, s.f j = ∑ i, resTop _ (DVR.gF D F (ιF (c i))) * (G i).f j := by
  obtain ⟨c, hc, -⟩ := hb sg
  choose u hu using fun i => (hr i).exists_left_inv
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (c i) * u i,
    IntegralCoord.lin_of_sval D.P.isLB _ G fun y J hJ => ?_⟩
  have a₁ : (𝟙 _ ≫ (ρ ▷ D.P.A).left) ≫ (snd (Over.mk (specOf σ)) D.P.A).left = 𝟙 _ ≫ (DegPre.prB D F).left := by
    rw [Category.assoc, ← Over.comp_left, whiskerRight_snd]
  have a₂ : (𝟙 _ ≫ (ρ ▷ D.P.A).left) ≫ (fst (Over.mk (specOf σ)) D.P.A).left =
      (𝟙 _ ≫ (fst (TF (R := R) F) D.P.A).left) ≫ specOf ιF := by
    rw [Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, hρ, Category.assoc]
  have a₃ : (𝟙 _ ≫ (DegPre.prB D F).left) ≫ D.P.A.hom =
      ((𝟙 _ ≫ (fst (TF (R := R) F) D.P.A).left) ≫ specOf ιF) ≫ specOf σ := by
    rw [← a₂, ← a₁]
    simp only [Category.assoc]
    rw [Over.w (snd (Over.mk (specOf σ)) D.P.A)]
    exact congrArg _ (congrArg _ (Over.w (fst (Over.mk (specOf σ)) D.P.A)).symm)
  rw [← secScal_sval hsg _ y hJ]
  refine (sval_lin (fun i => scal (fst (Over.mk (specOf σ)) D.P.A).left
    ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (c i))) _ (fun j => (hc j).trans (Finset.sum_congr rfl fun i _ =>
      congrArg₂ (· * ·) (congrArg _ (congrArg _ (Iso.hom_inv_id_apply _ _).symm)) rfl)) _ y hJ).trans
    (Finset.sum_congr rfl fun i _ => ?_)
  have e₃ : sval (g i) (𝟙 _ ≫ (DegPre.prB D F).left) y J =
      gs (𝟙 _ ≫ (DegPre.prB D F).left) y ⊤ (scal D.P.A.hom (r i)) * sval (b i) (𝟙 _ ≫ (DegPre.prB D F).left) y J := by
    have hm := hJ.mem (D.famφB α) (𝟙 _ ≫ (DegPre.prB D F).left)
    exact (congrArg (gs _ y _) (hg i _)).trans ((gs_mul _ y _ hm _ _).trans
      (congrArg₂ (· * ·) (gs_res _ y le_top hm _) rfl))
  have e₄ : gs (𝟙 _) y ⊤ (DVR.gF D F (ιF ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (c i) * u i))) =
      constVal (𝟙 _ ≫ (fst (TF (R := R) F) D.P.A).left) y
        (ιF ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (c i) * u i)) :=
    gs_scal (fst (TF (R := R) F) D.P.A).left _ y _
  rw [sval_pullSec _ _ _ _ _ y hJ, a₁, ← secScal_sval (hG i) _ y hJ, e₃, e₄, gs_scal, gs_scal, a₂, a₃,
    constVal_specMap, constVal_specMap, constVal_specMap, ← _root_.mul_assoc, ← constVal_mul, ← map_mul,
    _root_.mul_assoc _ (u i), hu, _root_.mul_one]

theorem zero_term {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ψ : K → (Y' ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y} {g : LB.Sec (LB.LinComb L φ ε)} (hg : ∀ j, g.f j = 0)
    {G : LB.Sec (LB.LinComb L ψ ε)} (hG : GeneratorPullback.SecScal L ψ ε G φ ε g h 1) (j) : G.f j = 0 := by
  refine sec_ext_val hL (s' := DVR.SecOps.secZero) (fun y J hJ => ?_) j
  rw [← secScal_sval hG _ y hJ, DVR.UUA.sval_zero_of hg _ y J (hJ.mem _ _),
    DVR.UUA.sval_zero_of (s := DVR.SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]


open DVR in
theorem exists_span_generate : PolBaseChangeSt → GlobalFnsSt → DVR.TwistBaseChangeStatement → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R), AdmBase R I → ∀ (φ : R →+* R') (D : DegData R I) (D' : DegPre R') (hD : IsPullDeg φ D.toPre D') (k : ℕ), 1 ≤ k → ∃ (n : ℕ) (F₀ : Fin n → Fam D.toPre (FractionRing R) k) (f : Fin n → ∀ α, D.toPre.SecB k α) (F₁ : Fin n → Fam D' (FractionRing R') k) (f' : Fin n → ∀ α, D'.SecB k α), (∀ i, (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) ((F₀ i).s α) (D.toPre.famφB α) (DegPre.famε k) (f i α) (DegPre.prB D.toPre (FractionRing R)).left 1) ∧ (∀ α, GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' (FractionRing R') α) (DegPre.famε k) ((F₁ i).s α) (D'.famφB α) (DegPre.famε k) (f' i α) (DegPre.prB D' (FractionRing R')).left 1) ∧ (∀ x : D'.X, (∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (p : Fin 4 → D.toPre.P.L.ι) (q : Fin 4 → D'.P.L.ι), (∀ κ, ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((D'.famφB x) κ (r z)) ∈ D.toPre.P.L.U (p κ)) → (∀ κ, (D'.famφB x) κ (r z) ∈ D'.P.L.U (q κ)) → Geo.Tor.gs (r ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) z (LB.wchart D.toPre.P.L (D.toPre.famφB (hD.xe x)) p) ((f i (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (D'.famφB x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.P.L (D'.famφB x) q) ((f' i x).f q)))) ∧ Submodule.span (FractionRing R') (Set.range F₁) = ⊤ ∧ (∀ (S : Type) [CommRing S] [IsDomain S] [ValuationRing S] (σ : R →+* S) (F : Type) [Field F] [Algebra (FractionRing R) F] (ιF : S →+* F), Function.Injective ιF → ∀ (ρ : TF (R := R) F ⟶ (Over.mk (specOf σ))), ρ.left = specOf ιF → ∀ (F' : Type) [Field F'] [Algebra (FractionRing R') F'] (π : S →+* F'), IsLocalHom π → (∀ r : R, π (σ r) = algebraMap (FractionRing R') F' (algebraMap R' (FractionRing R') (φ r))) → ∀ s : Fam D.toPre F k, (∃ g : ∀ α, LB.Sec (LB.LinComb D.toPre.P.L (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k)), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α) (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k) (g α) (ρ ▷ D.toPre.P.A).left 1)) → ∃ c : Fin n → S, ∀ α, GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α) (D.toPre.famφB α) (DegPre.famε k) (fun i => f i α) (DegPre.prB D.toPre F).left (fun i => scal (fst (TF (R := R) F) D.toPre.P.A).left (ιF (c i)))) := by
  intro hP hG hT R R' _ _ _ _ I hA φ D D' hD k hk
  classical
  have : IsNoetherianRing R := hA.1
  let pt : (TK R').left := genericPoint (Spec (CommRingCat.of (FractionRing R')))
  let P : Spec (CommRingCat.of R) := (jK R' ≫ specOf φ) pt
  have hPW : P ∈ hD.W := by
    show (jK R' ≫ specOf φ) pt ∈ hD.W
    rw [← hD.g_comm]
    exact (hD.g pt).2
  have hne : ∀ r : R, r ∉ P.asIdeal → algebraMap R' (FractionRing R') (φ r) ≠ 0 := fun r hr h => hr (by
    show algebraMap R' (FractionRing R') (φ r) ∈ PrimeSpectrum.asIdeal pt
    rw [h]; exact Ideal.zero_mem _)
  have hgen : genericPoint (Spec (CommRingCat.of R)) ∈ hD.W :=
    (genericPoint_specializes P).mem_open hD.W.isOpen hPW
  have := P.isPrime
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul D'.X k hk
  choose b hb using fun α => GlobalTheory.TwistLoc.exists_basis_off_prime hP hG hT R D.toPre ⟨hD.W, hgen, ⟨hD.psiW⟩⟩ P.asIdeal k hk α
  choose r hr F f hF hfρ hf0 using fun q : Fin (k ^ Module.finrank ℤ D'.X) × Fin (k ^ D.toPre.P.g) =>
    integralFamily_at_prime hG R I hA D hD.W ⟨hD.psiW⟩ P hPW k hk (hD.xe (e q.1)) (b (hD.xe (e q.1)) q.2)
  choose f' hf' using fun q x => (SecPull.existsUnique_secPull _ _ _ _ D.toPre.P.L D'.P.L _ D.toPre.P.isLB D'.P.isLB
    hD.w hD.w_gen (Fin 4) (D'.famφB x) (D.toPre.famφB (hD.xe x)) (DegPre.famε k) _ (famφB_comm hD x)
    (f q (hD.xe x))).exists
  choose F' hF' using fun q => exists_fam_of_isPullDeg hG R R' φ D.toPre D' hD k (F q) (f q) (f' q) (hF q) (hf' q)
  let en := (finProdFinEquiv (m := k ^ Module.finrank ℤ D'.X) (n := k ^ D.toPre.P.g)).symm
  have hoff : ∀ i i' l, i' ≠ i → ∀ j, (f (i', l) (hD.xe (e i))).f j = 0 := fun i i' l hi =>
    hf0 (i', l) _ fun mu hmu => hi ((he (e i)).unique ⟨hD.xe.symm mu, hD.xe.injective (by
      rw [map_add (f := _), map_nsmul, AddEquiv.apply_symm_apply]; exact hmu.symm)⟩ ⟨0, by rw [smul_zero, add_zero]⟩)
  refine ⟨_, fun i => F (en i), fun i => f (en i), fun i => F' (en i), fun i => f' (en i),
    fun i => ⟨hF _, hF' _, hf' _⟩, ?_, ?_⟩
  · have hrange : Set.range (fun i => F' (en i)) = Set.range F' := en.surjective.range_comp F'
    rw [hrange, eq_top_iff]
    rintro s -
    choose c hc using fun i => span_term hD k (e i) (b (hD.xe (e i))) (fun l => f (i, l) (hD.xe (e i)))
      (hb _ _ _ (fun t ht => (hne t ht).isUnit) _ (fun _ _ => rfl)) (fun l => r (i, l)) (fun l => hne _ (hr (i, l)))
      (fun l => hfρ (i, l)) (fun l => f' (i, l) (e i))
      (fun l y J J' hJ hJ' => val_of_rel (famφB_comm hD (e i)) (hf' (i, l) (e i)) _ y hJ hJ')
      (fun l => (F' (i, l)).s (e i)) (fun l => hF' (i, l) (e i)) (s.s (e i))
    have hs : s = ∑ q : Fin (k ^ Module.finrank ℤ D'.X) × Fin (k ^ D.toPre.P.g), c q.1 q.2 • F' q := by
      refine fam_ext fun χ j => ?_
      obtain ⟨i, ⟨m, rfl⟩, -⟩ := he χ
      refine fam_eq_on_class_of_eq hG R' D' _ k s _ (e i) (fun j => ?_) m j
      rw [sum_f, Fintype.sum_prod_type, Finset.sum_eq_single i, hc i j]
      · rfl
      · intro i' _ hi
        refine Finset.sum_eq_zero fun l _ => ?_
        have h0 := zero_sec D.toPre.P.isLB D'.P.isLB (DegPre.prB D' (FractionRing R')).left (f (i', l) (hD.xe (e i)))
          (hoff i i' l hi) (f' (i', l) (e i))
          (fun y J J' hJ hJ' => val_of_rel (famφB_comm hD (e i)) (hf' (i', l) (e i)) _ y hJ hJ')
          ((F' (i', l)).s (e i)) (hF' (i', l) (e i)) j
        rw [smul_f, h0, mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hs]
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
  · rintro S _ _ _ σ E _ _ ιE - ρ hρ E' _ _ π hπ hπσ s ⟨sg, hsg⟩
    have hun : ∀ t : R, t ∉ P.asIdeal → IsUnit (σ t) := fun t ht => hπ.map_nonunit _ (by
      rw [hπσ]
      exact ((hne t ht).isUnit).map _)
    choose θ hθ using fun q => FamBaseChange.main hG R I D k (F q) (f q) (hF q) E
    choose c hc using fun i => comb_term σ ιE ρ hρ k (hD.xe (e i)) (b (hD.xe (e i))) (fun l => f (i, l) (hD.xe (e i)))
      (hb _ _ _ hun _ (fun _ _ => rfl)) (fun l => r (i, l)) (fun l => hun _ (hr (i, l))) (fun l => hfρ (i, l))
      (fun l => (θ (i, l)).s (hD.xe (e i))) (fun l => hθ (i, l) _) (s.s (hD.xe (e i))) (sg _) (hsg _)
    have hs : s = ∑ q : Fin (k ^ Module.finrank ℤ D'.X) × Fin (k ^ D.toPre.P.g), ιE (c q.1 q.2) • θ q := by
      refine fam_ext fun χ j => ?_
      obtain ⟨i, ⟨m, hm⟩, -⟩ := he (hD.xe.symm χ)
      obtain rfl : χ = hD.xe (e i) + k • hD.xe m := by
        rw [← map_nsmul, ← map_add (f := _), ← hm, AddEquiv.apply_symm_apply]
      refine fam_eq_on_class_of_eq hG R D.toPre _ k s _ (hD.xe (e i)) (fun j => ?_) _ j
      rw [sum_f, Fintype.sum_prod_type, Finset.sum_eq_single i, hc i j]
      · rfl
      · intro i' _ hi
        refine Finset.sum_eq_zero fun l _ => ?_
        rw [smul_f, zero_term D.toPre.P.isLB (hoff i i' l hi) (hθ (i', l) _) j, mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [← en.sum_comp] at hs
    refine ⟨fun i => c (en i).1 (en i).2, fun α => (secLin_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_⟩
    refine (sval_lin (fun i => gF D.toPre E (ιE (c (en i).1 (en i).2))) (fun i => (θ (en i)).s α)
      (fun j => (congrArg (fun t : Fam D.toPre E k => (t.s α).f j) hs).trans (sum_f _ _ α j)) _ y hJ).trans
      (Finset.sum_congr rfl fun i _ => ?_)
    rw [secScal_sval (hθ (en i) α) _ y hJ]
    rfl

end GlobalTheory.FamGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralFamiliesSpanGenerateValuationRingsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_integral_families_span_generate_valuationRings : PolBaseChangeSt → GlobalFnsSt → DVR.TwistBaseChangeStatement → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R), AdmBase R I → ∀ (φ : R →+* R') (D : DegData R I) (D' : DegPre R') (hD : IsPullDeg φ D.toPre D') (k : ℕ), 1 ≤ k → ∃ (n : ℕ) (F₀ : Fin n → Fam D.toPre (FractionRing R) k) (f : Fin n → ∀ α, D.toPre.SecB k α) (F₁ : Fin n → Fam D' (FractionRing R') k) (f' : Fin n → ∀ α, D'.SecB k α), (∀ i, (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) ((F₀ i).s α) (D.toPre.famφB α) (DegPre.famε k) (f i α) (DegPre.prB D.toPre (FractionRing R)).left 1) ∧ (∀ α, GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' (FractionRing R') α) (DegPre.famε k) ((F₁ i).s α) (D'.famφB α) (DegPre.famε k) (f' i α) (DegPre.prB D' (FractionRing R')).left 1) ∧ (∀ x : D'.X, (∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (p : Fin 4 → D.toPre.P.L.ι) (q : Fin 4 → D'.P.L.ι), (∀ κ, ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((D'.famφB x) κ (r z)) ∈ D.toPre.P.L.U (p κ)) → (∀ κ, (D'.famφB x) κ (r z) ∈ D'.P.L.U (q κ)) → Geo.Tor.gs (r ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) z (LB.wchart D.toPre.P.L (D.toPre.famφB (hD.xe x)) p) ((f i (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (D'.famφB x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.P.L (D'.famφB x) q) ((f' i x).f q)))) ∧ Submodule.span (FractionRing R') (Set.range F₁) = ⊤ ∧ (∀ (S : Type) [CommRing S] [IsDomain S] [ValuationRing S] (σ : R →+* S) (F : Type) [Field F] [Algebra (FractionRing R) F] (ιF : S →+* F), Function.Injective ιF → ∀ (ρ : TF (R := R) F ⟶ (Over.mk (specOf σ))), ρ.left = specOf ιF → ∀ (F' : Type) [Field F'] [Algebra (FractionRing R') F'] (π : S →+* F'), IsLocalHom π → (∀ r : R, π (σ r) = algebraMap (FractionRing R') F' (algebraMap R' (FractionRing R') (φ r))) → ∀ s : Fam D.toPre F k, (∃ g : ∀ α, LB.Sec (LB.LinComb D.toPre.P.L (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k)), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α) (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k) (g α) (ρ ▷ D.toPre.P.A).left 1)) → ∃ c : Fin n → S, ∀ α, GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α) (D.toPre.famφB α) (DegPre.famε k) (fun i => f i α) (DegPre.prB D.toPre F).left (fun i => scal (fst (TF (R := R) F) D.toPre.P.A).left (ιF (c i)))) := by
  first | exact @GlobalTheory.FamGen.exists_span_generate | exact GlobalTheory.FamGen.exists_span_generate | (intros; apply GlobalTheory.FamGen.exists_span_generate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PhiSpecialises
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace PhiSpec

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

section Base

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T : Over (Spec (CommRingCat.of R))}

def trT (m : T ⟶ D.P.A) : T ⊗ D.P.A ⟶ T ⊗ D.P.A :=
  lift (fst _ _) (padd D.P.A (snd _ _) (fst _ _ ≫ m))

theorem trT_fst (m : T ⟶ D.P.A) : trT D m ≫ fst _ _ = fst _ _ := lift_fst _ _

theorem trT_snd (m : T ⟶ D.P.A) : trT D m ≫ snd _ _ = snd _ _ * (fst _ _ ≫ m) := lift_snd _ _

def lineT (m : T ⟶ D.P.A) : Fin 2 → (T.left ⟶ D.P.A.left) := ![(1 : T ⟶ D.P.A).left, m.left]

def uT (k : ℕ) (α : D.X) (m : T ⟶ D.P.A) {T₁ : Over (Spec (CommRingCat.of R))} (ρ : T₁ ⟶ T ⊗ D.P.A)
    (z : T₁.left) (J : (T₁.left ⟶ D.P.A.left) → D.P.L.ι) : (T₁.left.presheaf.stalk z)ˣ :=
  cubN (th D z J) k (cP D T₁ α) (ρ ≫ fst _ _ ≫ m) (ρ ≫ snd _ _) *
    (th D z J (cP D T₁ α) (ρ ≫ snd _ _) (ρ ≫ fst _ _ ≫ m))⁻¹

theorem gen_uT (k : ℕ) (α α' : D.X) (m : T ⟶ D.P.A)
    (hα : cP D _ α' = cP D _ α * m ^ k) {K : Type} [Fintype K]
    {φ : K → (T.left ⟶ D.P.A.left)} {ε : K → ℤ}
    (vO : LB.Gen (LB.LinComb D.P.L φ ε)) (hvO : vO.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U), ∏ i, h (φ i) ^ ε i =
      (h (cP D _ α * m).left)⁻¹ * h (cP D _ α).left * h m.left * (h (1 : T ⟶ D.P.A).left)⁻¹ *
        (h m.left ^ k)⁻¹ * h (1 : T ⟶ D.P.A).left ^ k) :
    ∃ u : LB.Gen (LB.LinComb D.P.L (Sum.elim (fun i => (snd T D.P.A).left ≫ D.famφB α' i)
        (fun i => (trT D m ≫ snd _ _).left ≫ D.famφB α i)) (DegPre.deltaε k)), u.IsGen ∧
      ∀ (T₁ : Over (Spec (CommRingCat.of R))) (ρ : T₁ ⟶ T ⊗ D.P.A) (z : T₁.left) (J), Good D.P.L z J →
        val u ρ.left z J = uT D k α m ρ z J * val vO (ρ ≫ fst _ _).left z J := by
  let a : T ⊗ D.P.A ⟶ D.P.A := cP D _ α
  let mm : T ⊗ D.P.A ⟶ D.P.A := fst _ _ ≫ m
  let x : T ⊗ D.P.A ⟶ D.P.A := snd _ _
  have hα' : cP D (T ⊗ D.P.A) α' = a * mm ^ k := by
    rw [← comp_cP D (fst T D.P.A), hα]
    exact (map_mul (preHom (fst T D.P.A)) _ _).trans
      (congrArg₂ (· * ·) (comp_cP D _ α) (map_pow (preHom (fst T D.P.A)) _ _))
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub a mm x k
  obtain ⟨u₀, hu₀, vu₀⟩ := exists_gen D.P.isLB (φ' := Sum.elim (fun i => (snd T D.P.A).left ≫ D.famφB α' i)
      (fun i => (trT D m ≫ snd _ _).left ≫ D.famφB α i)) (ε' := DegPre.deltaε k) (fun U _ h => by
      have p₁ := prod_cub a x mm h
      have p₂ := hF U (fun q => h ((fst T D.P.A).left ≫ q))
      have p₃ := SectionScalarValuation.prod_famB D (snd T D.P.A) α' k h
      have p₄ := SectionScalarValuation.prod_famB D (trT D m ≫ snd _ _) α k h
      have q₁ : (fst T D.P.A).left ≫ (cP D _ α * m).left = (a * mm).left :=
        congrArg (fun q : T ⊗ D.P.A ⟶ D.P.A => q.left)
          ((MonObj.comp_mul (fst T D.P.A) (cP D _ α) m).trans
            (congrArg (· * mm) (comp_cP D (fst T D.P.A) α)))
      have q₂ : (fst T D.P.A).left ≫ (cP D _ α).left = a.left :=
        congrArg (fun q : T ⊗ D.P.A ⟶ D.P.A => q.left) (comp_cP D (fst T D.P.A) α)
      have q₃ : (fst T D.P.A).left ≫ (1 : T ⟶ D.P.A).left = (1 : T ⊗ D.P.A ⟶ D.P.A).left :=
        congrArg (fun q : T ⊗ D.P.A ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (fst T D.P.A))
      have q₄ : (fst T D.P.A).left ≫ m.left = mm.left := rfl
      rw [q₁, q₂, q₃, q₄] at p₂
      have c₁ : SectionScalarValuation.cQ D (T ⊗ D.P.A) α' = a * mm ^ k := hα'
      have c₂ : SectionScalarValuation.cQ D (T ⊗ D.P.A) α = a := rfl
      rw [c₁] at p₃
      rw [c₂] at p₄
      conv at p₄ => rhs; rw [trT_snd]
      refine Eq.trans (prod_sum₂ (K := Fin 8 ⊕ thK) (K' := K) (U := U) _
        (prod_sum₂ (K := Fin 8) (K' := thK) (U := U) _ rfl (prod_neg _ _ p₁)) p₂)
        (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)).symm)
      have r1 : x * (a * mm ^ k) = a * mm ^ k * x := mul_comm _ _
      have r2 : x * mm * a = a * x * mm := by rw [mul_comm, ← _root_.mul_assoc]
      have r3 : mm * x = x * mm := mul_comm _ _
      rw [r1, r2, r3]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, a, mm, x]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ N (LB.invGen D.P.L _ _
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift a (lift x mm)).left)))
      (LB.pullGen D.P.L _ _ vO (fst T D.P.A).left))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN (invGen_isGen _ _ _ _
      (pullGen_isGen _ _ _ _ D.cub.isGen _))) (pullGen_isGen _ _ _ _ hvO _))
  refine ⟨u₀, hu₀, fun T₁ ρ z J hJ => ?_⟩
  refine (vu₀ _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    ((congrArg₂ (· * ·) (vN T₁ ρ z J hJ) ((val_inv _ _).trans
      (congrArg (·⁻¹) (val_cub D.cub ρ hJ _ _ _)))).trans ?_)) (val_pull hJ _ _ _)))
  rw [uT, ← comp_cP D ρ α]

abbrev SecT (T : Over (Spec (CommRingCat.of R))) (k : ℕ) (α : D.X) : Type :=
  LB.Sec (LB.LinComb D.P.L (fun i => (snd T D.P.A).left ≫ D.famφB α i) (DegPre.famε k))

variable {D}

def PhiT {k : ℕ} (y : D.X) (gp : GtPt D T) (w : LB.Gen (LB.LinComb D.P.L (lineT D gp.b) (DegPre.lineε k)))
    (g g₂ : ∀ α, SecT D T k α) : Prop :=
  ∀ (α β : D.X), α + y = β → ∀ (T₁ : Over (Spec (CommRingCat.of R))) (ρ : T₁ ⟶ T ⊗ D.P.A) (z : T₁.left) (J),
    Good D.P.L z J → sval (g₂ β) ρ.left z J = sval (g α) (ρ ≫ trT D gp.b).left z J *
      (uT D k α gp.b ρ z J * (val (gp.s α) (ρ ≫ fst _ _).left z J * val w (ρ ≫ fst _ _).left z J)).val

theorem exists_phiT {k : ℕ} (y : D.X) (gp : GtPt D T) (hy : cP D T y = gp.b ^ k)
    (w : LB.Gen (LB.LinComb D.P.L (lineT D gp.b) (DegPre.lineε k))) (hw : w.IsGen) (g : ∀ α, SecT D T k α) :
    ∃ g₂ : ∀ α, SecT D T k α, PhiT y gp w g g₂ := by
  have ex : ∀ β, ∃ t : SecT D T k β, ∀ α, α + y = β →
      ∀ (T₁ : Over (Spec (CommRingCat.of R))) (ρ : T₁ ⟶ T ⊗ D.P.A) (z : T₁.left) (J),
      Good D.P.L z J → sval t ρ.left z J = sval (g α) (ρ ≫ trT D gp.b).left z J *
        (uT D k α gp.b ρ z J * (val (gp.s α) (ρ ≫ fst _ _).left z J * val w (ρ ≫ fst _ _).left z J)).val := by
    intro β
    obtain ⟨α₀, rfl⟩ : ∃ α₀, α₀ + y = β := ⟨β - y, sub_add_cancel _ _⟩
    obtain ⟨u, hu, hv⟩ := gen_uT D k α₀ (α₀ + y) gp.b (by rw [cPoint_add, hy]) _
      (mulGen_isGen _ _ _ _ _ _ _ (gp.isGen α₀) hw) (fun U _ h => by
        refine (Fintype.prod_sum_type _).trans ?_
        rw [Fin.prod_univ_four, Fin.prod_univ_two]
        show h (cP D _ α₀ * gp.b).left ^ (-1 : ℤ) * h (cP D _ α₀).left ^ (1 : ℤ) * h gp.b.left ^ (1 : ℤ) *
          h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) *
          (h (1 : T ⟶ D.P.A).left ^ (k : ℤ) * h gp.b.left ^ (-(k : ℤ))) = _
        simp only [zpow_neg, zpow_one, zpow_natCast]
        ac_rfl)
    obtain ⟨t, ht⟩ := exists_sec D.P.isLB (φ' := fun i => (snd T D.P.A).left ≫ D.famφB (α₀ + y) i)
      (ε' := DegPre.famε k) (fun U _ h => by
        refine Eq.trans (prod_sum₂ (K := Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _
          (c := ∏ i, h ((trT D gp.b ≫ snd _ _).left ≫ D.famφB α₀ i) ^ DegPre.famε k i)
          (Finset.prod_congr rfl fun i _ => congrArg (fun q => h q ^ DegPre.famε k i) (Category.assoc _ _ _).symm)
          (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
            (c := ∏ i, h ((snd T D.P.A).left ≫ D.famφB (α₀ + y) i) ^ DegPre.famε k i) rfl (prod_neg _ _ rfl))) ?_
        exact (mul_comm _ _).trans (inv_mul_cancel_right _ _)) (pullMulSec (g α₀) (trT D gp.b).left u hu)
    refine ⟨t, fun α hα T₁ ρ z J hJ => ?_⟩
    obtain rfl : α = α₀ := add_right_cancel hα
    exact (ht _ _ z J hJ).trans ((sval_pullMulSec _ _ _ _ _ z hJ).trans
      (congrArg₂ (· * ·) rfl (congrArg Units.val ((hv T₁ ρ z J hJ).trans
        (congrArg₂ (· * ·) rfl (val_mul hJ _ _ _))))))
  choose t ht using ex
  exact ⟨t, fun α β h => ht β α h⟩

variable {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem generic_fibre {k : ℕ} (gp : GtPt D T) (ρ : TF (R := R) F ⟶ T) (p : QkPt D F k)
    (hp : GtPt.IsPullF F ρ.left gp p.g)
    (w : LB.Gen (LB.LinComb D.P.L (lineT D gp.b) (DegPre.lineε k)))
    (ν : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)))
    (hν : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) (J), Good D.P.L z J →
      val ν r z J = val w (r ≫ ρ.left) z J)
    (s s₂ : Fam D F k) (g g₂ : ∀ α, SecT D T k α) (H : PhiVal p ν s.s s₂.s) (HT : PhiT p.y gp w g g₂)
    (hs : ∀ α, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (s.s α)
      (fun i => (snd T D.P.A).left ≫ D.famφB α i) (DegPre.famε k) (g α) (ρ ▷ D.P.A).left 1) (β : D.X) :
    GeneratorPullback.SecScal D.P.L (DegPre.famφ D F β) (DegPre.famε k) (s₂.s β)
      (fun i => (snd T D.P.A).left ≫ D.famφB β i) (DegPre.famε k) (g₂ β) (ρ ▷ D.P.A).left 1 := by
  refine SectionScalarValuation.secScal_of_sval D.P.isLB fun y J hJ => ?_
  have hb : ρ ≫ gp.b = p.g.b := Over.OverMorphism.ext hp.1.symm
  have e₁ := H (β - p.y) β (sub_add_cancel _ _) _ (𝟙 _) y J hJ
  have e₂ := HT (β - p.y) β (sub_add_cancel _ _) _ (ρ ▷ D.P.A) y J hJ
  have e₃ := SectionScalarValuation.secScal_sval (hs (β - p.y)) (DegPre.trPt D F p.g.b).left y hJ
  have t : ρ ▷ D.P.A ≫ trT D gp.b = DegPre.trPt D F p.g.b ≫ ρ ▷ D.P.A := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, trT_fst, Category.assoc, whiskerRight_fst, ← Category.assoc, tr_fst]
    · rw [Category.assoc, trT_snd, MonObj.comp_mul, whiskerRight_snd, Category.assoc, whiskerRight_snd, tr_pr,
        ← Category.assoc, whiskerRight_fst, Category.assoc, hb]
  have u : uT D k (β - p.y) gp.b (ρ ▷ D.P.A) y J = uVal D F k (β - p.y) p.g.b (𝟙 _) y J := by
    rw [uVal_id, uT, ← Category.assoc, whiskerRight_fst, Category.assoc, hb, whiskerRight_snd]
  have v₁ := (val_corr hJ (hp.2 (β - p.y)) (fst (TF (R := R) F) D.P.A).left).trans (val_pull hJ _ _ _)
  have v₂ := hν _ (fst (TF (R := R) F) D.P.A).left y J hJ
  rw [t, u, whiskerRight_fst] at e₂
  rw [Category.id_comp, Category.id_comp, val_mul hJ, v₁, v₂, ← e₃] at e₁
  rw [Category.id_comp]
  exact e₂.trans e₁.symm

end Base

section Charts

variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {G : X' ⟶ X} {K : Type} [Fintype K]

theorem gs_of_charts {w : LB.Iso L' (L.pull G)} (hw : PGen w) {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X')} {ε : K → ℤ}
    {h : Y' ⟶ Y} (hψ : ∀ k, φ' k ≫ G = h ≫ φ k) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L' φ' ε))
    (r : Z ⟶ Y') (z : Z) {p p' : K → L.ι} {q q' : K → L'.ι}
    (hp : ∀ k, G (φ' k (r z)) ∈ L.U (p k)) (hq : ∀ k, φ' k (r z) ∈ L'.U (q k))
    (hp' : ∀ k, G (φ' k (r z)) ∈ L.U (p' k)) (hq' : ∀ k, φ' k (r z) ∈ L'.U (q' k))
    (H : gs (r ≫ h) z (LB.wchart L φ p') (s.f p') =
      (∏ k, gw w (r ≫ φ' k) z (p' k) (q' k) ^ ε k).val * gs r z (LB.wchart L' φ' q') (s'.f q')) :
    gs (r ≫ h) z (LB.wchart L φ p) (s.f p) =
      (∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k).val * gs r z (LB.wchart L' φ' q) (s'.f q) := by
  have m : ∀ {p : K → L.ι}, (∀ k, G (φ' k (r z)) ∈ L.U (p k)) → (r ≫ h) z ∈ LB.wchart L φ p := fun hp =>
    Set.mem_iInter.2 fun k => by
      show φ k (h (r z)) ∈ L.U _
      rw [pt_eq hψ]; exact hp k
  have a := sec_trans s (r ≫ h) z (m hp) (m hp')
  have b := sec_trans s' r z (Set.mem_iInter.2 hq) (Set.mem_iInter.2 hq')
  have c := pw_trans hw φ' ε r z (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hp') (Set.mem_iInter.2 hq)
    (Set.mem_iInter.2 hq')
  have d : trF (fun k => φ' k ≫ G) ε r z p p' = trF φ ε (r ≫ h) z p p' :=
    Finset.prod_congr rfl fun k _ => by rw [Category.assoc, ← hψ k]
  rw [d] at c
  show _ = (pw w φ' ε r z p q).val * _
  rw [a, b, c, H]
  show _ * ((pw w φ' ε r z p' q').val * _) = _
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, mul_right_comm _ _ (trF φ' ε r z q q'),
    inv_mul_cancel_right]

end Charts

section Special

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} {T : Over (Spec (CommRingCat.of R))} {F : Type} [Field F] [Algebra (FractionRing R') F]
  (hD : IsPullDeg φ D D') {h : (TF (R := R') F).left ⟶ T.left} (hT : (TF (R := R') F).hom ≫ spMap φ = h ≫ T.hom)
  {Θ : (DegPre.BF D' F).left ⟶ (T ⊗ D.P.A).left}
  (hΘ₁ : Θ ≫ (fst T D.P.A).left = (fst (TF (R := R') F) D'.P.A).left ≫ h)
  (hΘ₂ : Θ ≫ (snd T D.P.A).left = (DegPre.prB D' F).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
  {T' : Over (Spec (CommRingCat.of R'))}

def liftB (ρ : T' ⟶ DegPre.BF D' F) : Over.mk (T'.hom ≫ spMap φ) ⟶ T ⊗ D.P.A :=
  Over.homMk (ρ.left ≫ Θ) (by
    show (ρ.left ≫ Θ) ≫ (T ⊗ D.P.A).hom = T'.hom ≫ spMap φ
    rw [← Over.w (fst T D.P.A), Category.assoc, ← Category.assoc Θ, hΘ₁, Category.assoc, ← hT, ← Over.w ρ,
      ← Over.w (fst (TF (R := R') F) D'.P.A)]
    simp only [Category.assoc])

theorem liftB_fst (ρ : T' ⟶ DegPre.BF D' F) :
    (liftB hT hΘ₁ ρ ≫ fst T D.P.A).left = (ρ ≫ fst (TF (R := R') F) D'.P.A).left ≫ h :=
  (Category.assoc _ _ _).trans ((congrArg (ρ.left ≫ ·) hΘ₁).trans (Category.assoc _ _ _).symm)

include hΘ₂ in
theorem liftB_pr (ρ : T' ⟶ DegPre.BF D' F) :
    liftB hT hΘ₁ ρ ≫ snd T D.P.A = pushHom (pull_grp hD) T' (ρ ≫ DegPre.prB D' F) :=
  Over.OverMorphism.ext ((Category.assoc _ _ _).trans ((congrArg (ρ.left ≫ ·) hΘ₂).trans (Category.assoc _ _ _).symm))

theorem liftB_pt (ρ : T' ⟶ DegPre.BF D' F) {b : T ⟶ D.P.A} {b' : TF (R := R') F ⟶ D'.P.A}
    (hb : b'.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ b.left) :
    liftB hT hΘ₁ ρ ≫ fst T D.P.A ≫ b =
      pushHom (pull_grp hD) T' (ρ ≫ fst (TF (R := R') F) D'.P.A ≫ b') := by
  refine Over.OverMorphism.ext ?_
  show (liftB hT hΘ₁ ρ).left ≫ (fst T D.P.A).left ≫ b.left =
    (ρ.left ≫ (fst (TF (R := R') F) D'.P.A).left ≫ b'.left) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))
  rw [← Category.assoc, ← Over.comp_left, liftB_fst, Category.assoc, ← hb]
  simp only [Over.comp_left, Category.assoc]

include hΘ₂ in
theorem liftB_tr (ρ : T' ⟶ DegPre.BF D' F) {b : T ⟶ D.P.A} {b' : TF (R := R') F ⟶ D'.P.A}
    (hb : b'.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ b.left) :
    liftB hT hΘ₁ ρ ≫ trT D b = liftB hT hΘ₁ (ρ ≫ DegPre.trPt D' F b') := by
  apply CartesianMonoidalCategory.hom_ext
  · refine Over.OverMorphism.ext ?_
    rw [Category.assoc, trT_fst, liftB_fst, liftB_fst, Category.assoc ρ, tr_fst]
  · refine Eq.trans ?_ (liftB_pr hD hT hΘ₁ hΘ₂ _).symm
    rw [Category.assoc, Category.assoc, trT_snd, tr_pr, MonObj.comp_mul, MonObj.comp_mul, map_mul,
      liftB_pr hD hT hΘ₁ hΘ₂, liftB_pt hD hT hΘ₁ ρ hb]

include hΘ₂ in
theorem liftB_fam (ρ : T' ⟶ DegPre.BF D' F) (x : D'.X) (κ : Fin 4) :
    (liftB hT hΘ₁ ρ).left ≫ (snd T D.P.A).left ≫ D.famφB (hD.xe x) κ =
      (ρ.left ≫ DegPre.famφ D' F x κ) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) := by
  fin_cases κ
  · exact (congrArg ((liftB hT hΘ₁ ρ).left ≫ ·) (Category.comp_id _)).trans
      (congrArg (fun q => q.left) (liftB_pr hD hT hΘ₁ hΘ₂ ρ))
  · have e : liftB hT hΘ₁ ρ ≫ snd T D.P.A ≫ (𝟙 D.P.A * cP D _ (hD.xe x)) =
        pushHom (pull_grp hD) T' (ρ ≫ (DegPre.prB D' F * cP D' _ x)) := by
      rw [MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_mul, map_mul, comp_cP, comp_cP, comp_cP, PhiPull.push_cP,
        Category.comp_id, liftB_pr hD hT hΘ₁ hΘ₂]
    exact congrArg (fun q => q.left) e
  · have e : liftB hT hΘ₁ ρ ≫ snd T D.P.A ≫ cP D _ (hD.xe x) = pushHom (pull_grp hD) T' (ρ ≫ cP D' _ x) := by
      rw [comp_cP, comp_cP, comp_cP, PhiPull.push_cP]
    exact congrArg (fun q => q.left) e
  · have e : liftB hT hΘ₁ ρ ≫ snd T D.P.A ≫ (1 : D.P.A ⟶ D.P.A) =
        pushHom (pull_grp hD) T' (ρ ≫ (1 : DegPre.BF D' F ⟶ D'.P.A)) := by
      rw [MonObj.comp_one, MonObj.comp_one, MonObj.comp_one, map_one]
    exact congrArg (fun q => q.left) e

include hT hΘ₁ hΘ₂ in
theorem fam_comm (x : D'.X) (κ : Fin 4) : DegPre.famφ D' F x κ ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) =
    Θ ≫ (snd T D.P.A).left ≫ D.famφB (hD.xe x) κ := by
  have e := liftB_fam hD hT hΘ₁ hΘ₂ (𝟙 (DegPre.BF D' F)) x κ
  exact ((congrArg (· ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) (Category.id_comp _)).symm.trans e.symm).trans
    (congrArg (· ≫ (snd T D.P.A).left ≫ D.famφB (hD.xe x) κ) (Category.id_comp Θ))


variable (Θ) in
def SecMaps {k : ℕ} (x : D'.X) (s : SecT D T k (hD.xe x))
    (s' : LB.Sec (LB.LinComb D'.P.L (DegPre.famφ D' F x) (DegPre.famε k))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D' F).left) (z : Z) (p : Fin 4 → D.P.L.ι) (q : Fin 4 → D'.P.L.ι),
    (∀ κ, (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ((DegPre.famφ D' F x) κ (r z)) ∈ D.P.L.U (p κ)) →
    (∀ κ, (DegPre.famφ D' F x) κ (r z) ∈ D'.P.L.U (q κ)) →
    gs (r ≫ Θ) z (LB.wchart D.P.L (fun i => (snd T D.P.A).left ≫ D.famφB (hD.xe x) i) p) (s.f p) =
      (∏ κ, gw hD.w (r ≫ (DegPre.famφ D' F x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val *
        gs r z (LB.wchart D'.P.L (DegPre.famφ D' F x) q) (s'.f q)

include hΘ₂ in
theorem sval_rel {k : ℕ} (x : D'.X) (s : SecT D T k (hD.xe x))
    (s' : LB.Sec (LB.LinComb D'.P.L (DegPre.famφ D' F x) (DegPre.famε k))) (H : SecMaps hD Θ x s s')
    (ρ : T' ⟶ DegPre.BF D' F) {z : T'.left} {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J')
    (Ω : (T' ⟶ D'.P.A) → (T'.left.presheaf.stalk z)ˣ)
    (hΩ : Ω = fun x => gw hD.w x.left z (J (x.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) (J' x.left)) :
    @Eq (T'.left.presheaf.stalk z) (sval s (liftB hT hΘ₁ ρ).left z J)
      ((Ω (ρ ≫ DegPre.prB D' F) ^ ((k : ℤ) - 1) * Ω (cP D' T' x * (ρ ≫ DegPre.prB D' F)) * (Ω (cP D' T' x))⁻¹ *
        Ω 1).val * sval s' ρ.left z J') := by
  subst hΩ
  have e := H _ ρ.left z (fun κ => J ((ρ.left ≫ DegPre.famφ D' F x κ) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))))
    (fun κ => J' (ρ.left ≫ DegPre.famφ D' F x κ)) (fun κ => hJ ((ρ.left ≫ DegPre.famφ D' F x κ) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))))
    (fun κ => hJ' (ρ.left ≫ DegPre.famφ D' F x κ))
  have p := prod_fam D' F ρ x k (fun q => gw hD.w q z (J (q ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) (J' q))
  refine (sval_of s (liftB hT hΘ₁ ρ).left z J _ (fun κ => congrArg J (liftB_fam hD hT hΘ₁ hΘ₂ ρ x κ))).trans
    (e.trans ?_)
  exact congrArg₂ (· * ·) (congrArg Units.val p) rfl

include hΘ₂ in
theorem secMaps_of_sval {k : ℕ} (x : D'.X) (s : SecT D T k (hD.xe x))
    (s' : LB.Sec (LB.LinComb D'.P.L (DegPre.famφ D' F x) (DegPre.famε k)))
    (H : ∀ (T' : Over (Spec (CommRingCat.of R'))) (ρ : T' ⟶ DegPre.BF D' F) (z : T'.left) (J J'),
      Good D.P.L z J → Good D'.P.L z J' → ∀ (Ω : (T' ⟶ D'.P.A) → (T'.left.presheaf.stalk z)ˣ),
      (Ω = fun x => gw hD.w x.left z (J (x.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) (J' x.left)) →
      @Eq (T'.left.presheaf.stalk z) (sval s (liftB hT hΘ₁ ρ).left z J)
      ((Ω (ρ ≫ DegPre.prB D' F) ^ ((k : ℤ) - 1) * Ω (cP D' T' x * (ρ ≫ DegPre.prB D' F)) * (Ω (cP D' T' x))⁻¹ *
        Ω 1).val * sval s' ρ.left z J')) : SecMaps hD Θ x s s' := by
  intro Z r z p q hp hq
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB z
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
  let ρ : Over.mk (r ≫ (DegPre.BF D' F).hom) ⟶ DegPre.BF D' F := Over.homMk r rfl
  have e := H _ ρ z J J' hJ hJ' _ rfl
  have pr := prod_fam D' F ρ x k (fun q => gw hD.w q z (J (q ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) (J' q))
  refine gs_of_charts ((isGen_iff hD.w).1 hD.w_gen) (fam_comm hD hT hΘ₁ hΘ₂ x) s s' r z hp hq
    (p' := fun κ => J ((r ≫ DegPre.famφ D' F x κ) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) (q' := fun κ => J' (r ≫ DegPre.famφ D' F x κ))
    (fun κ => hJ ((r ≫ DegPre.famφ D' F x κ) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) (fun κ => hJ' (r ≫ DegPre.famφ D' F x κ)) ?_
  refine (sval_of s (liftB hT hΘ₁ ρ).left z J _
    (fun κ => congrArg J (liftB_fam hD hT hΘ₁ hΘ₂ ρ x κ))).symm.trans (e.trans ?_)
  exact congrArg₂ (· * ·) (congrArg Units.val pr.symm) rfl

include hT in
theorem gt_comm {b : T ⟶ D.P.A} {b' : TF (R := R') F ⟶ D'.P.A} (hb : b'.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ b.left) (x : D'.X) (i : Fin 4) :
    DegPre.gtφ D' F b' x i ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ DegPre.gtφT D T b (hD.xe x) i := by
  let η₀ : Over.mk ((TF (R := R') F).hom ≫ spMap φ) ⟶ T := Over.homMk h hT.symm
  have eb : pushHom (pull_grp hD) _ b' = η₀ ≫ b := Over.OverMorphism.ext hb
  have ec : pushHom (pull_grp hD) _ (cP D' (TF (R := R') F) x) = η₀ ≫ cP D T (hD.xe x) := by
    rw [PhiPull.push_cP, comp_cP]
  fin_cases i
  · have e : pushHom (pull_grp hD) _ (cP D' (TF (R := R') F) x * b') = η₀ ≫ (cP D T (hD.xe x) * b) := by
      rw [map_mul, eb, ec, MonObj.comp_mul]
    exact congrArg (fun q => q.left) e
  · exact congrArg (fun q => q.left) ec
  · exact hb
  · have e : pushHom (pull_grp hD) _ (1 : TF (R := R') F ⟶ D'.P.A) = η₀ ≫ (1 : T ⟶ D.P.A) := by
      rw [map_one, MonObj.comp_one]
    exact congrArg (fun q => q.left) e

include hT in
theorem line_comm {b : T ⟶ D.P.A} {b' : TF (R := R') F ⟶ D'.P.A} (hb : b'.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ b.left) (i : Fin 2) :
    DegPre.lineφ D' F b' i ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ lineT D b i := by
  fin_cases i
  · exact gt_comm hD hT hb 0 3
  · exact hb

set_option maxHeartbeats 1000000 in
include hT hΘ₁ hΘ₂ in
theorem special_fibre (hG : GlobalFnsSt) {k : ℕ} (y : D.X) (gp : GtPt D T) (p : QkPt D' F k)
    (hy : p.y = hD.xe.symm y) (hb : p.g.b.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ gp.b.left)
    (hg : ∀ χ, PMaps hD.w (DegPre.gtφ D' F p.g.b χ) (DegPre.gtφT D T gp.b (hD.xe χ)) DegPre.gtε (p.g.s χ)
      (gp.s (hD.xe χ)) h)
    (w : LB.Gen (LB.LinComb D.P.L (lineT D gp.b) (DegPre.lineε k)))
    (ν' : LB.Gen (LB.LinComb D'.P.L (DegPre.lineφ D' F p.g.b) (DegPre.lineε k)))
    (hν : PMaps hD.w (DegPre.lineφ D' F p.g.b) (lineT D gp.b) (DegPre.lineε k) ν' w h)
    (g g₂ : ∀ α, SecT D T k α) (s' s₂' : Fam D' F k)
    (H₁ : ∀ x, SecMaps hD Θ x (g (hD.xe x)) (s'.s x)) (HT : PhiT y gp w g g₂) (H : PhiVal p ν' s'.s s₂'.s)
    (β : D'.X) : SecMaps hD Θ β (g₂ (hD.xe β)) (s₂'.s β) := by
  obtain ⟨α, rfl⟩ : ∃ α, α + p.y = β := ⟨β - p.y, sub_add_cancel _ _⟩
  refine secMaps_of_sval hD hT hΘ₁ hΘ₂ _ _ _ fun T' ρ z J J' hJ hJ' Ω hΩ => ?_
  have e := HT (hD.xe α) (hD.xe (α + p.y)) (by rw [map_add (f := _), hy, AddEquiv.apply_symm_apply]) _ (liftB hT hΘ₁ ρ) z J hJ
  have e' := H α _ rfl T' ρ z J' hJ'
  have v₁ := sval_rel hD hT hΘ₁ hΘ₂ _ _ _ (H₁ α) (ρ ≫ DegPre.trPt D' F p.g.b) hJ hJ' Ω hΩ
  let σ : T' ⟶ TF (R := R') F := ρ ≫ fst _ _
  have m₁ : ρ ≫ fst (TF (R := R') F) D'.P.A ≫ p.g.b = σ ≫ p.g.b := (Category.assoc _ _ _).symm
  have cy : cP D' T' (α + p.y) = cP D' T' α * (σ ≫ p.g.b) ^ k := by
    rw [cPoint_add, ← comp_cP D' σ p.y, cPoint_y]
    exact congrArg _ (map_pow (preHom σ) _ _)
  have tp : (ρ ≫ DegPre.trPt D' F p.g.b) ≫ DegPre.prB D' F = (ρ ≫ DegPre.prB D' F) * (σ ≫ p.g.b) := by
    rw [Category.assoc, tr_pr, MonObj.comp_mul, m₁]
  rw [cy]
  rw [tp, ← liftB_tr hD hT hΘ₁ hΘ₂ ρ hb] at v₁
  have vu : @Eq (T'.left.presheaf.stalk z)ˣ (uT D k (hD.xe α) gp.b (liftB hT hΘ₁ ρ) z J)
      (cubN (th D (T := Over.mk (T'.hom ≫ spMap φ)) z J) k (pushHom (pull_grp hD) T' (cP D' T' α))
        (pushHom (pull_grp hD) T' (σ ≫ p.g.b)) (pushHom (pull_grp hD) T' (ρ ≫ DegPre.prB D' F)) *
      (th D (T := Over.mk (T'.hom ≫ spMap φ)) z J (pushHom (pull_grp hD) T' (cP D' T' α))
        (pushHom (pull_grp hD) T' (ρ ≫ DegPre.prB D' F)) (pushHom (pull_grp hD) T' (σ ≫ p.g.b)))⁻¹) := by
    rw [uT, liftB_pt hD hT hΘ₁ ρ hb, liftB_pr hD hT hΘ₁ hΘ₂, PhiPull.push_cP, m₁]
  have vg : @Eq (T'.left.presheaf.stalk z)ˣ (val (gp.s (hD.xe α)) (liftB hT hΘ₁ ρ ≫ fst _ _).left z J)
      ((Ω (cP D' T' α * (σ ≫ p.g.b)))⁻¹ * Ω (cP D' T' α) * Ω (σ ≫ p.g.b) * (Ω 1)⁻¹ *
        val (p.g.s α) σ.left z J') := by
    have c := DegPull.pmaps_val (gt_comm hD hT hb α) (hg α) σ.left z hJ hJ'
    have pr := prod_gt p.g.b α (fun q => gw hD.w (σ.left ≫ q) z (J ((σ.left ≫ q) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) (J' (σ.left ≫ q)))
    rw [liftB_fst]
    refine c.trans (congrArg₂ (· * ·) (pr.trans ?_) rfl)
    rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul, comp_cP,
      MonObj.comp_one, hΩ]
  have vν : @Eq (T'.left.presheaf.stalk z)ˣ (val w (liftB hT hΘ₁ ρ ≫ fst _ _).left z J)
      (Ω 1 ^ (k : ℤ) * Ω (σ ≫ p.g.b) ^ (-(k : ℤ)) * val ν' σ.left z J') := by
    have c := DegPull.pmaps_val (line_comm hD hT hb) hν σ.left z hJ hJ'
    rw [liftB_fst]
    refine c.trans (congrArg₂ (· * ·) ((Fin.prod_univ_two _).trans ?_) rfl)
    have e₀ : σ.left ≫ DegPre.lineφ D' F p.g.b 0 = (1 : T' ⟶ D'.P.A).left :=
      congrArg (fun q : T' ⟶ D'.P.A => q.left) (MonObj.comp_one (M := D'.P.A) σ)
    have e₁ : σ.left ≫ DegPre.lineφ D' F p.g.b 1 = (σ ≫ p.g.b).left := rfl
    rw [e₀, e₁, hΩ]
    rfl
  have key := PhiPull.units_rel (pushHom (pull_grp hD) T') Ω (PhiPull.cub_rel hG hD hJ hJ' Ω hΩ) k (cP D' T' α)
    (σ ≫ p.g.b) (ρ ≫ DegPre.prB D' F) (val (p.g.s α) σ.left z J') (val ν' σ.left z J')
  have fin := e.trans (congrArg₂ (· * ·) v₁ (congrArg Units.val
    (congrArg₂ (· * ·) vu (congrArg₂ (· * ·) vg vν))))
  have alg : ∀ {S : Type} [CommRing S] (A₁ A₂ u u' : Sˣ) (a : S), A₁ * u = A₂ * u' →
      A₁.val * a * u.val = A₂.val * (a * u'.val) := by
    intro S _ A₁ A₂ u u' a h₁
    rw [mul_right_comm, ← Units.val_mul, h₁, Units.val_mul, _root_.mul_assoc, mul_comm a]
  rw [val_mul hJ', uVal, m₁] at e'
  refine fin.trans ((alg _ _ _ _ _ key).trans ?_)
  rw [e']

end Special

end PhiSpec

theorem phi_specialises : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre), ∀ (S : Type) [CommRing S] [IsDomain S] [ValuationRing S] (σ : R →+* S) (F : Type) [Field F] [Algebra (FractionRing R) F] (ιF : S →+* F), Function.Injective ιF → ∀ (ρ : TF (R := R) F ⟶ (Over.mk (specOf σ))), ρ.left = specOf ιF → ∀ (F' : Type) [Field F'] [Algebra (FractionRing R') F'] (π : S →+* F'), IsLocalHom π → (∀ r : R, π (σ r) = algebraMap (FractionRing R') F' (algebraMap R' (FractionRing R') (φ r))) → ∀ (Θ : (DegPre.BF D'.toPre F').left ⟶ ((Over.mk (specOf σ)) ⊗ D.toPre.P.A).left), Θ ≫ (fst (Over.mk (specOf σ)) D.toPre.P.A).left = (fst (TF (R := R') F') D'.toPre.P.A).left ≫ specOf π → Θ ≫ (snd (Over.mk (specOf σ)) D.toPre.P.A).left = (DegPre.prB D'.toPre F').left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) → ∀ (k : ℕ), 1 ≤ k → ∀ (gp : GtPt D.toPre (Over.mk (specOf σ))) (p₀ : QkPt D.toPre F k) (p₁ : QkPt D'.toPre F' k), GtPt.IsPullF F ρ.left gp p₀.g → p₁.y = hD.xe.symm p₀.y → p₁.g.b.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = specOf π ≫ gp.b.left → (∀ χ, Geo.Tor.PMaps hD.w (DegPre.gtφ D'.toPre F' p₁.g.b χ) (DegPre.gtφT D.toPre (Over.mk (specOf σ)) gp.b (hD.xe χ)) DegPre.gtε (p₁.g.s χ) (gp.s (hD.xe χ)) (specOf π)) → ∃ (ν : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₀.g.b) (DegPre.lineε k))) (ν' : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F' p₁.g.b) (DegPre.lineε k))), ν.IsGen ∧ ν'.IsGen ∧ ∀ (s : Fam D.toPre F k) (s' : Fam D'.toPre F' k) (g : ∀ α, LB.Sec (LB.LinComb D.toPre.P.L (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k))), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α) (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k) (g α) (ρ ▷ D.toPre.P.A).left 1) → (∀ (x : D'.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D'.toPre F').left) (z : Z) (p : Fin 4 → D.toPre.P.L.ι) (q : Fin 4 → D'.toPre.P.L.ι), (∀ κ, (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) ((DegPre.famφ D'.toPre F' x) κ (r z)) ∈ D.toPre.P.L.U (p κ)) → (∀ κ, (DegPre.famφ D'.toPre F' x) κ (r z) ∈ D'.toPre.P.L.U (q κ)) → Geo.Tor.gs (r ≫ Θ) z (LB.wchart D.toPre.P.L (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB (hD.xe x) i) p) ((g (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (DegPre.famφ D'.toPre F' x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.toPre.P.L (DegPre.famφ D'.toPre F' x) q) ((s'.s x).f q)) → ∃ (s₂ : Fam D.toPre F k) (s₂' : Fam D'.toPre F' k) (g₂ : ∀ α, LB.Sec (LB.LinComb D.toPre.P.L (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k))), PhiRel D.toPre F k p₀ ν s s₂ ∧ PhiRel D'.toPre F' k p₁ ν' s' s₂' ∧ (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s₂.s α) (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k) (g₂ α) (ρ ▷ D.toPre.P.A).left 1) ∧ (∀ (x : D'.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D'.toPre F').left) (z : Z) (p : Fin 4 → D.toPre.P.L.ι) (q : Fin 4 → D'.toPre.P.L.ι), (∀ κ, (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) ((DegPre.famφ D'.toPre F' x) κ (r z)) ∈ D.toPre.P.L.U (p κ)) → (∀ κ, (DegPre.famφ D'.toPre F' x) κ (r z) ∈ D'.toPre.P.L.U (q κ)) → Geo.Tor.gs (r ≫ Θ) z (LB.wchart D.toPre.P.L (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB (hD.xe x) i) p) ((g₂ (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (DegPre.famφ D'.toPre F' x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.toPre.P.L (DegPre.famφ D'.toPre F' x) q) ((s₂'.s x).f q)) := by
  intro hG R R' _ _ _ _ I I' φ D D' hD S _ _ _ σ F _ _ ιF hι ρ hρ F' _ _ π _ hπ Θ hΘ₁ hΘ₂ k _ gp p₀ p₁ hp hy hb hg
  have hT : (TF (R := R') F').hom ≫ Geo.Tor.spMap φ = specOf π ≫ (Over.mk (specOf σ)).hom :=
    (Category.assoc _ _ _).trans
      (((congrArg (jFK (R := R') F' ≫ ·) (Geo.Tor.spMap_comp φ _).symm).trans (Geo.Tor.spMap_comp _ _).symm).trans
        ((congrArg Geo.Tor.spMap (RingHom.ext fun r => (hπ r).symm)).trans (Geo.Tor.spMap_comp _ _)))
  have hb₀ : ρ ≫ gp.b = p₀.g.b := Over.OverMorphism.ext hp.1.symm
  have hk : DVR.cP D.toPre _ p₀.y = gp.b ^ k := by
    have : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
    have hd : IsDominant ρ.left := by
      rw [hρ]
      constructor
      exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical ιF).2
        (by rw [(RingHom.injective_iff_ker_eq_bot ιF).1 hι]; exact bot_le)
    have : IsReduced (Over.mk (specOf σ)).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of S)))
    have e : ρ ≫ DVR.cP D.toPre _ p₀.y = ρ ≫ gp.b ^ k := by
      rw [DVR.comp_cP, DVR.cPoint_y, ← hb₀]
      exact (map_pow (Geo.Tor.preHom ρ) _ _).symm
    exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated D.toPre.P.A.hom ((Over.w _).trans (Over.w _).symm)
      ρ.left (congrArg (fun q => q.left) e))
  obtain ⟨w, hw⟩ := DVR.exists_gen_of_local (V := S) D.toPre.P.L D.toPre.P.isLB (PhiSpec.lineT D.toPre gp.b)
    (DegPre.lineε k)
  obtain ⟨ν, hν, vν⟩ := Geo.Tor.exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre F p₀.g.b)
    (ε' := DegPre.lineε k) (fun U _ h => Finset.prod_congr rfl fun i _ => congrArg (fun q => h q ^ DegPre.lineε k i) (by
      fin_cases i
      · exact congrArg (fun q : TF (R := R) F ⟶ D.toPre.P.A => q.left) (MonObj.comp_one (M := D.toPre.P.A) ρ)
      · exact hp.1.symm))
    (LB.pullGen D.toPre.P.L _ _ w ρ.left) (DVR.pullGen_isGen _ _ _ _ hw _)
  obtain ⟨ν', hν', pm⟩ := DegPull.exists_pmaps ((Geo.Tor.isGen_iff hD.w).1 hD.w_gen) D.toPre.P.isLB D'.toPre.P.isLB
    (specOf π) (PhiSpec.line_comm hD hT hb) w hw
  refine ⟨ν, ν', hν, hν', fun s s' g hs hs' => ?_⟩
  obtain ⟨s₂, H⟩ := DVR.exists_phi hG p₀ ν hν D.tau_bimult s
  obtain ⟨s₂', H'⟩ := DVR.exists_phi hG p₁ ν' hν' D'.tau_bimult s'
  obtain ⟨g₂, HT⟩ := PhiSpec.exists_phiT p₀.y gp hk w hw g
  exact ⟨s₂, s₂', g₂, (DVR.phiRel_iff hG p₀ ν hν _ _).2 H, (DVR.phiRel_iff hG p₁ ν' hν' _ _).2 H',
    PhiSpec.generic_fibre gp ρ p₀ hp w ν
      (fun Z r z J hJ => (vν Z r z J hJ).trans (Geo.Tor.val_pull hJ _ _ _)) s s₂ g g₂ H HT hs,
    PhiSpec.special_fibre hD hT hΘ₁ hΘ₂ hG p₀.y gp p₁ hy hb hg w ν' pm g g₂ s' s₂' hs' HT H'⟩

end GlobalTheory
end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaSpecialise

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar GlobalTheory.ThetaBaseChange


set_option maxHeartbeats 1600000 in
theorem exists_families (hL : Laws) (hT : DVR.TwistBaseChangeStatement) {R R' : Type} [CommRing R] [IsDomain R]
    [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'} (hR : AdmBase R I) (φ : R →+* R') (D : DegData R I)
    (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) {S : Type} [CommRing S] [IsDomain S] [ValuationRing S]
    (σ : R →+* S) {F : Type} [Field F] [Algebra (FractionRing R) F] (g : S →+* F) (hg : Function.Injective g)
    (ρ : TF (R := R) F ⟶ Over.mk (specOf σ)) (hρ : ρ.left = specOf g) {F' : Type} [Field F']
    [Algebra (FractionRing R') F'] (π : S →+* F') (hπl : IsLocalHom π)
    (hπ : ∀ r : R, π (σ r) = algebraMap (FractionRing R') F' (algebraMap R' (FractionRing R') (φ r)))
    (hτ' : specOf π ≫ specOf σ = (jFK (R := R') F' ≫ jK R') ≫ specOf φ)
    (k : ℕ) (hk : 1 ≤ k) (gp : GtPt D.toPre (Over.mk (specOf σ))) (p₀ : QkPt D.toPre F k) (p₁ : QkPt D'.toPre F' k)
    (h₁ : GtPt.IsPullF F ρ.left gp p₀.g) (h₂ : p₁.y = hD.xe.symm p₀.y)
    (h₃ : p₁.g.b.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = specOf π ≫ gp.b.left)
    (h₄ : ∀ χ, PMaps hD.w (DegPre.gtφ D'.toPre F' p₁.g.b χ)
      (DegPre.gtφT D.toPre (Over.mk (specOf σ)) gp.b (hD.xe χ)) DegPre.gtε (p₁.g.s χ) (gp.s (hD.xe χ)) (specOf π)) :
    ∃ (n : ℕ) (F₀ : Fin n → Fam D.toPre (FractionRing R) k) (f : Fin n → ∀ α, D.toPre.SecB k α)
      (f' : Fin n → ∀ α, D'.toPre.SecB k α) (s : Fin n → Fam D.toPre F k) (s' : Fin n → Fam D'.toPre F' k)
      (c : Fin n → Fin n → S)
      (ν : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₀.g.b) (DegPre.lineε k)))
      (ν' : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F' p₁.g.b) (DegPre.lineε k))),
      ν.IsGen ∧ ν'.IsGen ∧
      (∀ i α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) ((F₀ i).s α)
        (D.toPre.famφB α) (DegPre.famε k) (f i α) (DegPre.prB D.toPre (FractionRing R)).left 1) ∧
      (∀ i x, PSec hD.w (D'.toPre.famφB x) (D.toPre.famφB (hD.xe x)) (DegPre.famε k)
        (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) (f' i x) (f i (hD.xe x))) ∧
      (∀ i α, IsPull (DegPre.prB D.toPre F).left ((s i).s α) (f i α)) ∧
      (∀ i α, IsPull (DegPre.prB D'.toPre F').left ((s' i).s α) (f' i α)) ∧
      Submodule.span F' (Set.range s') = ⊤ ∧
      ∀ i, PhiRel D.toPre F k p₀ ν (s i) (∑ l, g (c i l) • s l) ∧
        PhiRel D'.toPre F' k p₁ ν' (s' i) (∑ l, π (c i l) • s' l) := by
  have hG := hL.globalFns
  have hM := D.toPre.P.isLB
  obtain ⟨n, F₀, f, F₁, f', hf, hspan, hgen⟩ := GlobalTheory.T.exists_integral_families_span_generate_valuationRings hL.polBaseChange hG hT R R' I hR φ D D'.toPre hD k hk
  obtain ⟨Θ, hΘ₁, hΘ₂, -⟩ := exists_psi (pull_grp hD) (T := TF (R := R') F') (T₀ := Over.mk (specOf σ)) (specOf π) hτ'
  obtain ⟨ν, ν', hν, hν', hΦ⟩ := GlobalTheory.phi_specialises hG R R' I I' φ D D' hD S σ F g hg ρ hρ F' π hπl hπ Θ hΘ₁.w hΘ₂
    k hk gp p₀ p₁ h₁ h₂ h₃ h₄
  obtain ⟨πB, hπB⟩ : ∃ πB : (Over.mk (specOf σ) ⊗ D.toPre.P.A).left ⟶ Spec (CommRingCat.of S),
    πB = (fst (Over.mk (specOf σ)) D.toPre.P.A).left := ⟨_, rfl⟩
  have pb₀ : IsPullback (snd (Over.mk (specOf σ)) D.toPre.P.A).left πB D.toPre.P.A.hom
      (Spec.map (CommRingCat.ofHom σ)) := by rw [hπB]; exact (IsPullback.of_hasPullback _ _).flip
  have r₂ : (ρ ▷ D.toPre.P.A).left ≫ (snd (Over.mk (specOf σ)) D.toPre.P.A).left = (DegPre.prB D.toPre F).left := by
    rw [← Over.comp_left, whiskerRight_snd]
  have pb : IsPullback (ρ ▷ D.toPre.P.A).left (famBase D.toPre F) πB (Spec.map (CommRingCat.ofHom g)) := by
    refine IsPullback.of_right ?_ ?_ pb₀
    · have e : Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom σ) = (TF (R := R) F).hom :=
        (congrArg (· ≫ specOf σ) hρ).symm.trans (Over.w ρ)
      rw [r₂, e]
      exact (IsPullback.of_hasPullback _ _).flip
    · rw [hπB]
      exact (congrArg (fun q => q.left) (whiskerRight_fst ρ D.toPre.P.A)).trans
        (congrArg ((fst (TF (R := R) F) D.toPre.P.A).left ≫ ·) hρ)
  have : Flat πB := by
    have := D.toPre.P.isAb.smooth
    exact MorphismProperty.of_isPullback (P := @Flat) pb₀ inferInstance
  have c₁ : ∀ α κ, DegPre.famφ D.toPre F α κ = (ρ ▷ D.toPre.P.A).left ≫
      (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α κ := fun α κ => by
    rw [← Category.assoc, r₂, famφ_prB]
  have c₂ : ∀ x κ, DegPre.famφ D'.toPre F' x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) =
      Θ ≫ (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB (hD.xe x) κ := fun x κ => by
    rw [← Category.assoc Θ, hΘ₂, famφ_prB, Category.assoc, ExpGTrans.famφB_pull hD x κ]
    exact (Category.assoc _ _ _).symm
  let s : Fin n → Fam D.toPre F k := fun i => famPull D.toPre (FractionRing R) F hG k (F₀ i)
  let s' : Fin n → Fam D'.toPre F' k := fun i => famPull D'.toPre (FractionRing R') F' hG k (F₁ i)
  have hs : ∀ i α, IsPull (DegPre.prB D.toPre F).left ((s i).s α) (f i α) := fun i α =>
    isPull_famPull D.toPre F hG (F₀ i) α (f i α) ((hf i).1 α)
  have hs' : ∀ i α, IsPull (DegPre.prB D'.toPre F').left ((s' i).s α) (f' i α) := fun i α =>
    isPull_famPull D'.toPre F' hG (F₁ i) α (f' i α) ((hf i).2.1 α)
  obtain ⟨b, hb⟩ : ∃ b : Fin n → ∀ α, SecOver πB (LB.LinComb D.toPre.P.L
      (fun κ => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α κ) (DegPre.famε k)),
      ∀ i α, IsPull (snd (Over.mk (specOf σ)) D.toPre.P.A).left (b i α) (f i α) :=
    ⟨fun i α => pullOver D.toPre.P.L _ pb₀.w (fun _ => rfl) (f i α), fun i α => isPull_pullOver _ _ _⟩
  have b₁ : ∀ i α, GeneratorPullback.SecScal D.toPre.P.L _ _ ((s i).s α) _ _ (b i α) (ρ ▷ D.toPre.P.A).left 1 := fun i α =>
    (secScal_one_iff hM).2 fun y J hJ => by
      rw [(hb i α).sval _ hJ, (hs i α).sval _ hJ, Category.assoc, r₂]
  have b₂ : ∀ i x, PSec hD.w (DegPre.famφ D'.toPre F' x) _ (DegPre.famε k) Θ ((s' i).s x) (b i (hD.xe x)) :=
    fun i x => (psec_iff_of_isPull (c₂ x) (hb i (hD.xe x)) hΘ₂).2 (PSec.pull_left ((hf i).2.2 x) (hs' i x))
  choose s₂ s₂' b₀ q₁ q₂ q₃ q₄ using fun i => hΦ (s i) (s' i) (b i) (b₁ i) (b₂ i)
  choose c hc using fun i => hgen S σ F g hg ρ hρ F' π hπl hπ (s₂ i) ⟨b₀ i, q₃ i⟩
  let b' : Fin n → ∀ α, SecOver πB (LB.LinComb D.toPre.P.L
      (fun κ => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α κ) (DegPre.famε k)) := b₀
  have hc' : ∀ i α, famProj D.toPre F k α (s₂ i) = ∑ l, g (c i l) • famProj D.toPre F k α (s l) := fun i α =>
    (secLin_iff (π' := famBase D.toPre F) hM (famProj D.toPre F k α (s₂ i)) (fun l => f l α) _ (fun l => g (c i l))
      (fun l => famProj D.toPre F k α (s l)) (fun l y J hJ => (hs l α).sval _ hJ)).1 (hc i α)
  have e₁ : ∀ i, s₂ i = ∑ l, g (c i l) • s l := fun i => fam_ext fun α j => congrArg (fun q => LB.Sec.f q j)
    ((hc' i α).trans (by simp only [map_sum, map_smul]) : famProj D.toPre F k α (s₂ i) =
      famProj D.toPre F k α (∑ l, g (c i l) • s l))
  have e₂ : ∀ i α, b' i α = ∑ l, c i l • b l α := fun i α => by
    refine sub_eq_zero.1 (sec_indep pb (DegPre.famε k) (c₁ α) (n := 1) (fun _ => 1) (fun a ha i => ?_)
      (fun _ => b' i α - ∑ l, c i l • b l α) ?_ 0)
    · rw [Fin.sum_univ_one, _root_.mul_one] at ha
      rw [Subsingleton.elim i 0]; exact hg (ha.trans (map_zero _).symm)
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [Fin.sum_univ_one, one_smul, map_sub, map_sum, sub_eq_zero]
        refine (eq_pullOver_of_secScal hM pb.w (c₁ α) (q₃ i α)).trans
          ((hc' i α).trans (Finset.sum_congr rfl fun l _ => ?_))
        rw [map_smulₛₗ]
        exact congrArg (fun q : FamTerm D.toPre F k α => g (c i l) • q)
          (eq_pullOver_of_secScal hM pb.w (c₁ α) (b₁ l α)).symm
  have e₃ : ∀ i, s₂' i = ∑ l, π (c i l) • s' l := fun i => fam_ext fun x j => by
    obtain ⟨mv, hmv⟩ := exists_moveMap (π := πB) (π' := famBase D'.toPre F') (fS := π) (ε := DegPre.famε k) hM
      D'.toPre.P.isLB hD.w_gen (c₂ x) (by rw [hπB]; exact hΘ₁.w)
    refine congrArg (fun q => LB.Sec.f q j) (?_ : famProj D'.toPre F' k x (s₂' i) =
      famProj D'.toPre F' k x (∑ l, π (c i l) • s' l))
    refine ((hmv _ _).1 (q₄ i x)).symm.trans ((congrArg mv (e₂ i (hD.xe x))).trans ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smulₛₗ, map_smul, (hmv _ _).1 (b₂ l x)]
    rfl
  refine ⟨n, F₀, f, f', s, s', c, ν, ν', hν, hν', fun i => (hf i).1, fun i => (hf i).2.2, hs, hs', ?_,
    fun i => ⟨e₁ i ▸ q₁ i, e₃ i ▸ q₂ i⟩⟩
  refine eq_top_iff.2 ((isExtension_famPull D'.toPre (FractionRing R') F' hG hk).span.ge.trans
    (Submodule.span_le.2 ?_))
  rintro _ ⟨v, rfl⟩
  have hv : v ∈ Submodule.span (FractionRing R') (Set.range F₁) := hspan ▸ Submodule.mem_top
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hv
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Submodule.sum_mem _ fun i _ => by
    rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.ThetaSpecialise

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar GlobalTheory.ThetaBaseChange
  GlobalTheory.ThetaSpecialise in
set_option maxHeartbeats 1600000 in
theorem qkToAkU_specialises : Laws → Laws2 → DVR.TwistBaseChangeStatement → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ (φ : R →+* R') (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∀ (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (U' : Unif I' D' A' G'), IsPullUnif φ hD bc U U' → IsSemiAbelian G → ∀ (S : Type) [CommRing S] [IsDomain S] [ValuationRing S] (σ : R →+* S) (F : Type) [Field F] [Algebra (FractionRing R) F] (ιF : S →+* F), Function.Injective ιF → ∀ (ρ : TF (R := R) F ⟶ (Over.mk (specOf σ))), ρ.left = specOf ιF → ∀ (F' : Type) [Field F'] [Algebra (FractionRing R') F'] (π : S →+* F'), IsLocalHom π → (∀ r : R, π (σ r) = algebraMap (FractionRing R') F' (algebraMap R' (FractionRing R') (φ r))) → ∀ (k : ℕ), 1 ≤ k → ∀ (gp : GtPt D.toPre (Over.mk (specOf σ))) (p₀ : QkPt D.toPre F k) (p₁ : QkPt D'.toPre F' k), GtPt.IsPullF F ρ.left gp p₀.g → p₁.y = hD.xe.symm p₀.y → p₁.g.b.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = specOf π ≫ gp.b.left → (∀ χ, Geo.Tor.PMaps hD.w (DegPre.gtφ D'.toPre F' p₁.g.b χ) (DegPre.gtφT D.toPre (Over.mk (specOf σ)) gp.b (hD.xe χ)) DegPre.gtε (p₁.g.s χ) (gp.s (hD.xe χ)) (specOf π)) → ∀ (xS : (Over.mk (specOf σ)) ⟶ G) (x : TFK (R := R) F ⟶ A.A) (x' : TFK (R := R') F' ⟶ A'.A), x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = ρ.left ≫ xS.left → x'.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = specOf π ≫ xS.left → QkToAkU U.toUnifPre F k p₀ x → QkToAkU U'.toUnifPre F' k p₁ x' := by
  intro hL _ hT R R' _ _ _ _ I I' hR _ φ D A G _ _ U G' _ _ bc hbc A' D' hD U' hU hsa S _ _ _ σ F _ _ g hg ρ hρ F' _ _
    π hπl hπ k hk gp p₀ p₁ h₁ h₂ h₃ h₄ xS x x' hx hx' H w' hw'
  have hG := hL.globalFns
  obtain ⟨wL, hwL, -, -, hlev⟩ := (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U U').1 hU
  obtain ⟨w, hw⟩ := U.ext
  obtain ⟨hx1, H⟩ := H w hw
  have gA := grp_generic U.toUnifPre
  have gΨ : IsGrpPullback G' G (specOf φ) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf φ))).congr (Category.id_comp _) rfl
  have gA' := (grp_generic U'.toUnifPre).comp gΨ
  have hτ : specOf g ≫ specOf σ = jFK (R := R) F ≫ jK R := (congrArg (· ≫ specOf σ) hρ).symm.trans (Over.w ρ)
  have hτ' : specOf π ≫ specOf σ = jFK (R := R') F' ≫ jK R' ≫ specOf φ := by
    rw [jFK, jK, specOf, specOf, specOf, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (RingHom.ext hπ : π.comp σ =
      ((algebraMap (FractionRing R') F').comp (algebraMap R' (FractionRing R'))).comp φ)
  have hx₁ : specOf g ≫ xS.left = x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) :=
    (congrArg (· ≫ xS.left) hρ).symm.trans hx.symm
  have hx₂ : specOf π ≫ xS.left = x'.left ≫ (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R')) ≫
      bc.hom.left ≫ pullback.fst G.hom (specOf φ) := hx'.symm.trans (by simp only [Category.assoc])
  have := U.separated
  have hxS : xS ^ k = 1 := pow_eq_one_of_injective hg ρ hρ xS (by
    have e : pushHom gA (TFK (R := R) F) x = ρ ≫ xS := Over.OverMorphism.ext hx
    exact (congrArg (· ^ k) e).symm.trans ((map_pow _ _ _).symm.trans ((congrArg _ hx1).trans (map_one _))))
  have hx'1 : x' ^ k = 1 := by
    let o : Over.mk (jFK (R := R') F' ≫ jK R' ≫ specOf φ) ⟶ Over.mk (specOf σ) := Over.homMk (specOf π) hτ'
    exact pow_eq_one_of_push rfl gA' (x := o ≫ xS) hx₂.symm
      ((map_pow (preHom o) xS k).symm.trans ((congrArg _ hxS).trans (map_one _)))
  refine ⟨hx'1, fun θ' hθ' => ?_⟩
  obtain ⟨θS, rfl⟩ := TorsionThetaLocal.exists_theta_of_pow_eq_one _ G U.LG U.cubG S (specOf σ) k xS hxS
  have n₁ : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]
  have n₂ : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U'.gen.inv_hom_id, Over.id_left]
  obtain ⟨u, hu, hu₁⟩ := exists_unpull hw _ n₁ rfl
  obtain ⟨u', hu', hu₁'⟩ := exists_unpull hw' _ n₂ rfl
  obtain ⟨v', T⟩ := exists_comp U'.LG.isLB wL u' ((isGen_iff _).1 hwL) hu' U.LG.isLB A'.isLB
  have hv' := (isGen_iff _).2 (T.pgen_comp U'.LG.isLB ((isGen_iff _).1 hwL) hu')
  obtain ⟨π₀, hπ₀⟩ : ∃ π₀ : (Over.mk (specOf σ) ⊗ G).left ⟶ Spec (CommRingCat.of S),
    π₀ = (fst (Over.mk (specOf σ)) G).left := ⟨_, rfl⟩
  obtain ⟨θ, mv, hθ, act, ps, ind⟩ := exists_side_map gA g hτ U.LG.isLB A.isLB u ((isGen_iff _).2 hu) k x θS hx₁
    π₀ hπ₀ (abelianBase A F) rfl
  obtain ⟨θ₀, mv', hθ₀, act', ps', -⟩ := exists_side_map gA' π hτ' U.LG.isLB A'.isLB v' hv' k x' θS hx₂
    π₀ hπ₀ (abelianBase A' F') rfl
  obtain ⟨aS, -, haS⟩ := exists_actMap U.LG.isLB θS (𝟙 _) π₀ (hπ₀.trans (Category.comp_id _).symm)
  obtain ⟨a', inj', ha'⟩ := exists_actMap A'.isLB θ₀ (𝟙 _) (abelianBase A' F') (Category.comp_id _).symm
  obtain ⟨e, he⟩ := exists_linearEquiv_expandsF hG U F hk w hw
  obtain ⟨e', he'⟩ := exists_linearEquiv_expandsF hG U' F' hk w' hw'
  obtain ⟨n, F₀, f, f', s, s', c, ν, ν', hν, hν', f₁, f₂, hs, hs', hspan, hc⟩ := exists_families hL hT hR φ D D' hD σ g hg
    ρ hρ π hπl hπ (hτ'.trans (Category.assoc _ _ _).symm) k hk gp p₀ p₁ h₁ h₂ h₃ h₄
  have := hsa.geomConnected
  have := hsa.quasiCompact
  choose τ hτE using fun i => exists_sec_expandsAt_of_integral_family R I hR D A G U.toUnifPre k
    (fun F => ((U.expand k hk).2 F).exists) (F₀ i) (f i) (f₁ i)
  have hΨ : ∀ _ : Fin 1, 𝟙 G'.left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) =
      (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ≫ 𝟙 G.left := fun _ =>
    (Category.id_comp _).trans (Category.comp_id _).symm
  choose τ' hτ₁ using fun i => (SecPull.existsUnique_secPull _ _ _ _ _ _ _ U.LG.isLB U'.LG.isLB wL hwL (Fin 1)
    (fun _ => 𝟙 G'.left) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)) _ hΨ (τ i)).exists
  have hτE' : ∀ i m, U'.ExpandsAt m k (τ' i) (f' i) := fun i m => by
    obtain ⟨h, hh⟩ := hlev m
    exact expandsAt_transport R R' I I' D D' A A' G G' U.toUnifPre U'.toUnifPre _ hD.w hD.xe _ wL hD.w_gen hwL
      (ExpGTrans.famφB_pull hD) m m k h hh (τ i) (τ' i) (f i) (f' i) (hτ₁ i) (f₂ i) (hτE i m)
  obtain ⟨b, hb⟩ : ∃ b : Fin n → SecOver π₀ (LPow G U.LG.L (k : ℤ) (Over.mk (specOf σ))),
      ∀ i, IsPull (φ₁ := fun _ : Fin 1 => (snd (Over.mk (specOf σ)) G).left) (snd (Over.mk (specOf σ)) G).left
        (b i) (τ i) := by
    have pw : (snd (Over.mk (specOf σ)) G).left ≫ G.hom = π₀ ≫ Spec.map (CommRingCat.ofHom σ) := by
      rw [hπ₀]; exact (Over.w (snd (Over.mk (specOf σ)) G)).trans (Over.w (fst (Over.mk (specOf σ)) G)).symm
    exact ⟨fun i => pullOver U.LG.L _ pw (fun _ => (Category.comp_id _).symm) (τ i),
      fun i => isPull_pullOver pw (fun _ => (Category.comp_id _).symm) (τ i)⟩
  have E : ∀ i, e (mv (b i)) = s i := fun i => (he _ _).1 (expandsF_of_integral U.toUnifPre F hu₁ (τ i) (f i) (hτE i)
    (s i) (fun α y J hJ => (hs i α).sval _ hJ) _ (ps _ _ (hb i)))
  have E' : ∀ i, e' (mv' (b i)) = s' i := fun i => (he' _ _).1 (expandsF_of_integral U'.toUnifPre F' hu₁' (τ' i) (f' i)
    (hτE' i) (s' i) (fun α y J hJ => (hs' i α).sval _ hJ) _ (PSec.cancel T U.LG.isLB
      (fun _ => (Category.comp_id _).symm) (hτ₁ i) (by rw [Category.assoc (snd (TFK (R := R') F') A'.A).left]; exact ps' _ _ (hb i))))
  obtain ⟨ν₀, hν₀, Hν⟩ := H θ hθ
  obtain ⟨l, -, hl⟩ := TorsionImage.exists_smul_of_phiVal p₀ ν ν₀ hν hν₀
  obtain ⟨Φ', hΦ'⟩ := phiFun_of_globalFns hG R' I' D' F' k hk p₁ ν' hν'
  have m : ∀ i, mv (aS (b i)) = l • mv (∑ j, c i j • b j) := fun i => e.injective (by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum, map_sum]
    simp only [map_smulₛₗ, RingHom.id_apply, E]
    exact hl _ _ _ ((phiRel_iff hG p₀ ν hν _ _).1 (hc i).1) ((phiRel_iff hG p₀ ν₀ hν₀ _ _).1
      (Hν _ _ _ _ ((he _ _).2 (E i)) ((he _ _).2 rfl) (act _ _ ((haS _ _).2 rfl)))))
  have m₁ : ∀ i, mv' (aS (b i)) = a' (mv' (b i)) := fun i => ((ha' _ _).1 (act' _ _ ((haS _ _).2 rfl))).symm
  have m₂ : ∀ i, e' (mv' (∑ j, c i j • b j)) = Φ' (s' i) := fun i => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    simp only [map_smulₛₗ, RingHom.id_apply, E']
    exact (hΦ' _ _).1 (hc i).2
  obtain ⟨l', hl', m'⟩ : ∃ l' : F', l' ≠ 0 ∧ ∀ i, e' (a' (mv' (b i))) = l' • Φ' (s' i) := by
    by_cases z : ∀ i, s' i = 0
    · refine ⟨1, one_ne_zero, fun i => ?_⟩
      rw [e'.map_eq_zero_iff.1 ((E' i).trans (z i)), z i, map_zero, map_zero, map_zero, smul_zero]
    · obtain ⟨i, hi⟩ := not_forall.1 z
      have := U.smooth
      obtain ⟨l', hl', m'⟩ := exists_ratio hg mv mv' (ind inferInstance) _ _ l m
        ⟨i, fun h => hi (by rw [← E', inj' ((m₁ i).symm.trans (h.trans (map_zero _).symm)), map_zero])⟩
        ⟨i, fun h => hi (eq_zero_of_phiVal p₁ ν' _ ((phiRel_iff hG p₁ ν' hν' _ _).1 ((hΦ' _ _).2
          (by rw [← m₂, h, map_zero]))))⟩
      exact ⟨l', hl', fun i => by rw [← m₁, m', map_smul, m₂]⟩
  have key : e'.toLinearMap ∘ₗ a' ∘ₗ e'.symm.toLinearMap = l' • Φ' := LinearMap.ext_on_range hspan fun i => by
    refine Eq.trans ?_ (m' i)
    rw [← E']
    exact congrArg (fun q => e' (a' q)) (e'.symm_apply_apply _)
  obtain ⟨d, hd, hd'⟩ := exists_act_ratio hG A'.isAb A'.isLB θ₀ θ' (hθ₀.trans hθ'.symm) (abelianBase A' F') rfl
  obtain ⟨ν₁, hν₁, Hν₁⟩ := ProdTorsion.exists_phiRel_smul hG p₁ ν' hν' (d * l') (mul_ne_zero hd hl')
  refine ⟨ν₁, hν₁, fun t t₂ q q₂ X X₂ hA => ?_⟩
  obtain rfl := (he' _ _).1 X
  obtain rfl := (he' _ _).1 X₂
  have y : e' t₂ = (d * l') • Φ' (e' t) := by
    refine (congrArg e' (hd' t _ t₂ ((ha' _ _).2 rfl) hA)).trans ((map_smul e' _ _).trans ?_)
    rw [mul_smul]
    exact congrArg (d • ·) ((congrArg (fun q => e' (a' q)) (e'.symm_apply_apply _)).symm.trans
      (LinearMap.congr_fun key (e' t)))
  rw [y]
  exact Hν₁ _ _ ((hΦ' _ _).2 rfl)

end GlobalTheory
