module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBasisAtOfIsLocBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondOperatorHermitianSideLevelPrime

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianUpMoveAtLevelPrimePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianUpMoveAtLevelPrimePlace
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt.UpMove

section G

variable {D : D7} {u : D.what₂.Word}


set_option maxHeartbeats 4000000 in
theorem upCl_of_crd (A : AtTTied u) (P : ∀ i hi, LvTied u A i hi) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT)
    (c : (D.mem u).C.cls i) (y : Formalism.L2.Herm.Ld D u i c)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hoff : ∀ q : HeightOneSpectrum (𝓞 D.host.E), q.asIdeal ≠ A.Pv v → q.asIdeal ≠ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) (A.Pv v) →
      Formalism.HermitianLatticesTheory.localization₂ q.asIdeal (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v c (prH A P i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ q.asIdeal (clsCrd D u i hi c))
    (h3 : Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v c (prH A P i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.L2.Forms.Ld D u i hi c))
    (h4 : Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat γ.1.1 (Formalism.L2.Forms.Ld D u i hi ((D.fm u).up i v c (prH A P i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.L2.Forms.Ld D u i hi c ⊔
          Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (toLd i hi c y).1}))
    (h5 : ∀ (x : ↥(Formalism.L2.Forms.Ld D u i hi ((D.fm u).up i v c (prH A P i v c y))))
        (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Formalism.L2.Forms.Ld D u i hi c),
        (D.fm u).fv i v _ ((P i hi).pr v _ x) = (D.fm u).fv i v c ((P i hi).pr v c ⟨_, hx⟩))
    (h6 : ∀ v', v' ≠ v → ∀ (z : ↥(Formalism.L2.Forms.Ld D u i hi c))
        (z' : ↥(Formalism.L2.Forms.Ld D u i hi ((D.fm u).up i v c (prH A P i v c y)))), z.1 = γ.1.1 *ᵥ z'.1 →
        (D.fm u).fv i v' _ ((P i hi).pr v' _ z') = (D.fm u).fv i v' c ((P i hi).pr v' c z)) :
    UpCl A P i v c y (gx i hi γ) := by

  let crdL := ((crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E))
  have inj : Function.Injective crdL := (crdN D i hi).injective
  have eCls : ∀ c' : (D.mem u).C.cls i, (D.clsLat u i c').map crdL = clsCrd D u i hi c' := fun _ => rfl
  have eLd : ∀ c' : (D.mem u).C.cls i, (Formalism.L2.Herm.Ld D u i c').map crdL = Formalism.L2.Forms.Ld D u i hi c' := fun c' =>
    dual_co D.sp.cm (D.sp.X i) (rankN D i hi) (D.clsLat u i c')
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q hq hP hc
    haveI := hq.isPrime
    let q' : HeightOneSpectrum (𝓞 D.host.E) :=
      ⟨q, hq.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hq (RingOfIntegers.not_isField D.host.E)⟩
    apply Submodule.map_injective_of_injective inj
    rw [localization_map₂ hi, localization_map₂ hi, lc_gmap, eCls, eCls]
    exact hoff q' hP hc
  · apply Submodule.map_injective_of_injective inj
    rw [localization_map₂ hi, localization_map₂ hi, lc_gmap, eCls, eLd]
    exact h3
  · apply Submodule.map_injective_of_injective inj
    rw [localization_map₂ hi, localization_map₂ hi, lc_gmap, eLd, Submodule.map_sup, eLd, Submodule.map_span, Set.image_singleton]
    convert h4 using 4
    simp [crdL, toLd]
  · intro z hz
    rw [prH_eq A P hi v _ z, prH_eq A P hi v c ⟨_, hz⟩]
    have key : crdN D i hi (((D.mem u).A.T : D.host.E) • (gx i hi γ).1 (z : (D.sp.X i).V)) =
        (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ (toLd i hi _ z).1) := by
      rw [map_smul, crdN_gx]
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
      rfl
    have hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ (toLd i hi _ z).1) ∈ Formalism.L2.Forms.Ld D u i hi c :=
      key ▸ (mem_Ld i hi c _).1 hz
    have e : toLd i hi c ⟨_, hz⟩ = ⟨_, hx⟩ := Subtype.ext key
    rw [e]
    exact h5 _ hx
  · intro v' hv' z hz
    rw [prH_eq A P hi v' _ z, prH_eq A P hi v' c ⟨_, hz⟩]
    exact h6 v' hv' (toLd i hi c ⟨_, hz⟩) (toLd i hi _ z) (crdN_gx i hi γ _)

end G

section S

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}


set_option maxHeartbeats 4000000 in
theorem crd_up (T : FormsTiedSym D u Ch chOf) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT)
    (c : (D.mem u).C.cls i) (y : Formalism.L2.Herm.Ld D u i c)
    (hf : (D.fm u).fv i v c (prH T.atT T.lv i v c y) = 1)
    (hC : ∀ (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) (c' : (D.mem u).C.cls i) (z : Formalism.L2.Forms.Ld D u i (le_of_succ_m h2) c')
      (z' : LdG D i (le_of_succ_m h2) (clsCrd D u i (le_of_succ_m h2) c')), z'.1 = z.1 →
        (T.lvC i h1 h2).pr v c' z' = (T.lv i (le_of_succ_m h2)).pr v c' z) :
    ∃ γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi),
      AdC T i hi c ((D.fm u).up i v c (prH T.atT T.lv i v c y)) γ.1 (T.atT.eV v).1 ∧
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v c (prH T.atT T.lv i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Formalism.L2.Forms.Ld D u i hi c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Formalism.L2.Forms.Ld D u i hi ((D.fm u).up i v c (prH T.atT T.lv i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Formalism.L2.Forms.Ld D u i hi c ⊔
          Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (toLd i hi c y).1}) ∧
      ∀ (x : ↥(Formalism.L2.Forms.Ld D u i hi ((D.fm u).up i v c (prH T.atT T.lv i v c y))))
        (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Formalism.L2.Forms.Ld D u i hi c),
        (D.fm u).fv i v _ ((T.lv i hi).pr v _ x) = (D.fm u).fv i v c ((T.lv i hi).pr v c ⟨_, hx⟩) := by
  have e1 : (T.lv i hi).pr v c (toLd i hi c y) = prH T.atT T.lv i v c y := (prH_eq T.atT T.lv hi v c y).symm
  rcases (show (i = 0 ∨ i = D.R.m) ∨ (1 ≤ i ∧ i + 1 ≤ D.R.m) by omega) with h | ⟨h1, h2⟩
  · have hz : (D.fm u).fv i v c ((T.lv i hi).pr v c (toLd i hi c y)) = 1 := by rw [e1]; exact hf
    have H0 := T.upN i hi h v c (toLd i hi c y) hz
    generalize (T.lv i hi).pr v c (toLd i hi c y) = t at H0 e1
    subst e1
    obtain ⟨γ, η, κ, hη, hy, h3, h4, h5, -⟩ := H0
    refine ⟨γ, ⟨fun h' => ⟨κ.1, κ.2, η.1, η.2, hη, hy⟩, fun h1 h2 => absurd h (by omega)⟩, h3, h4, h5⟩
  · have hl := le_of_succ_m h2
    have e0 : (T.lvC i h1 h2).pr v c (toLd i hi c y) = prH T.atT T.lv i v c y :=
      (hC h1 h2 c (toLd i hi c y) (toLd i hi c y) rfl).trans e1
    have hz : (D.fm u).fv i v c ((T.lvC i h1 h2).pr v c (toLd i hi c y)) = 1 := by rw [e0]; exact hf
    have H0 := T.upC i h1 h2 v (chOf i c) ⟨c, rfl⟩ (toLd i hi c y) hz
    generalize (T.lvC i h1 h2).pr v c (toLd i hi c y) = t at H0 e0
    subst e0
    obtain ⟨hβ, γ, η, κ, hη, hy, h3, h4, h5, -⟩ := H0
    refine ⟨γ, ⟨fun h => absurd h (by omega), fun h1' h2' => ⟨hβ, κ.1, κ.2, η.1, η.2, hη, hy⟩⟩, h3, h4, fun x hx => ?_⟩
    have := h5 x hx
    rwa [hC h1 h2 _ x x rfl, hC h1 h2 c ⟨_, hx⟩ ⟨_, hx⟩ rfl] at this

end S

end GlobalTheory.Mem.Col2.HAt.UpMove


open GlobalTheory.Mem.Col2.HAt.UpMove in
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Mem.Col2.HAt.UpMove.up_move : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i v (c : ((I.rec7 l Z).mem u).C.cls i) (y : Formalism.L2.Herm.Ld (I.rec7 l Z) u i c), ∃ γ, i ≤ (I.rec7 l Z).R.m → ((I.rec7 l Z).fm u).fv i v c (prH (F u).atT (F u).lv i v c y) = 1 → UpCl (F u).atT (F u).lv i v c y γ ∧ AdOf H u i c (((I.rec7 l Z).fm u).up i v c (prH (F u).atT (F u).lv i v c y)) γ v := by
  intro B X I hOk hPins l Z H F hStd hCar u i v c y
  by_cases hi : i ≤ (I.rec7 l Z).R.m
  swap
  · exact ⟨1, fun h => absurd h hi⟩
  by_cases hf : ((I.rec7 l Z).fm u).fv i v c (prH (F u).atT (F u).lv i v c y) = 1
  swap
  · exact ⟨1, fun _ h => absurd h hf⟩
  obtain ⟨γ, hAd, h3, h4, h5⟩ := crd_up (F u) i hi v c y hf
    (fun h1 h2 c' z z' e => (GlobalTheory.T.middleStep_oneLevel_projection_eq_chart_projection I hOk hPins l Z H F hStd hCar u i h1 h2 v c').1 z z' e)
  refine ⟨gx i hi γ, fun _ _ => ⟨upCl_of_crd (F u).atT (F u).lv i hi v c y γ ?_ h3 h4 h5 ?_,
    GlobalTheory.T.adelic_relation_classes_coordinates I hOk hPins l Z H F hStd hCar u i hi v c _ γ hAd⟩⟩
  · intro q hP hc
    refine GlobalTheory.T.adelic_conjugate_character_standard_forms I hOk hPins l Z H F hStd hCar u i hi v c _ γ.1 hAd q fun hq => ?_
    rcases GlobalTheory.T.host_primes_over_level_place I hOk hPins l Z H F hStd hCar u v q hq with h | h
    · exact hP h
    · exact hc h
  · intro v' hv' z z' e
    exact GlobalTheory.T.levelFunctional_eq_of_classes_related_at_place I hOk hPins l Z H F hStd hCar u i hi v v' c _ γ.1 hAd hv' z z' e
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianUpMoveAtLevelPrimePlaceStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianUpMove_at_levelPrime_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i v (c : ((I.rec7 l Z).mem u).C.cls i) (y : Formalism.L2.Herm.Ld (I.rec7 l Z) u i c), ∃ γ, i ≤ (I.rec7 l Z).R.m → ((I.rec7 l Z).fm u).fv i v c (prH (F u).atT (F u).lv i v c y) = 1 → UpCl (F u).atT (F u).lv i v c y γ ∧ AdOf H u i c (((I.rec7 l Z).fm u).up i v c (prH (F u).atT (F u).lv i v c y)) γ v := by
  first | exact @GlobalTheory.Mem.Col2.HAt.UpMove.up_move | exact GlobalTheory.Mem.Col2.HAt.UpMove.up_move | (intros; apply GlobalTheory.Mem.Col2.HAt.UpMove.up_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHermitianDownMoveAtLevelPrimePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHermitianDownMoveAtLevelPrimePlace
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt


set_option maxHeartbeats 4000000 in
theorem dnCl_of_tie {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z))
    (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u))
    (hS : ∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) (hC : CarH H F) (u) (i : ℕ) (hi : i ≤ (I.rec7 l Z).R.m) (v)
    (c : ((I.rec7 l Z).mem u).C.cls i)
    (g : Module.Dual (((I.rec7 l Z).mem u).A.Fv v) (((I.rec7 l Z).fm u).lk i v c))
    (γ₀ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi))
    (hAd : AdC (F u) i hi c (((I.rec7 l Z).fm u).dn i v c g) γ₀.1 ((F u).atT.eV v).1)
    (hloc : Formalism.HermitianLatticesTheory.localization₂ ((F u).atT.Pv v) (Formalism.L2.Forms.mulLat γ₀.1.1
        (Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi (((I.rec7 l Z).fm u).dn i v c g))) =
      Formalism.HermitianLatticesTheory.localization₂ ((F u).atT.Pv v) (clsCrd (I.rec7 l Z) u i hi c))
    (hfv : ∀ (x : Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi (((I.rec7 l Z).fm u).dn i v c g))
      (hx : γ₀.1.1 *ᵥ x.1 ∈ Formalism.L2.Forms.Lk (F u).atT i hi v c),
      ((I.rec7 l Z).fm u).fv i v _ (((F u).lv i hi).pr v _ x) = g (((F u).lv i hi).prk v c ⟨_, hx⟩)) :
    DnCl (F u).atT (F u).lv i v c g (gx i hi γ₀) ∧
      AdOf H u i c (((I.rec7 l Z).fm u).dn i v c g) (gx i hi γ₀) v := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, GlobalTheory.T.adelic_relation_classes_coordinates I hOk hP l Z H F hS hC u i hi v c _ γ₀ hAd⟩
  · intro q hq hq1 hq2
    haveI := hq.isPrime
    let Q : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E) :=
      ⟨q, hq.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hq (RingOfIntegers.not_isField _)⟩
    have hu : Q.under (𝓞 (I.rec7 l Z).host.F) ≠ ((F u).atT.eV v).1 := fun h =>
      (GlobalTheory.T.host_primes_over_level_place I hOk hP l Z H F hS hC u v Q h).elim hq1 hq2
    have h1 := GlobalTheory.T.adelic_conjugate_character_standard_forms I hOk hP l Z H F hS hC u i hi v c _ γ₀.1 hAd Q hu
    refine Submodule.map_injective_of_injective
      (f := ((crdN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi : ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X i).V →ₗ[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E] (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N i) → (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)).restrictScalars (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)))
      (crdN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi).injective ?_
    rw [localization_map₂ hi, localization_map₂ hi, lc_gmap]
    exact h1
  · have e : lc ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) (Formalism.L2.Herm.Ld (I.rec7 l Z) u i (((I.rec7 l Z).fm u).dn i v c g)) =
        Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi (((I.rec7 l Z).fm u).dn i v c g) :=
      dual_co (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) ((I.rec7 l Z).clsLat u i _)
    refine Submodule.map_injective_of_injective
      (f := ((crdN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi : ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X i).V →ₗ[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E] (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N i) → (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)).restrictScalars (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)))
      (crdN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi).injective ?_
    rw [localization_map₂ hi, localization_map₂ hi, lc_gmap]
    refine Eq.trans ?_ hloc
    exact congrArg (fun L => Formalism.HermitianLatticesTheory.localization₂ ((F u).atT.Pv v) (Formalism.L2.Forms.mulLat γ₀.1.1 L)) e
  · intro z hz
    rw [prH_eq _ _ hi, prkH_eq _ _ hi]
    have hx : γ₀.1.1 *ᵥ (toLd i hi _ z).1 ∈ Formalism.L2.Forms.Lk (F u).atT i hi v c := by
      rw [show (toLd i hi _ z).1 = crdN (I.rec7 l Z) i hi z.1 from rfl, ← crdN_gx]
      exact (mem_Lk (F u).atT i hi v c _).1 hz
    rw [hfv _ hx]
    exact congrArg g (congrArg _ (Subtype.ext (crdN_gx i hi γ₀ z.1).symm))
  · intro v' hv' z hz
    rw [prH_eq _ _ hi, prH_eq _ _ hi]
    exact GlobalTheory.T.levelFunctional_eq_of_classes_related_at_place I hOk hP l Z H F hS hC u i hi v v' c _ γ₀.1 hAd hv' (toLd i hi c ⟨_, hz⟩) (toLd i hi _ z)
      (crdN_gx i hi γ₀ z.1)

end GlobalTheory.Mem.Col2.HAt


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Mem.Col2.HAt.dn_move_exists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i v (c : ((I.rec7 l Z).mem u).C.cls i) (g : Module.Dual (((I.rec7 l Z).mem u).A.Fv v) (((I.rec7 l Z).fm u).lk i v c)), ∃ γ, i ≤ (I.rec7 l Z).R.m → g ≠ 0 → DnCl (F u).atT (F u).lv i v c g γ ∧ AdOf H u i c (((I.rec7 l Z).fm u).dn i v c g) γ v := by
  intro B X I hOk hP l Z H F hS hC u i v c g
  by_cases hcase : i ≤ (I.rec7 l Z).R.m ∧ g ≠ 0
  · obtain ⟨hi, hg⟩ := hcase
    by_cases hN : i = 0 ∨ i = (I.rec7 l Z).R.m
    · obtain ⟨γ, η, κ, hη, hy, hloc, hfv, -⟩ := (F u).dnN i hi hN v c g hg
      refine ⟨gx i hi γ, fun _ _ => dnCl_of_tie I hOk hP l Z H F hS hC u i hi v c g γ
        ⟨fun _ => ⟨κ.1, κ.2, η.1, η.2, hη, hy⟩, fun h1 h2 => absurd hN (by omega)⟩ hloc hfv⟩
    · have h1 : 1 ≤ i := by omega
      have h2 : i + 1 ≤ (I.rec7 l Z).R.m := by omega
      obtain ⟨hβ, γ, η, κ, hη, hy, hloc, hfv, -⟩ := (F u).dnC i h1 h2 v (H.chOf u i c) ⟨c, rfl⟩ g hg
      refine ⟨gx i hi γ, fun _ _ => dnCl_of_tie I hOk hP l Z H F hS hC u i hi v c g γ
        ⟨fun h => absurd h hN, fun _ _ => ⟨hβ, κ.1, κ.2, η.1, η.2, hη, hy⟩⟩ hloc ?_⟩
      intro x hx
      rw [← (GlobalTheory.T.middleStep_oneLevel_projection_eq_chart_projection I hOk hP l Z H F hS hC u i h1 h2 v (((I.rec7 l Z).fm u).dn i v c g)).1 x x rfl,
        ← (GlobalTheory.T.middleStep_oneLevel_projection_eq_chart_projection I hOk hP l Z H F hS hC u i h1 h2 v c).2 ⟨_, hx⟩ ⟨_, hx⟩ rfl]
      exact hfv x hx
  · exact ⟨1, fun hi hg => absurd ⟨hi, hg⟩ hcase⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHermitianDownMoveAtLevelPrimePlaceStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitianDownMove_at_levelPrime_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i v (c : ((I.rec7 l Z).mem u).C.cls i) (g : Module.Dual (((I.rec7 l Z).mem u).A.Fv v) (((I.rec7 l Z).fm u).lk i v c)), ∃ γ, i ≤ (I.rec7 l Z).R.m → g ≠ 0 → DnCl (F u).atT (F u).lv i v c g γ ∧ AdOf H u i c (((I.rec7 l Z).fm u).dn i v c g) γ v := by
  first | exact @GlobalTheory.Mem.Col2.HAt.dn_move_exists | exact GlobalTheory.Mem.Col2.HAt.dn_move_exists | (intros; apply GlobalTheory.Mem.Col2.HAt.dn_move_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualModClassLatticeEquivQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualModClassLatticeEquivQuotient
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.HAt.Disc

section Gen

variable {R V W : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

def quotMapEquiv (e : V ≃ₗ[R] W) (A L : Submodule R V) (A' L' : Submodule R W) (hA : A.map (e : V →ₗ[R] W) = A')
    (hL : L.map (e : V →ₗ[R] W) = L') : (A ⧸ L.comap A.subtype) ≃ₗ[R] (A' ⧸ L'.comap A'.subtype) := by
  subst hA hL
  refine Submodule.Quotient.equiv _ _ (e.submoduleMap A) ?_
  ext ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨z, hz, hze⟩
    have : (z : V) = x := e.injective (congrArg Subtype.val hze)
    exact ⟨x, this ▸ hz, rfl⟩
  · rintro ⟨x', hx', hxe⟩
    have : x' = x := e.injective hxe
    subst this
    exact ⟨⟨x', hx⟩, hx', rfl⟩

end Gen

end GlobalTheory.Mem.Col2.HAt.Disc

namespace GlobalTheory.Mem.Col2.HAt.Disc

theorem span_pi_eq {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) :
    Ideal.span {Pr.piT u} = ⨅ P : Pr.vT u, P.1.asIdeal := by
  refine le_antisymm ?_ fun r hr => ?_
  · refine le_iInf fun P => ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact decoFin_mem_of_mem_divs P.2
  · exact Ideal.mem_span_singleton.2 (piT_dvd_of_mem hX hPr u r fun P => Ideal.mem_iInf.1 hr P)

theorem span_conj_pi_eq {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) :
    Ideal.span {X.conjO (Pr.piT u)} = ⨅ P : Pr.vT u, (conjPrime₂ P.1).asIdeal := by
  refine le_antisymm ?_ fun r hr => ?_
  · refine le_iInf fun P => ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show cO X.E (X.conjO (Pr.piT u)) ∈ P.1.asIdeal
    rw [show cO X.E (X.conjO (Pr.piT u)) = Pr.piT u from cO_cO _]
    exact decoFin_mem_of_mem_divs P.2
  · obtain ⟨s, hs⟩ := piT_dvd_of_mem hX hPr u (cO X.E r) fun P => Ideal.mem_iInf.1 hr P
    refine Ideal.mem_span_singleton.2 ⟨cO X.E s, ?_⟩
    have := congrArg (cO X.E) hs
    rw [cO_cO, map_mul] at this
    exact this

end GlobalTheory.Mem.Col2.HAt.Disc

namespace GlobalTheory.Mem.Col2.HAt.Disc

theorem span_T_eq {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (u : Pr.Word) :
    Ideal.span {((Pr.T u : ℕ) : 𝓞 X.E)} = Ideal.span {Pr.piT u} ⊓ Ideal.span {X.conjO (Pr.piT u)} := by
  rw [← hPr.piT_norm u, ← Ideal.span_singleton_mul_span_singleton]
  exact Ideal.mul_eq_inf_of_coprime ((Ideal.isCoprime_span_singleton_iff _ _).2 (hPr.piT_cop u)).sup_eq

theorem quotT_equiv {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) :
    Nonempty ((𝓞 X.E ⧸ Ideal.span {((Pr.T u : ℕ) : 𝓞 X.E)}) ≃ₗ[𝓞 X.E]
      ((∀ P : Pr.vT u, 𝓞 X.E ⧸ P.1.asIdeal) × (∀ P : Pr.vT u, 𝓞 X.E ⧸ (conjPrime₂ P.1).asIdeal))) := by
  have hco : IsCoprime (Ideal.span {Pr.piT u}) (Ideal.span {X.conjO (Pr.piT u)}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).2 (hPr.piT_cop u)
  have hp1 : Pairwise (Function.onFun IsCoprime fun P : Pr.vT u => P.1.asIdeal) := fun P Q hne => by
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne P.1.isMaximal Q.1.isMaximal fun h => hne (Subtype.ext (HeightOneSpectrum.ext h))
  have hp2 : Pairwise (Function.onFun IsCoprime fun P : Pr.vT u => (conjPrime₂ P.1).asIdeal) := fun P Q hne => by
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    refine Ideal.IsMaximal.coprime_of_ne (conjPrime₂ P.1).isMaximal (conjPrime₂ Q.1).isMaximal fun h => hne (Subtype.ext ?_)
    ext x
    have h2 := congrArg (fun J : Ideal (𝓞 X.E) => cO X.E x ∈ J) h
    simp only [conjPrime₂, Ideal.mem_comap, cO_cO] at h2
    exact Iff.of_eq h2
  let φ : (𝓞 X.E ⧸ Ideal.span {((Pr.T u : ℕ) : 𝓞 X.E)}) ≃+*
      ((∀ P : Pr.vT u, 𝓞 X.E ⧸ P.1.asIdeal) × (∀ P : Pr.vT u, 𝓞 X.E ⧸ (conjPrime₂ P.1).asIdeal)) :=
    (Ideal.quotEquivOfEq (span_T_eq hPr u)).trans ((Ideal.quotientInfEquivQuotientProd _ _ hco).trans
      (RingEquiv.prodCongr
        ((Ideal.quotEquivOfEq (span_pi_eq hX hPr u)).trans (Ideal.quotientInfRingEquivPiQuotient _ hp1))
        ((Ideal.quotEquivOfEq (span_conj_pi_eq hX hPr u)).trans (Ideal.quotientInfRingEquivPiQuotient _ hp2))))
  exact ⟨(AlgEquiv.ofRingEquiv (f := φ) fun a => rfl).toLinearEquiv⟩

end GlobalTheory.Mem.Col2.HAt.Disc


open GlobalTheory.Mem.Col2.HAt.Disc in
theorem GlobalTheory.Mem.Col2.TC.disc_cl : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u, DiscCl (D := I.rec7 l Z) (u := u) := by
  intro B X I hI hP l Z H F _ _ u i hi c
  obtain ⟨hG, -, hc⟩ := (spaces_in_coordinates I hI hP l Z).2.2.2 i hi
  have hL : latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c) = ((I.stp u I.mu0 i).rep c).1.1.deco.1.L := (hc u I.mu0).1 c
  have hD : lc ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) (Formalism.L2.Herm.Ld (I.rec7 l Z) u i c) =
      ((I.stp u I.mu0 i).rep c).1.1.deco.1.Lsh := by
    refine (dual_co (I.rec7 l Z).sp.cm _ (rankN (I.rec7 l Z) i hi) _).trans ?_
    have h1 := BwLat.dualL_std (E := B.host.E) (sigD (I.rec7 l Z)).toRingHom (fun x => rfl) ((I.stp u I.mu0 i).rep c).1.1.deco.1.L
    exact (congrArg₂ (dualL _) hG hL).trans h1
  have hc' : ∀ P Q : (B.primes X).vT u, Q.1 ≠ conjPrime₂ P.1 := fun P Q => (moveHyp_of_ok l.pr u P).st Q
  obtain ⟨e1⟩ := ((I.stp u I.mu0 i).rep c).1.1.deco.2.Lsh_quot_L hc'
  obtain ⟨e2⟩ := quotT_equiv (FieldsLaws.fields_satisfy_definite_laws B).1.ok l.pr u
  exact ⟨(quotMapEquiv ((crdN (I.rec7 l Z) i hi).restrictScalars (𝓞 (I.rec7 l Z).host.E)) _ _ _ _ hD hL) ≪≫ₗ e1 ≪≫ₗ e2.symm⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualModClassLatticeEquivQuotientStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_mod_class_lattice_equiv_quotient : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u, DiscCl (D := I.rec7 l Z) (u := u) := by
  first | exact @GlobalTheory.Mem.Col2.TC.disc_cl | exact GlobalTheory.Mem.Col2.TC.disc_cl | (intros; apply GlobalTheory.Mem.Col2.TC.disc_cl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianSideClassesEqFormClasses
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianSideClassesEqFormClasses
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.HAt

section GenP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open scoped TensorProduct

theorem val_nat_lt_one (v : HeightOneSpectrum (𝓞 F)) (g : ℕ) (h : (g : 𝓞 F) ∈ v.asIdeal) :
    Valued.v (g : v.adicCompletion F) < 1 := by
  have h1 : v.valuation F (algebraMap (𝓞 F) F (g : 𝓞 F)) < 1 := (v.valuation_lt_one_iff_mem _).2 h
  have h2 : ((g : v.adicCompletion F)) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (g : 𝓞 F)) := by
    simp only [map_natCast]
  rw [h2]
  exact lt_of_eq_of_lt (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap (𝓞 F) F (g : 𝓞 F))) h1

theorem redM_eq_one {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (g : v.adicCompletion F) (hg : Valued.v g < 1)
    (X W : Matrix (Fin n) (Fin n) (v.adicCompletion F))
    (hW : ∀ a b, W a b ∈ v.adicCompletionIntegers F)
    (hX : ∀ a b, X a b = (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b + g * W a b) :
    redM F v X = 1 := by
  have hgi : g ∈ v.adicCompletionIntegers F := le_of_lt hg
  have h1 : ∀ a b, (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b ∈ v.adicCompletionIntegers F := by
    intro a b
    by_cases e : a = b
    · subst e
      rw [Matrix.one_apply_eq]
      exact one_mem _
    · rw [Matrix.one_apply_ne e]
      exact zero_mem _
  ext a b
  have hm : X a b ∈ v.adicCompletionIntegers F := by
    rw [hX]
    exact add_mem (h1 a b) (mul_mem hgi (hW a b))
  have hz : IsLocalRing.residue (v.adicCompletionIntegers F) ⟨g, hgi⟩ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := (Valuation.integer.integers (Valued.v (R := v.adicCompletion F))).isUnit_iff_valuation_eq_one.1 hu
    exact absurd this (ne_of_lt hg)
  have e : (⟨X a b, hm⟩ : v.adicCompletionIntegers F) =
      ⟨(1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b, h1 a b⟩ + ⟨g, hgi⟩ * ⟨W a b, hW a b⟩ := by
    exact Subtype.ext ((hX a b).trans rfl)
  simp only [redM]
  rw [dite_eq_left hm, e, map_add (f := _), map_mul, hz, zero_mul, add_zero]
  by_cases ab : a = b
  · subst ab
    simp only [Matrix.one_apply_eq]
    exact map_one _
  · simp only [Matrix.one_apply_ne ab]
    exact map_zero _

theorem mem_Uloc_of_princ {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 F))} {gp : Fin 2 → ℕ} (S : StepLevel F E σ J T f bad) (G : GLoc F E σ gp)
    {H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v))}
    {lam : ∀ a v h, H a v h →* ℂˣ} (V : GLevH S G H lam)
    (hLb : ∀ b : Fin n, (Pi.single b 1 : Fin n → E) ∈ S.Lb)
    (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) (hfr : V.fr i v h = 1)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hx : x ∈ levelVL σ J v S.Lb)
    (hc : ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb,
      ∃ z ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb,
        (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = (gp i : E ⊗[F] v.adicCompletion F) • z) :
    x ∈ S.Uloc v := by
  have hint : ∀ z ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb, ∀ a,
      G.phi i v h (z a) ∈ v.adicCompletionIntegers F := by
    intro z hz a
    have := (V.fr_lat i v h (fun b => G.phi i v h (z b))).1 ⟨z, hz, fun _ => rfl⟩ a
    rw [hfr] at this
    simpa using this
  have hcol : ∀ b : Fin n, ∃ z ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb, ∀ a,
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b =
        (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b + (gp i : E ⊗[F] v.adicCompletion F) * z a := by
    intro b
    have e1 : (fun j => inclE (F := F) (v.adicCompletion F) ((Pi.single b 1 : Fin n → E) j)) =
        (Pi.single b 1 : Fin n → E ⊗[F] v.adicCompletion F) := by
      funext j
      by_cases e : j = b
      · subst e
        simp
      · simp [e]
    have hb : (Pi.single b 1 : Fin n → E ⊗[F] v.adicCompletion F) ∈
        latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
      rw [← e1]
      exact Submodule.subset_span ⟨_, hLb b, rfl⟩
    obtain ⟨z, hz, e⟩ := hc _ hb
    refine ⟨z, hz, fun a => ?_⟩
    have := congrFun e a
    rw [Matrix.mulVec_single_one] at this
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply] at this
    rw [← this]
    by_cases ab : a = b
    · subst ab
      simp
    · simp [ab]
  choose Z hZ hZe using hcol
  refine (V.mem i v h x hx).2 ⟨1, one_mem _, ?_⟩
  have key : redM F v (G.mat i v h (V.fr i v h) x) = 1 := by
    rw [hfr]
    refine redM_eq_one v (gp i : v.adicCompletion F) (val_nat_lt_one v (gp i) h) _
      (fun a b => G.phi i v h (Z b a)) (fun a b => hint _ (hZ b) a) fun a b => ?_
    have e2 : G.mat i v h 1 x a b = G.phi i v h ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b) := by
      simp [GLoc.mat, bc]
    rw [e2, hZe b a, map_add (f := _), map_mul, map_natCast]
    congr 1
    by_cases ab : a = b
    · subst ab
      simp
    · simp [ab]
  rw [key]
  rfl

end GenP

section Tr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

open scoped TensorProduct

theorem reGL_rfl_apply {n : ℕ} (R : Type) [CommRing R] (g : GL (Fin n) R) : reGL rfl R g = g := by
  ext a b
  simp [reGL]

theorem reGL_rfl_hom {n : ℕ} (R : Type) [CommRing R] :
    (reGL (rfl : n = n) R).toMonoidHom = MonoidHom.id _ := by
  ext1 g
  exact reGL_rfl_apply R g

theorem reL_rfl {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) : reL rfl L = L := by
  ext x
  simp [reL, reV]

theorem co_rfl (S : HSpace E) : co S rfl = Formalism.L2.Herm.crd S :=
  LinearEquiv.ext fun x => funext fun j => by simp [co, Formalism.L2.Herm.crd]

theorem tie_of_forms (hc : CMData F E) (S : HSpace E) {n : ℕ} (h : S.rank = n) (hO : Crd.Ortho S)
    {σ : E →ₐ[F] E} (hσ : σ = hc.sig) {J : Matrix (Fin n) (Fin n) E} (hJ : J = S.gram.reindex (finCongr h) (finCongr h))
    {f : ℕ} {gp : Fin 2 → ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (hbad : bad = {v | (gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal})
    (St : StepLevel F E σ J 1 f bad) (G : GLoc F E σ gp)
    {H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v))}
    {lam : ∀ a v h, H a v h →* ℂˣ} (V : GLevH St G H lam) (hfr : ∀ a v h, V.fr a v h = 1)
    (hLb : ∀ x, x ∈ St.Lb ↔ ∀ j, x j ∈ (algebraMap (𝓞 E) E).range)
    {cls : Type} {stab : cls → Type} [∀ c, Group (stab c)]
    (y : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls St)))
    (lat : cls → Submodule (𝓞 E) (Fin n → E))
    (y_lat : ∀ c (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F),
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (lat c) ↔
      ((y c).1⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) St.Lb)
    (stabI : ∀ c, stab c →* UJ (σ : E →+* E) J)
    (stabI_inj : ∀ c, Function.Injective (stabI c))
    (stabI_range : ∀ c (γ : UJ (σ : E →+* E) J), γ ∈ (stabI c).range ↔
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ St.U.map (MulAut.conj (y c).1).toMonoidHom) :
    ∃ (lattice₂ : cls → Submodule (𝓞 E) S.V) (levP : Formalism.L2.Herm.StepLevel0 hc S gp (Formalism.L2.Herm.crdLat S S.L0))
      (clsP : Formalism.L2.Herm.ClassTie hc S (Formalism.L2.Herm.crdLat S S.L0) levP.U stab lattice₂),
      SameCar h (Formalism.L2.Herm.crdLat S S.L0) St.Lb levP.Uloc St.Uloc levP.U St.U
        (fun c => (clsP.y c).1) (fun c => (y c).1) (fun c s => (clsP.stabI c s).1) (fun c s => (stabI c s).1) ∧
      ∀ c, lat c = (lattice₂ c).map (((co S h : S.V ≃ₗ[E] (Fin n → E)) : S.V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) := by
  subst h
  subst hσ
  obtain rfl : J = S.gram := hJ.trans (by ext a b; simp)
  subst hbad
  have hL : St.Lb = Formalism.L2.Herm.crdLat S S.L0 := by
    ext x
    rw [hLb x, ← hO.mem_standardLattice_iff_integral_coords rfl x]
    unfold Formalism.L2.Herm.crdLat
    rw [show Crd.co S rfl = Formalism.L2.Herm.crd S from co_rfl S]
  have hone : ∀ v : HeightOneSpectrum (𝓞 F), ((1 : ℕ) : 𝓞 F) ∉ v.asIdeal := fun v hv =>
    v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using hv))
  have hs : ∀ b : Fin S.rank, (Pi.single b 1 : Fin S.rank → E) ∈ St.Lb := by
    intro b
    refine (hLb _).2 fun j => ?_
    by_cases e : j = b
    · subst e
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [e]⟩
  refine ⟨fun c => (lat c).map (((Formalism.L2.Herm.crd S).symm : (Fin S.rank → E) →ₗ[E] S.V).restrictScalars (𝓞 E)),
    { Uloc := St.Uloc
      Uloc_lev := fun v => hL ▸ St.Uloc_lev v
      Uloc_hyp := fun v h0 h1 => ?_
      Uloc_g := fun i v hv x hx => ?_
      U := St.U
      U_eq := St.U_eq },
    { y := y
      y_bij := y_bij
      y_lat := fun c x => ?_
      stabI := stabI
      stabI_inj := stabI_inj
      stabI_range := stabI_range }, ⟨?_, fun v => ?_, ?_, fun c => ?_, fun c s => ?_⟩, fun c => ?_⟩
  · rw [St.Uloc_hyp v (by rintro (h | h); exacts [h0 h, h1 h]) (hone v), hL]
  · rw [← hL] at hx
    exact mem_Uloc_of_princ St G V hs i v hv (hfr i v hv) x hx.1 hx.2
  · have e : Formalism.L2.Herm.crdLat S ((lat c).map (((Formalism.L2.Herm.crd S).symm : (Fin S.rank → E) →ₗ[E] S.V).restrictScalars (𝓞 E))) = lat c :=
      Crd.map_symm_map (Formalism.L2.Herm.crd S) (lat c)
    rw [e, ← hL]
    exact y_lat c x
  · rw [reL_rfl, hL]
  · show St.Uloc v = (St.Uloc v).map (reGL rfl _).toMonoidHom
    rw [reGL_rfl_hom, Subgroup.map_id]
  · show St.U = St.U.map (reGL rfl _).toMonoidHom
    rw [reGL_rfl_hom, Subgroup.map_id]
  · exact (reGL_rfl_apply _ _).symm
  · exact (reGL_rfl_apply _ _).symm
  · rw [show co S rfl = Formalism.L2.Herm.crd S from co_rfl S]
    exact (Crd.map_symm_map (Formalism.L2.Herm.crd S) (lat c)).symm

end Tr


set_option maxHeartbeats 4000000 in
theorem clsP_hermitian : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u, ∃ (lattice₂ : ((I.rec7 l Z).fm u).clsP → Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).sp.X'.V) (levP : Formalism.L2.Herm.StepLevel0 (I.rec7 l Z).sp.cm (I.rec7 l Z).sp.X' (I.rec7 l Z).host.g (Formalism.L2.Herm.crdLat (I.rec7 l Z).sp.X' (I.rec7 l Z).sp.X'.L0)) (clsP : Formalism.L2.Herm.ClassTie (I.rec7 l Z).sp.cm (I.rec7 l Z).sp.X' (Formalism.L2.Herm.crdLat (I.rec7 l Z).sp.X' (I.rec7 l Z).sp.X'.L0) levP.U ((I.rec7 l Z).fm u).stabilizer₂ lattice₂), SameCar (rankP (I.rec7 l Z)) (Formalism.L2.Herm.crdLat (I.rec7 l Z).sp.X' (I.rec7 l Z).sp.X'.L0) (F u).clsP.lev.Lb levP.Uloc (F u).clsP.lev.Uloc levP.U (F u).clsP.lev.U (fun c => (clsP.y c).1) (fun c => ((F u).clsP.y c).1) (fun c s => (clsP.stabI c s).1) (fun c s => ((F u).clsP.stabI c s).1) ∧ ∀ c, (F u).clsP.lat c = (lattice₂ c).map ((crdP (I.rec7 l Z) : (I.rec7 l Z).sp.X'.V →ₗ[(I.rec7 l Z).host.E] (Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1) → (I.rec7 l Z).host.E)).restrictScalars (𝓞 (I.rec7 l Z).host.E)) := by
  intro B X I hI hP l Z H F hstd hcar u
  obtain ⟨hs, -, hX', -⟩ := hI.spaces
  have oX' : Crd.Ortho B.sp.X' := by rw [hX']; exact Crd.ortho_pos hs _
  have hr := (hstd u).1.what₂
  have hLb : ∀ x, x ∈ (F u).clsP.lev.Lb ↔ ∀ j, x j ∈ (algebraMap (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E).range := by
    intro x
    refine (hr.lb x).trans ⟨fun hx j => ?_, fun hx j => ?_⟩
    · obtain ⟨r, e, -⟩ := hx j
      exact ⟨r, e.symm⟩
    · obtain ⟨r, e⟩ := hx j
      exact ⟨r, e.symm, fun _ => one_dvd r⟩
  exact tie_of_forms (I.rec7 l Z).sp.cm (I.rec7 l Z).sp.X' (rankP (I.rec7 l Z)) oX' rfl rfl rfl (F u).clsP.lev (F u).gl
    (F u).glevP (hstd u).1.frP hLb (F u).clsP.y (F u).clsP.y_bij (F u).clsP.lat (F u).clsP.y_lat (F u).clsP.stabI
    (F u).clsP.stabI_inj (F u).clsP.stabI_range

end GlobalTheory.Mem.Col2.HAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianSideClassesEqFormClassesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianSide_classes_eq_formClasses : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u, ∃ (lattice₂ : ((I.rec7 l Z).fm u).clsP → Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).sp.X'.V) (levP : Formalism.L2.Herm.StepLevel0 (I.rec7 l Z).sp.cm (I.rec7 l Z).sp.X' (I.rec7 l Z).host.g (Formalism.L2.Herm.crdLat (I.rec7 l Z).sp.X' (I.rec7 l Z).sp.X'.L0)) (clsP : Formalism.L2.Herm.ClassTie (I.rec7 l Z).sp.cm (I.rec7 l Z).sp.X' (Formalism.L2.Herm.crdLat (I.rec7 l Z).sp.X' (I.rec7 l Z).sp.X'.L0) levP.U ((I.rec7 l Z).fm u).stabilizer₂ lattice₂), SameCar (rankP (I.rec7 l Z)) (Formalism.L2.Herm.crdLat (I.rec7 l Z).sp.X' (I.rec7 l Z).sp.X'.L0) (F u).clsP.lev.Lb levP.Uloc (F u).clsP.lev.Uloc levP.U (F u).clsP.lev.U (fun c => (clsP.y c).1) (fun c => ((F u).clsP.y c).1) (fun c s => (clsP.stabI c s).1) (fun c s => ((F u).clsP.stabI c s).1) ∧ ∀ c, (F u).clsP.lat c = (lattice₂ c).map ((crdP (I.rec7 l Z) : (I.rec7 l Z).sp.X'.V →ₗ[(I.rec7 l Z).host.E] (Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1) → (I.rec7 l Z).host.E)).restrictScalars (𝓞 (I.rec7 l Z).host.E)) := by
  first | exact @GlobalTheory.Mem.Col2.HAt.clsP_hermitian | exact GlobalTheory.Mem.Col2.HAt.clsP_hermitian | (intros; apply GlobalTheory.Mem.Col2.HAt.clsP_hermitian <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StabiliserMapHyperplaneEqConjClassMap
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StabiliserMapHyperplaneEqConjClassMap
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000

namespace GlobalTheory.Mem.Col2.HAt.Stab

theorem co_apply {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {n : ℕ} (h : S.rank = n)
    (g : S.V ≃ₗ[E] S.V) (x : S.V) :
    co S h (g x) = (reGL h E (Formalism.L2.Herm.toGLb S.frame g)).1 *ᵥ co S h x := by
  have e : lin S h (reGL h E (Formalism.L2.Herm.toGLb S.frame g)) = g := by
    subst h
    have e0 : ∀ k : GL (Fin S.rank) E, reGL rfl E k = k := fun k => by
      ext a b
      simp [reGL]
    show (Formalism.L2.Herm.toGLb S.frame).symm (reGL rfl E (reGL rfl E (Formalism.L2.Herm.toGLb S.frame g))) = g
    rw [e0, e0, MulEquiv.symm_apply_apply]
  rw [← co_lin, e]

theorem co_symm_apply {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {n : ℕ} (h : S.rank = n)
    (k : GL (Fin S.rank) E) (x : S.V) :
    co S h ((Formalism.L2.Herm.toGLb S.frame).symm k x) = (reGL h E k).1 *ᵥ co S h x := by
  rw [co_apply, MulEquiv.apply_symm_apply]

theorem eq_of_frMul {E K ι : Type} [Field E] [Field K] [Fintype ι] (τ : ι) (emb : ι → E →+* K) (σ : K →+* ℂ) {n : ℕ}
    (g M : GL (Fin n) E) (y : Col2.Fr emb σ n) (h : frMul emb σ M⁻¹ (frMul emb σ g y) = y) : g = M := by
  have h1 : (M⁻¹ : GL (Fin n) E).1.map (embAt σ emb τ) * (g.1.map (embAt σ emb τ) * y.1 τ) = y.1 τ :=
    congrFun (congrArg Subtype.val h) τ
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul] at h1
  have hy : IsUnit (y.1 τ) := (Matrix.isUnit_iff_isUnit_det _).2 (y.2 τ)
  have h2 : (M⁻¹ * g : GL (Fin n) E).1.map (embAt σ emb τ) = 1 := hy.mul_right_cancel (by rw [h1, Matrix.one_mul])
  have h3 : (M⁻¹ * g : GL (Fin n) E).1 = 1 := by
    apply Matrix.map_injective (embAt σ emb τ).injective
    show _ = (1 : Matrix (Fin n) (Fin n) E).map (embAt σ emb τ)
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact h2
  have h4 : M⁻¹ * g = 1 := Units.ext h3
  exact (inv_mul_eq_one.1 h4).symm

theorem ext_vec {E : Type} [Field E] {N n : ℕ} (hN : N = n + 1) {x y : Fin N → E} (h1 : iniH hN x = iniH hN y)
    (h2 : x (Br.iL hN) = y (Br.iL hN)) : x = y := by
  funext j
  by_cases hj : j.1 < n
  · exact congrFun h1 ⟨j.1, hj⟩
  · have : j = Br.iL hN := Fin.ext (by have := j.2; show j.1 = n; omega)
    rw [this, h2]

theorem ga_eq_gam_mv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u)) → ∀ (u : B.Word) (c : ((I.rec7 l Z).fm u).clsP), ((F u).til.ga c).1.1 = ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))).1 := by
  intro B X I l Z H F hF u c
  classical
  have hemb : Formalism.L2.Forms.embT (I.rec7 l Z) = embAt B.embLL B.fields.emb := by
    funext τ
    ext y
    show B.host.φ₀ _ = _
    rw [← B.embE_φ₀]
    rfl
  let y : Col2.Fr B.fields.emb B.embLL (B.R.N B.R.m) := ⟨fun _ => 1, fun _ => by simp⟩
  let g : GL (Fin (B.R.N B.R.m)) B.fields.E := ((F u).til.ga c).1
  let φ : (I.stp u I.mu0 B.R.m).Cl → Col2.Fr B.fields.emb B.embLL (B.R.N B.R.m) → ℂ := fun _ z => if z = y then 1 else 0
  have hY := (hF u).eY B.R.m le_rfl (Or.inr rfl)
  have h := (F u).evz φ c (frMul B.fields.emb B.embLL g y) y (by
    intro τ
    rw [hemb]
    exact (congrFun (hY _) τ).trans (congrArg (fun k : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) ℂ => (g.1.map (embAt B.embLL B.fields.emb τ) * k : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) ℂ)) (congrFun (hY y) τ)).symm)
  rw [(hF u).eWz] at h
  have h' : B.embLL _ * φ ((I.perIn u I.mu0).tilC c) (frMul B.fields.emb B.embLL ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c)))⁻¹ (frMul B.fields.emb B.embLL g y)) = _ * φ ((I.perIn u I.mu0).tilC c) y := h
  have hy : frMul B.fields.emb B.embLL ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c)))⁻¹ (frMul B.fields.emb B.embLL g y) = y := by
    by_contra hne
    simp only [φ, if_neg hne, if_pos, mul_zero, mul_one] at h'
    exact Units.ne_zero _ h'.symm
  exact congrArg Units.val (eq_of_frMul (show B.fields.Tau from (I.rec7 l Z).eTau.symm 1) _ _ _ _ _ hy)

theorem crdN_stabM : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u)) → CarH H F → ∀ (u : B.Word) (h1 : 1 ≤ (I.rec7 l Z).R.m) (c : ((I.rec7 l Z).mem u).C.cls (I.rec7 l Z).R.m) (s : ((I.rec7 l Z).mem u).C.stab (I.rec7 l Z).R.m c) (y : ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m).V), crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl (Formalism.L2.Herm.stabMLinS (I.rec7 l Z) H u h1 c s y) = ((I.stp u I.mu0 B.R.m).gam c.1 s.1).1 *ᵥ crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl y := by
  intro B X I l Z H F hF hC u h1 c s y
  obtain ⟨k, hk⟩ := (hF u).ends B.R.m le_rfl (Or.inr rfl)
  have e1 := hk.stab c s
  have e2 := (hC.carM u).st_eq c s
  have e3 : ∀ (β β' : H.Ch u (I.rec7 l Z).R.m) (h : H.chOf u (I.rec7 l Z).R.m c = β) (h' : H.chOf u (I.rec7 l Z).R.m c = β'),
      ((H.cls u (I.rec7 l Z).R.m h1 le_rfl β).stabI ⟨c, h⟩ s).1 = ((H.cls u (I.rec7 l Z).R.m h1 le_rfl β').stabI ⟨c, h'⟩ s).1 := by
    intro β β' h h'
    subst h
    subst h'
    rfl
  refine (co_symm_apply ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m) (rankN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl) _ y).trans ?_
  refine congrArg (fun k : GL (Fin (B.R.N B.R.m)) B.fields.E => k.1 *ᵥ crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl y) ?_
  rw [← e1]
  exact (congrArg _ (e3 _ _ rfl (chOf_m H u c))).trans e2.symm

theorem crdP_stabP : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u)) → CarT H F A → ∀ (u : B.Word) (c : ((I.rec7 l Z).fm u).clsP) (s : ((I.rec7 l Z).fm u).stabilizer₂ c) (x : (I.rec7 l Z).sp.X'.V), crdP (I.rec7 l Z) (Formalism.L2.Herm.stabPLinS (I.rec7 l Z) H A u c s x) = ((I.perIn u I.mu0).S'.gam c.1 s.1).1 *ᵥ crdP (I.rec7 l Z) x := by
  intro B X I l Z H F A hF hC u c s x
  have e1 := (hF u).what₂.stab c s
  have e2 := (hC.carP u).st_eq c s
  refine (co_symm_apply (I.rec7 l Z).sp.X' (rankP (I.rec7 l Z)) _ x).trans ?_
  exact congrArg (fun k : GL (Fin (B.R.N B.R.m - 1)) B.fields.E => k.1 *ᵥ crdP (I.rec7 l Z) x) (e2.symm.trans e1)

theorem crdN_tilG : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), CarT H F A → ∀ (u : B.Word) (c : ((I.rec7 l Z).fm u).clsP) (y : ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m).V), crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl (((A u).tilG c).1 y) = ((F u).til.ga c).1.1 *ᵥ crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl y := by
  intro B X I l Z H F A hC u c y
  rw [hC.ga u c]
  exact co_apply ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m) (rankN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl) _ y

theorem gam_ext : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (b : (I.perIn u I.mu0).S'.β) (g : (I.perIn u I.mu0).S'.G b), (∀ y, ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).ext b g)).1 *ᵥ iXc (I.rec7 l Z) y = iXc (I.rec7 l Z) (((I.perIn u I.mu0).S'.gam b g).1 *ᵥ y)) ∧ ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).ext b g)).1 *ᵥ TC.z0 X u = TC.z0 X u := by
  intro B X I hOk hP l Z u b g
  have hi := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hP l Z).2.2.1
  have ini : ∀ y : Fin (B.R.N B.R.m - 1) → B.fields.E, iniH (N_m_succ B.R) (iXc (I.rec7 l Z) y) = y := fun y => by
    funext j
    exact (hi y _).trans (dif_pos j.2)
  have las : ∀ y : Fin (B.R.N B.R.m - 1) → B.fields.E, iXc (I.rec7 l Z) y (Br.iL (N_m_succ B.R)) = 0 := fun y =>
    (hi y _).trans (dif_neg (lt_irrefl _))
  refine ⟨fun y => ext_vec (N_m_succ B.R) ?_ ?_, ext_vec (N_m_succ B.R) ?_ ?_⟩
  · refine ((l.per u I.mu0).gam_ini b g _).trans ?_
    exact (congrArg _ (ini _)).trans (ini _).symm
  · exact ((l.per u I.mu0).gam_last b g _).trans ((las _).trans (las _).symm)
  · refine ((l.per u I.mu0).gam_ini b g _).trans ?_
    have z : iniH (E := B.fields.E) (N_m_succ B.R) (TC.z0 X u) = 0 := by
      funext j
      exact if_neg (by have := j.2; show ¬ (j.1 + 1 = _); omega)
    exact (congrArg _ z).trans ((Matrix.mulVec_zero _).trans z.symm)
  · exact (l.per u I.mu0).gam_last b g _

theorem stabMap_tied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), CarT H F A → Formalism.L2.Herm.SymmetricStabilizerMapCompatibility (I.rec7 l Z) H A := by
  intro B X I hOk hPins l Z H F hStd hCarH A hCarT u h1 c s
  have hF : ∀ u, I.StdF l Z u (F u) := fun u => (hStd u).1
  have hga := ga_eq_gam_mv I l Z H F hF u c
  have conj : ∀ v, ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))).1 *ᵥ
      (((I.stp u I.mu0 B.R.m).gam _ (((I.rec7 l Z).fm u).stabMap c s).1).1 *ᵥ v) =
      ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).ext c.1 s.1)).1 *ᵥ
      (((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))).1 *ᵥ v) := by
    intro v
    show _ *ᵥ (((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 (((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))⁻¹ * (I.perIn u I.mu0).ext c.1 s.1 *
          (I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))).1 *ᵥ v) = _
    rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have key : ∀ y, crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl (((A u).tilG c).1 (Formalism.L2.Herm.stabMLinS (I.rec7 l Z) H u h1 _
      (((I.rec7 l Z).fm u).stabMap c s) (((A u).tilG c).1.symm y))) =
      ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).ext c.1 s.1)).1 *ᵥ crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl y := by
    intro y
    have hw : ((F u).til.ga c).1.1 *ᵥ crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl (((A u).tilG c).1.symm y) =
        crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl y := by
      rw [← crdN_tilG I l Z H F A hCarT u c, LinearEquiv.apply_symm_apply]
    rw [crdN_tilG I l Z H F A hCarT u c, crdN_stabM I l Z H F hF hCarH u h1, ← hw, hga]
    exact conj _
  have hiX : ∀ x, crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl ((I.rec7 l Z).sp.iX' x) = iXc (I.rec7 l Z) (crdP (I.rec7 l Z) x) := by
    intro x
    simp [iXc, crdN, crdP]
  have hext := gam_ext I hOk hPins l Z u c.1 s.1
  refine ⟨fun x => ?_, ?_⟩
  · apply (crdN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m le_rfl).injective
    rw [key, hiX, hiX, hext.1, crdP_stabP I l Z H F A hF hCarT u c s x]
    rfl
  · apply (crdN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m le_rfl).injective
    rw [key, ← hCarT.z0 u]
    have hz : (F u).til.z0 = TC.z0 X u := funext fun j => (hF u).z0 j
    rw [hz, hext.2]

end GlobalTheory.Mem.Col2.HAt.Stab
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StabiliserMapHyperplaneEqConjClassMapStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabiliserMap_hyperplane_eq_conj_classMap : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), CarT H F A → Formalism.L2.Herm.SymmetricStabilizerMapCompatibility (I.rec7 l Z) H A := by
  first | exact @GlobalTheory.Mem.Col2.HAt.Stab.stabMap_tied | exact GlobalTheory.Mem.Col2.HAt.Stab.stabMap_tied | (intros; apply GlobalTheory.Mem.Col2.HAt.Stab.stabMap_tied <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianDataAtLevelPrime
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Mem.Col2.TC.hermitian_data_at_level_prime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∃ A, CarT H F A ∧ Formalism.L2.Herm.SymmetricAdelicCompatibility (I.rec7 l Z) H A ∧ Formalism.L2.Herm.SymmetricStabilizerMapCompatibility (I.rec7 l Z) H A := by
  intro B X I hI hP l Z H F hS hC
  have hseen := GlobalTheory.T.hermitianSeenPrimeCondition_hermitianSide I hI hP l Z H F hS hC
  have hdisc := GlobalTheory.T.dual_mod_class_lattice_equiv_quotient I hI hP l Z H F hS hC
  have hlvc := GlobalTheory.T.middleStep_oneLevel_projection_eq_chart_projection I hI hP l Z H F hS hC
  have hstab := GlobalTheory.T.stabiliserMap_hyperplane_eq_conj_classMap I hI hP l Z H F hS hC
  choose upG hup using GlobalTheory.T.hermitianUpMove_at_levelPrime_place I hI hP l Z H F hS hC
  choose dnG hdn using GlobalTheory.T.exists_hermitianDownMove_at_levelPrime_place I hI hP l Z H F hS hC
  choose dilG hdil using GlobalTheory.T.diamondOperator_hermitian_side_levelPrime I hI hP l Z H F hS hC
  choose lattice₂ levP clsP hcar hlat using GlobalTheory.T.hermitianSide_classes_eq_formClasses I hI hP l Z H F hS hC
  let A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u) := fun u =>
    mkAtT (F u).atT (F u).lv (hC.eV u) (hC.fv u) (hseen u) (hdisc u) (upG u) (fun i hi v c y h => (hup u i v c y hi h).1)
      (dnG u) (fun i hi v c g h => (hdn u i v c g hi h).1) (dilG u) (fun i hi v a c => (hdil u i v a c hi).1)
      (lattice₂ u) (levP u) (clsP u) (F u).til (hlat u)
  have hT : CarT H F A := by
    refine ⟨fun _ => rfl, fun _ => rfl, hcar, hlat, ?_, ?_, ?_, ?_, ?_⟩
    · intro u i hi v c z z' h
      exact (congrArg _ (Subtype.ext h)).trans (prH_eq (F u).atT (F u).lv hi v c z).symm
    · intro u i hi v c z z' h
      exact (congrArg _ (Subtype.ext h)).trans (prkH_eq (F u).atT (F u).lv hi v c z).symm
    · intro u i h1 h2 v c z z' h
      refine ((hlvc u i h1 h2 v c).1 (toLd i (le_of_succ_m h2) c z) z' h).trans (prH_eq (F u).atT (F u).lv (le_of_succ_m h2) v c z).symm
    · intro u
      exact ((crdN (I.rec7 l Z) _ le_rfl).apply_symm_apply _).symm
    · intro u c
      exact (reGL_lin _ (rankN (I.rec7 l Z) _ le_rfl) _).symm
  refine ⟨A, hT, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hstab A hT⟩
  · intro u v c y h
    exact (hup u 0 v c y (Nat.zero_le _) h).2
  · intro u i h1 hm v c y h
    cases i with
    | zero => omega
    | succ i => exact (hup u (i + 1) v c y hm h).2 hm
  · intro u v c g h
    exact (hdn u 0 v c g (Nat.zero_le _) h).2
  · intro u i h1 hm v c g h
    cases i with
    | zero => omega
    | succ i => exact (hdn u (i + 1) v c g hm h).2 hm
  · intro u v a c
    exact (hdil u 0 v a c (Nat.zero_le _)).2
  · intro u i h1 hm v a c
    cases i with
    | zero => omega
    | succ i => exact (hdil u (i + 1) v a c hm).2 hm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianDataAtLevelPrimeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitian_data_carT_of_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∃ A, CarT H F A ∧ Formalism.L2.Herm.SymmetricAdelicCompatibility (I.rec7 l Z) H A ∧ Formalism.L2.Herm.SymmetricStabilizerMapCompatibility (I.rec7 l Z) H A := by
  first | exact @GlobalTheory.Mem.Col2.TC.hermitian_data_at_level_prime | exact GlobalTheory.Mem.Col2.TC.hermitian_data_at_level_prime | (intros; apply GlobalTheory.Mem.Col2.TC.hermitian_data_at_level_prime <;> assumption)
end
