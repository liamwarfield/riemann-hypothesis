module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NormalisedPullbackCommutesSymmetricTranslations
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HalfPrincipalAndSplit
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueSymmetricTranslateOddLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueSymmetricTranslateOddLevel
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.SymMove

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {k : ℤ}

theorem act_unique (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {n : ℕ} (hn : Odd n) {x : T ⟶ A}
    {θ θ' : ThetaGrp A L k T} (h : SymLift A L k n x θ) (h' : SymLift A L k n x θ')
    {s t t' : LB.Sec (LPow A L k T)} (a : IsActOf A L k θ s t) (a' : IsActOf A L k θ' s t') : t = t' := by
  have hc := SymLiftOdd.symLift_unique hG hA hL hn θ θ' h h'
  have e : θ.pt = θ'.pt := h.pt_eq.trans h'.pt_eq.symm
  have key : ∀ j, t.f j = t'.f j :=
    sec_ext_val hL (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) (s := t) (s' := t')
      fun y J hJ => (twist_val a (𝟙 _) y hJ).trans (Eq.trans (congrArg₂ (· * ·)
        (congrArg Units.val (val_corr hJ hc (𝟙 _))) (by rw [e])) (twist_val a' (𝟙 _) y hJ).symm)
  obtain ⟨f₁, p₁⟩ := t
  obtain ⟨f₂, p₂⟩ := t'
  obtain rfl : f₁ = f₂ := funext key
  rfl

theorem exists_one (hL : L.IsLB) {ν : LB.Gen (negLB A L k T)} (hν : ν.IsGen) (n : ℕ) (s : LB.Sec (LPow A L k T)) :
    ∃ θ : ThetaGrp A L k T, SymLift A L k n 1 θ ∧ IsActOf A L k θ s s := by
  obtain ⟨o, ho, vo⟩ := ThetaCoord.exists_symLift_one hL hν n
  refine ⟨o, ho, VVRank.isTwistPull_of_sv A hL o.isGen fun z J hJ => ?_⟩
  have e : translT A (1 : T ⟶ A) = 𝟙 _ := by
    rw [translT, ThetaAct.translPt_one, lift_fst_snd]
  change _ = (CommPairing.tval o (𝟙 _) z J).val * _
  rw [vo _ _ z J hJ, ho.pt_eq, e, Units.val_one, _root_.one_mul, Over.id_left]
  rfl

end GlobalTheory.SymMove

namespace GlobalTheory

theorem existsUnique_moves : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (k : ℕ), Odd k → ∀ (b : (ptO Xo x ⟶ Xo.univ.t.G)), b ^ k = 1 → ∀ F : SecN Xo x k, (∃! F' : SecN Xo x k, Moves Xo b F F') ∧ Moves Xo 1 F F := by
  intro E _ _ _ H Dw l Xo S _ x k hk b hb F
  have hLaw : Laws := firstFiveLaws.1
  have := UnivPol.isLocallyNoetherian Xo
  have hA : IsAbelianScheme Xo.univ.t.G := (UnivPol.pol Xo).isAb
  have hL : Xo.univ.t.PP.L.IsLB := (UnivPol.pol Xo).isLB
  obtain ⟨U, hU⟩ : ∃ U : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo x),
      SymLift Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) k b U :=
    exists_symLift_global hLaw Xo.X (UnivPol.pol Xo) k hk (UnivPol.isUnit_natCast Xo _ hk.pos) _ b hb
  obtain ⟨F', hF', -⟩ := existsUnique_isTwistPull _ _ _ hL _ (translT _ U.pt) (translPt _ U.pt) (lift_snd _ _)
    k k U.φ U.isGen F
  obtain ⟨ν, hν, -⟩ := hU.sym
  refine ⟨⟨F', ⟨hb, U, hU, hF'⟩, fun F'' h => ?_⟩, one_pow k, SymMove.exists_one hL hν k F⟩
  obtain ⟨-, U', hU', a⟩ := h
  exact SymMove.act_unique hLaw.globalFns hA hL hk hU' hU a hF'

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueSymmetricTranslateOddLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_symmetricTranslate_oddLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (k : ℕ), Odd k → ∀ (b : (ptO Xo x ⟶ Xo.univ.t.G)), b ^ k = 1 → ∀ F : SecN Xo x k, (∃! F' : SecN Xo x k, Moves Xo b F F') ∧ Moves Xo 1 F F := by
  first | exact @GlobalTheory.existsUnique_moves | exact GlobalTheory.existsUnique_moves | (intros; apply GlobalTheory.existsUnique_moves <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsThetaValData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.RatData

theorem epi_spMap_fields {K L : Type} [Field K] [Field L] (i : K →+* L) : Epi (spMap i) := by
  have : Flat (spMap i) := by
    rw [spMap, Flat.SpecMap_iff]
    exact RingHom.Flat.of_isField (Field.toIsField K) _
  have : Surjective (spMap i) := ⟨Function.surjective_to_subsingleton _⟩
  exact Flat.epi_of_flat_of_surjective _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem cancel_of_left_eq (Xo : Moduli Dw l) {K L : Type} [Field K] [Field L] {x : Sp K ⟶ Xo.X} {x' : Sp L ⟶ Xo.X}
    (i : K →+* L) (g : ptO Xo x' ⟶ ptO Xo x) (hg : g.left = spMap i) {a b : ptO Xo x ⟶ Xo.univ.t.G}
    (h : g ≫ a = g ≫ b) : a = b := by
  have := epi_spMap_fields i
  have h₁ := congrArg (fun f => f.left) h
  simp only [Over.comp_left, hg] at h₁
  ext1
  exact (cancel_epi (spMap i)).1 h₁

theorem descend (Xo : Moduli Dw l) {K : Type} [Field K] (x : Sp K ⟶ Xo.X) (M : ℕ) (hx : AllRat Xo x M)
    {B : Type} [CommRing B] (φ : K →+* B) (hφ : φ.FaithfullyFlat) :
    ∃ (Ω : Type) (_ : Field Ω) (χ : B →+* Ω) (x' : Sp Ω ⟶ Xo.X) (g₁ : ptO Xo x' ⟶ ptO Xo (spMap φ ≫ x))
      (g₂ : ptO Xo x' ⟶ ptO Xo x), g₁.left = spMap χ ∧ g₂.left = spMap (χ.comp φ) ∧ g₂.left = g₁.left ≫ spMap φ ∧
      ∀ w : ptO Xo (spMap φ ≫ x) ⟶ Xo.univ.t.G, w ^ M = 1 → ∃ a, g₂ ≫ a = g₁ ≫ w := by
  have : Nontrivial B := hφ.injective.nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  let χ : B →+* B ⧸ m := Ideal.Quotient.mk m
  have hc : spMap (χ.comp φ) = spMap χ ≫ spMap φ := by
    rw [spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  let g₁ : ptO Xo (spMap (χ.comp φ) ≫ x) ⟶ ptO Xo (spMap φ ≫ x) :=
    Over.homMk (spMap χ) (by
      change spMap χ ≫ spMap φ ≫ x = spMap (χ.comp φ) ≫ x
      rw [hc, Category.assoc])
  let g₂ : ptO Xo (spMap (χ.comp φ) ≫ x) ⟶ ptO Xo x := Over.homMk (spMap (χ.comp φ)) rfl
  refine ⟨B ⧸ m, inferInstance, χ, _, g₁, g₂, rfl, rfl, hc, fun w hw => ?_⟩
  obtain ⟨a, ha⟩ := hx (B ⧸ m) (χ.comp φ) (g₁ ≫ w) (by rw [← MonObj.comp_pow, hw, MonObj.comp_one])
  exact ⟨a, Over.OverMorphism.ext ha.symm⟩

theorem exists_root (Xo : Moduli Dw l) {K : Type} [Field K] (x : Sp K ⟶ Xo.X) (N : ℕ) (hN : 0 < N)
    (hx : AllRat Xo x (N ^ 2)) (t : ptO Xo x ⟶ Xo.univ.t.G) (ht : t ^ N = 1) : ∃ r, r ^ N = t := by
  obtain ⟨B, _, φ, w, hφ, hw⟩ := GlobalTheory.T.exists_faithfullyFlat_nthRoots_of_torsion GlobalTheory.firstFiveLaws.1 E H Dw l Xo K x N N hN hN Unit
    (fun _ => t) (fun _ => ht)
  obtain ⟨Ω, _, χ, x', g₁, g₂, h₁, h₂, h₃, h₄⟩ := descend Xo x _ hx φ hφ
  let g : ptO Xo (spMap φ ≫ x) ⟶ ptO Xo x := Over.homMk (spMap φ) rfl
  have hw' : w () ^ N = g ≫ t := Over.OverMorphism.ext (hw ())
  have hg : g₂ = g₁ ≫ g := Over.OverMorphism.ext h₃
  obtain ⟨a, ha⟩ := h₄ (w ()) (by rw [pow_two, pow_mul, hw', ← MonObj.comp_pow, ht, MonObj.comp_one])
  refine ⟨a, cancel_of_left_eq Xo _ g₂ h₂ ?_⟩
  rw [MonObj.comp_pow, ha, ← MonObj.comp_pow, hw', hg, Category.assoc]

theorem exists_linear_level (Xo : Moduli Dw l) {K : Type} [Field K] (x : Sp K ⟶ Xo.X) (k : ℕ) (hk : 0 < k)
    (hx : AllRat Xo x k) : ∃ ev : Dw.La → (ptO Xo x ⟶ Xo.univ.t.G), (∀ a b, ev (a + b) = ev a * ev b) ∧
      (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ Xo.univ.t.act.act o) ∧ (∀ a, ev (k • a) = 1) ∧
      ∀ a b, ev a = ev b → Dw.ModN k (a - b) := by
  obtain ⟨B, _, φ, ev, hφ, hadd, hsm, hkill, hinj⟩ := GlobalTheory.T.exists_faithfullyFlat_full_linear_level_structure GlobalTheory.firstFiveLaws.1 E H Dw l Xo K x k hk
  obtain ⟨Ω, _, χ, x', g₁, g₂, h₁, h₂, -, h₄⟩ := descend Xo x _ hx φ hφ
  choose e he using fun a => h₄ (ev a) (by rw [← map_nsmul_eq_pow_of_add_eq_mul ev hadd, hkill])
  refine ⟨e, fun a b => cancel_of_left_eq Xo _ g₂ h₂ ?_, fun o a => cancel_of_left_eq Xo _ g₂ h₂ ?_,
    fun a => cancel_of_left_eq Xo _ g₂ h₂ ?_, fun a b hab => hinj Ω χ a b ?_⟩
  · rw [MonObj.comp_mul, he, he, he, hadd, MonObj.comp_mul]
  · rw [← Category.assoc, he, he, hsm, Category.assoc]
  · rw [he, hkill, MonObj.comp_one, MonObj.comp_one]
  · have h : g₁ ≫ ev a = g₁ ≫ ev b := by rw [← he, ← he, hab]
    have h' := congrArg (fun f => f.left) h
    simp only [Over.comp_left, h₁] at h'
    exact h'

theorem exists_thetaVal_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), (AllRat Xo y.x (l.M ^ 2) → ∀ x : Dw.La, ∃ F, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y.s (levPt Xo y.x x) F) ∧ ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.LevOK N l.M → AllRat Xo y.x (N ^ 2) → ∃ (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (tp : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), (∀ i, InZh Xo Λ N (z i)) ∧ GeoInj Xo y.x z ∧ (∀ q b, tp q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp q b)) ∧ (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z i b) (tp q b) (F q i b)) := by
  intro E _ _ _ H Dw l Xo c K _ _ y
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hM : 0 < l.M := l.odd.pos
  have hlev : ∀ a : Dw.La, KilledBy Xo l.Mb (levPt Xo y.x a) ∧ levPt Xo y.x a ^ l.M = 1 := by
    intro a
    obtain ⟨h₁, -, h₃⟩ := moduli_univ_eta_killed hL E H Dw l Xo a
    refine ⟨fun b hb => ?_, ?_⟩
    · rw [levPt, Category.assoc, h₁ b hb, MonObj.comp_one]
    · rw [levPt, ← MonObj.comp_pow, h₃, MonObj.comp_one]
  refine ⟨fun hx a => ?_, fun n Λ N hU hLev hx => ?_⟩
  · obtain ⟨v, hv⟩ := exists_root Xo y.x l.M hM hx _ (hlev a).2
    obtain ⟨t', ht', hk⟩ := (exists_root_killedBy_pow E H Dw l Xo _ _ v l.M hM (hlev a).1 hv).2 rfl
    refine (exists_isVtOver_and_existsUnique_isUUOver hL E H Dw l Xo l.M l.odd (ptO Xo y.x) y.s).1 _ _ t' ht' ?_ hk
    rw [pow_two, pow_mul, ht', (hlev a).2]
  · obtain ⟨hodd, hdvd, hle⟩ := hLev
    have hN : 0 < N := hodd.pos
    have hlevN : ∀ a : Dw.La, levPt Xo y.x a ^ N = 1 := by
      intro a
      obtain ⟨k, hk⟩ := hdvd
      rw [hk, pow_mul, (hlev a).2, one_pow]
    choose r hr using fun q : LevQ Dw l => exists_root Xo y.x N hN hx _ (hlevN (levRep q))
    choose t ht ht' using fun q =>
      (exists_root_killedBy_pow E H Dw l Xo _ _ _ N hN (hlev _).1 (hr q)).1
    have htN : ∀ q, t q ^ (N ^ 2) = 1 := fun q => by rw [pow_two, pow_mul, ht q, hlevN]
    obtain ⟨ev, hadd, hsm, hk, hinj⟩ := exists_linear_level Xo y.x (N ^ 2) (pow_pos hN 2) hx
    obtain ⟨zz, hz, hzi, -⟩ := GlobalTheory.T.exists_isotropic_group_lattice_class_representatives E H Dw n Λ N hU hN (hle.trans inf_le_left)
    have hZ : ∀ i, InZh Xo Λ N (fun b => ev (zz i b)) := by
      refine fun i => ⟨fun b => ?_, ?_⟩
      · rw [← map_nsmul_eq_pow_of_add_eq_mul ev hadd, hk]
      · intro mu hmu cm hcm i'
        obtain ⟨u, hu⟩ := hz i mu hmu cm hcm i'
        simp only [← hsm]
        rw [← map_sum_eq_prod_ofFn_of_add_eq_mul ev hadd, hu]
        exact hk u
    choose F hF using fun (q : Fin n → LevQ Dw l) i b =>
      ((exists_isVtOver_and_existsUnique_isUUOver hL E H Dw l Xo N hodd _ y.s).2 (ev (zz i b)) (t (q b))
        ((hZ i).1 b) (htN _)).exists
    refine ⟨fun i b => ev (zz i b), fun q b => t (q b), F, hZ, ?_, fun q b => ⟨ht _, ht' _⟩, hF⟩
    intro k _ ψ g hg i i' hii
    exact hzi _ _ fun b => hinj _ _ (cancel_of_left_eq Xo ψ g hg (congrFun hii b))

end GlobalTheory.RatData
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortThetaValueFieldEqMapSubfieldData
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortThetaValueFieldEqMapSubfieldData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShortAtField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_pull [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {n : ℕ} (Λ : GenLat E n) (N : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ HH c a n)
    {S T : Type} [CommRing S] [Algebra c.F S] [Field T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) (w : FrPt Xo c T) (hm : FrMap ψ y w)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (tp : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x)))
    (hz : ∀ i, InZh Xo Λ N (z i)) (hg : GeoInj Xo y.x z)
    (ht : ∀ q b, tp q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp q b))
    (hF : ∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z i b) (tp q b) (F q i b)) :
    ∃ (z' : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo w.x ⟶ Xo.univ.t.G))
      (tp' : (Fin n → LevQ Dw l) → Fin n → (ptO Xo w.x ⟶ Xo.univ.t.G))
      (F' : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
        LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo w.x))),
      (∀ i, InZh Xo Λ N (z' i)) ∧ GeoInj Xo w.x z' ∧
      (∀ q b, tp' q b ^ N = levPt Xo w.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp' q b)) ∧
      (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N w.s (z' i b) (tp' q b) (F' q i b)) ∧
      ∀ q, ψ (∑ i, ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
          ∏ b, nab y ((N : ℤ) ^ 2) (F q i b) (colOf m b)) =
        ∑ i, ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) *
          ∏ b, nab w ((N : ℤ) ^ 2) (F' q i b) (colOf m b) := by
  let h : ptO Xo w.x ⟶ ptO Xo y.x := Over.homMk (spMap ψ.toRingHom) hm.1.symm
  choose F' hF' using fun q i b => GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2)
    (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F q i b)
  obtain ⟨p1, -, p3, -⟩ := GlobalTheory.inZh_geoInj_stable E H Dw l Xo n Λ N
  refine ⟨fun i b => h ≫ z i b, fun q b => h ≫ tp q b, F', fun i => p1 _ _ h _ (hz i),
    p3 S T y.x w.x ψ.toRingHom h rfl _ z hg, fun q b => ⟨?_, ?_⟩, fun q i b => ?_, fun q => ?_⟩
  · have e : h ≫ levPt Xo y.x (levRep (q b)) = levPt Xo w.x (levRep (q b)) := by
      unfold levPt
      rw [← Category.assoc, comp_toUnit]
    rw [← e, ← (ht q b).1, MonObj.comp_pow]
  · obtain ⟨j, hj⟩ := (ht q b).2
    exact ⟨j, fun u hu => by rw [Category.assoc, hj u hu, MonObj.comp_one]⟩
  · exact (GlobalTheory.VtBaseChange.isVtOver_isUUOver_baseChange E H Dw l Xo N ⊤ _ _ h y.s w.s
      (GlobalTheory.FramedBaseChange.isPullSec ψ hm h rfl) (F q i b) (F' q i b) (hF' q i b)).2 _ _ (hF q i b)
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum]
      exact Finset.sum_congr rfl fun i _ =>
        GlobalTheory.harmonicValue_baseChange_field E H Dw l Xo c nab hnab S T ψ y w hm h rfl a n P hP N (F q i) (F' q i)
          (hF' q i)

theorem finite_levQ (Dw : Datum H) (l : Geo.Tor.Level H) : Finite (LevQ Dw l) := by
  have hne : l.Mb ≠ ⊥ := by
    intro h
    have hp := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] at hp
    have := l.three_le
    omega
  haveI : Finite (𝓞 E ⧸ l.Mb) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  haveI := Dw.fin
  exact Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem map_weighted {F S₁ S₂ T Q : Type} [Field F] [CommRing S₁] [CommRing S₂] [CommRing T]
    [Algebra F S₁] [Algebra F S₂] [Algebra F T] [Finite Q] (ψ₁ : S₁ →ₐ[F] T) (ψ₂ : S₂ →ₐ[F] T)
    (k : F) (w : Q → F) (A₁ : Q → S₁) (A₂ : Q → S₂) (h : ∀ q, ψ₁ (A₁ q) = ψ₂ (A₂ q)) :
    ψ₁ (algebraMap F S₁ k * ∑ᶠ q, algebraMap F S₁ (w q) * A₁ q) =
      ψ₂ (algebraMap F S₂ k * ∑ᶠ q, algebraMap F S₂ (w q) * A₂ q) := by
  haveI := Fintype.ofFinite Q
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [finsum_eq_sum_of_fintype, map_mul, map_sum, AlgHom.commutes, h]

theorem exists_algHom_field (F S : Type) [Field F] [CommRing S] [Nontrivial S] [Algebra F S] :
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra F Ω), Nonempty (S →ₐ[F] Ω) := by
  obtain ⟨J, hJ⟩ := Ideal.exists_maximal S
  exact ⟨S ⧸ J, Ideal.Quotient.field J, inferInstance, ⟨Ideal.Quotient.mkₐ F J⟩⟩

theorem shortValAt_eq_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HH c w n → ∀ (cf : (Fin n → LevQ Dw l) → c.F) (β : c.F) (K k : Type) [Field K] [Algebra c.F K] [Field k] [Algebra c.F k] (ψ : K →ₐ[c.F] k) (y : FrPt Xo c K) (yk : FrPt Xo c k), FrMap ψ y yk → ∀ (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (tp : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), (∀ i, InZh Xo Λ N (z i)) → GeoInj Xo y.x z → (∀ q b, tp q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z i b) (tp q b) (F q i b)) → ∀ v : k, ShortValAt Xo c nab cf Λ β N P yk v → v = ψ (algebraMap c.F K (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) * ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c.F K (cf q) * ∑ i, hv Xo c nab y (N ^ 2) (fun b => sqN Xo N (F q i b)) P) := by
  intro E _ _ _ H Dw l Xo c _ hstar nab hnab n Λ N hU hT hN w P hP cf β K k _ _ _ _ ψ y yk hψ z tp F hz hg ht hF v hv
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  haveI := finite_levQ Dw l
  obtain ⟨S1, _, _, φ1, y1, z1, tp1, F1, hf1, hm1, hz1, hg1, ht1, hu1, e1⟩ := hv
  have hinj : Function.Injective φ1 := hf1.injective
  haveI : Nontrivial S1 := hinj.nontrivial
  obtain ⟨Ω, _, _, ⟨κ⟩⟩ := exists_algHom_field c.F S1
  obtain ⟨u, hu⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c S1 Ω κ y1
  have hu' : FrMap (κ.comp (φ1.comp ψ)) y u :=
    GlobalTheory.FramedBaseChange.trans (φ1.comp ψ) κ (GlobalTheory.FramedBaseChange.trans ψ φ1 hψ hm1) hu
  obtain ⟨z1', tp1', G1, a1', b1', c1', d1', f1⟩ :=
    exists_pull nab hnab Λ N w P hP κ y1 u hu z1 tp1 F1 hz1 hg1 ht1 hu1
  obtain ⟨z2', tp2', G2, a2', b2', c2', d2', f2⟩ :=
    exists_pull nab hnab Λ N w P hP (κ.comp (φ1.comp ψ)) y u hu' z tp F hz hg ht hF
  apply (κ.comp φ1).toRingHom.injective
  change κ (φ1 v) = (κ.comp (φ1.comp ψ)) _
  rw [e1]
  refine map_weighted κ (κ.comp (φ1.comp ψ)) _ cf _ _ fun q => ?_
  have hc := (GlobalTheory.PlaceInt.hv_linear E H Dw l Xo c hstar nab hnab K y n P).2.2 N
  rw [← Finset.sum_congr rfl fun i _ => hc (F q i)]
  exact (f1 q).trans ((GlobalTheory.shortSum_indep_local hL E H Dw l Xo c nab hnab n Λ N hU hT hN P Ω u z1' tp1' G1 z2' tp2' G2
    a1' b1' c1' d1' a2' b2' c2' d2' q).trans (f2 q).symm)

end GlobalTheory.ShortAtField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortThetaValueFieldEqMapSubfieldDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortThetaValue_field_eq_map_subfield_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HH c w n → ∀ (cf : (Fin n → LevQ Dw l) → c.F) (β : c.F) (K k : Type) [Field K] [Algebra c.F K] [Field k] [Algebra c.F k] (ψ : K →ₐ[c.F] k) (y : FrPt Xo c K) (yk : FrPt Xo c k), FrMap ψ y yk → ∀ (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (tp : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), (∀ i, InZh Xo Λ N (z i)) → GeoInj Xo y.x z → (∀ q b, tp q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z i b) (tp q b) (F q i b)) → ∀ v : k, ShortValAt Xo c nab cf Λ β N P yk v → v = ψ (algebraMap c.F K (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) * ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c.F K (cf q) * ∑ i, hv Xo c nab y (N ^ 2) (fun b => sqN Xo N (F q i b)) P) := by
  first | exact @GlobalTheory.ShortAtField.shortValAt_eq_map | exact GlobalTheory.ShortAtField.shortValAt_eq_map | (intros; apply GlobalTheory.ShortAtField.shortValAt_eq_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EqZeroOfComplex
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.CoverRoot

theorem eq_zero_of_complex {K : Type} [Field K] (σ : K →+* ℂ) (p : TRing K) (r : p.R)
    (h : ∀ χ : p.R →ₐ[K] CAt σ, χ r = 0) : r = 0 := by
  refine ReciprocityTheory.ChartRestriction.G.TB.detAlg_holds K p.n p.I p.rad r fun L _ _ _ ψ => ?_
  letI : Algebra K ℂ := σ.toAlgebra
  let e : L →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have h2 : e (ψ r) = 0 := h (e.comp ψ)
  exact (map_eq_zero_iff e e.injective).mp h2

theorem value_pow_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (Cls : Type) [CommGroup Cls] [Finite Cls] (δ : Cls →* d.c₂.Fˣ) (gdet : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom) → Cls), CMP Xo c d _ Cls δ gdet false → ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ ^ m₀ = 1 := by
  intro E _ _ _ H Dw l Xo c n d Cls _ _ δ gdet h
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hWD := (GlobalTheory.Frames.algebraic_laws hL.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂).2.2.1
  have hnat := h.1.1
  refine ⟨Nat.card Cls, Nat.card_pos, fun k _ _ y₂ => ?_⟩
  obtain ⟨p, φ, y', hy⟩ := GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂ k y₂
  have key : d.cδ p y' ^ Nat.card Cls - 1 = 0 := by
    refine eq_zero_of_complex d.c₂.F.val.toRingHom p _ fun χ => ?_
    obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw d.l₂ d.Xo₂ d.c₂ _ _ χ y'
    have e1 : evR d.Xo₂ d.c₂ d.cδ z = χ (d.cδ p y') :=
      ReciprocityTheory.ChartRestriction.G.PullbackSections.evalAt_eq_of _ _ hWD d.cδ hnat p χ y' z hz
    have e2 := h.2 z
    rw [map_sub, map_pow, map_one, ← e1, e2, ← map_pow, if_neg (by simp), ← Units.val_pow_eq_pow_val, ← map_pow,
      pow_card_eq_one', map_one, Units.val_one, map_one, sub_self]
  have e3 : evR d.Xo₂ d.c₂ d.cδ y₂ = φ (d.cδ p y') :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.evalAt_eq_of _ _ hWD d.cδ hnat p φ y' y₂ hy
  rw [e3, ← map_pow, sub_eq_zero.mp key, map_one]

end GlobalTheory.CoverRoot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EqOfSqEqOfOdd
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem eq_of_sq_eq_of_odd {U : Type} [CommGroup U] {r r' : U} {k : ℕ} (hk : Odd k) (h : r ^ 2 = r' ^ 2)
    (h₁ : r ^ k = 1) (h₂ : r' ^ k = 1) : r = r' := by
  obtain ⟨t, rfl⟩ := hk
  rw [pow_succ, pow_mul] at h₁ h₂
  rw [h] at h₁
  exact mul_left_cancel (h₁.trans h₂.symm)

theorem moves_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (k : ℕ), Odd k → ∀ (a b : (ptO Xo x ⟶ Xo.univ.t.G)) (e : Γ((ptO Xo x).left, ⊤)ˣ), a ^ k = 1 → b ^ k = 1 → WeilIs Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) a b e → ∃ r : S, toΓ S r ^ 2 = (e : Γ((ptO Xo x).left, ⊤)) ∧ r ^ k = 1 ∧ ∀ F F₁ F₂ F₃ : SecN Xo x k, Moves Xo b F F₁ → Moves Xo a F₁ F₂ → Moves Xo (a * b) F F₃ → (∀ j, F₂.f j = liftFun Xo.univ.t.G _ (T := ptO Xo x) (toΓ S r) * F₃.f j) := by
  intro E _ _ _ H Dw l Xo S _ x k hk a b e ha hb he
  have hLaw : Laws := GlobalTheory.firstFiveLaws.1
  have := UnivPol.isLocallyNoetherian Xo
  have ex : ∀ c : ptO Xo x ⟶ Xo.univ.t.G, c ^ k = 1 →
      ∃ U : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo x), SymLift Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) k c U :=
    fun c hc => (symLift_exists_unique_of_cast hLaw Xo.X (UnivPol.pol Xo) k hk
      (UnivPol.isUnit_natCast Xo _ hk.pos) (k : ℤ) rfl (ptO Xo x) c hc).1
  have hA := (moduli_univ_polAV E H Dw l Xo).2.2.2.1
  obtain ⟨Ua, hUa⟩ := ex a ha
  obtain ⟨Ub, hUb⟩ := ex b hb
  obtain ⟨Uab, hUab⟩ := ex (a * b) (by rw [mul_pow, ha, hb, _root_.mul_one])
  obtain ⟨r₀, h₂, hp, -⟩ := SymLiftMul.symLift_mul hLaw.globalFns hA Xo.univ.t.PP.isLB hk hUa hUb hUab he
  have bij : Function.Bijective (toΓ S) :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv
  obtain ⟨r, hr⟩ := bij.2 (r₀ : Γ((ptO Xo x).left, ⊤))
  refine ⟨r, ?_, bij.1 ?_, ?_⟩
  · rw [hr, ← h₂]; exact (Units.val_pow_eq_pow_val r₀ 2).symm
  · rw [map_pow, map_one, hr]
    exact (Units.val_pow_eq_pow_val r₀ k).symm.trans (congrArg Units.val hp)
  · rintro F F₁ F₂ F₃ ⟨-, Vb, hVb, a₁⟩ ⟨-, Va, hVa, a₂⟩ ⟨-, Vab, hVab, a₃⟩ j
    obtain ⟨r₁, h₂', hp', h⟩ := SymLiftMul.symLift_mul hLaw.globalFns hA Xo.univ.t.PP.isLB hk hVa hVb hVab he
    obtain rfl : r₁ = r₀ := eq_of_sq_eq_of_odd hk (h₂'.trans h₂.symm) hp' hp
    rw [hr]
    exact h F F₁ F₂ F₃ a₁ a₂ a₃ j

end GlobalTheory.PlaceInt
end
end
