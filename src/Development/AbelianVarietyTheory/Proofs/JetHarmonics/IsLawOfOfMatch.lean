module

public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGenRosati
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartPf
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAlgHomValuationSubring

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsLawOfOfMatch
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LinkLaw

variable {V : Type} [CommRing V]

theorem jetMap_coord {κ κ' : Type} {m : ℕ} (φ : κ → MvPolynomial κ' V) (hφ : ∀ i, φ i ∈ orig V κ') (j : κ) :
    jetMap (m := m) φ hφ (Ideal.Quotient.mk _ (MvPolynomial.X j)) = Ideal.Quotient.mk _ (φ j) := by
  show Ideal.Quotient.mk _ (MvPolynomial.aeval φ (MvPolynomial.X j)) = _
  rw [MvPolynomial.aeval_X]

theorem jetSubstP_coord {κ κ' : Type} [Fintype κ'] [DecidableEq κ'] (m : ℕ) (F : κ → MvPowerSeries κ' V) (j : κ)
    (h : MvPowerSeries.constantCoeff (F j) = 0) :
    jetSubstP m (fun p => psTrunc m (F p)) (Ideal.Quotient.mk _ (MvPolynomial.X j)) = JetSer.toJet m (F j) := by
  unfold jetSubstP
  rw [jetMap_coord]
  have h0 : MvPolynomial.constantCoeff (psTrunc m (F j)) = 0 := by
    rw [Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq, MvPolynomial.constantCoeff_eq,
      MvPowerSeries.coeff_truncTotal _ (by simp), MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h]
  rw [h0, map_zero, sub_zero]
  exact congrArg (Ideal.Quotient.mk _) (Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq m (F j))

def toAt (A : Type) [CommRing A] [Algebra V A] : Chart.sp (R₀ := V) A ⟶ overAt (𝟙 (Sp V)) A :=
  Over.homMk (𝟙 _) (by dsimp; simp)

theorem read_match {G : Over (Sp V)} {κ : Type} {N m : ℕ} (z : overAt (𝟙 (Sp V)) (Jet V κ m) ⟶ G)
    (x : Chart.sp (R₀ := V) (Chart.JetR V (Fin N) m) ⟶ G) (e : Chart.JetR V (Fin N) m ≃ₐ[V] Jet V κ m)
    (he : z.left = Geo.Tor.spMap (e : Chart.JetR V (Fin N) m →+* Jet V κ m) ≫ x.left)
    {A B : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] (S : Jet V κ m →ₐ[V] B) (Φ : B →ₐ[V] A) :
    (toAt A ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) Φ) ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) S ≫ z =
      Chart.spMap (Φ.comp (S.comp (e : Chart.JetR V (Fin N) m →ₐ[V] Jet V κ m))) ≫ x := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, he, Chart.spMap_left, toAt, Formalism.L2.Pj.homAt, Over.homMk_left, Category.id_comp,
    ← Category.assoc]
  congr 1
  simp only [Geo.Tor.spMap, ← Spec.map_comp]
  rfl

theorem constantCoeff_ev {k n d : ℕ} (a : Fin k → Pt V n d) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0)
    (f : PS V k d) (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (ev a f) = 0 := by
  unfold ev
  have h1 : ∀ p : Fin k × Fin d, MvPowerSeries.constantCoeff ((fun p : Fin k × Fin d => a p.1 p.2) p) = 0 :=
    fun p => ha p.1 p.2
  have h2 : MvPowerSeries.HasSubst (fun p : Fin k × Fin d => a p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero h1
  exact MvPowerSeries.constantCoeff_subst_eq_zero (a := fun p : Fin k × Fin d => a p.1 p.2) h2 h1 hf

theorem exists_subst {σ κ : Type} [Finite σ] [Finite κ] (c : σ → MvPowerSeries κ V)
    (hc : ∀ j, MvPowerSeries.constantCoeff (c j) = 0) (m : ℕ) :
    ∃ Φ : Jet V σ m →ₐ[V] Chart.JetR V κ m,
      (∀ j, Φ (Ideal.Quotient.mk _ (MvPolynomial.X j)) = JetSer.toJet m (c j)) ∧
      ∀ g : MvPowerSeries σ V, Φ (JetSer.toJet m g) = JetSer.toJet m (MvPowerSeries.subst c g) := by
  obtain ⟨⟨Φ, hΦ⟩, hsub⟩ := (JetSer.jetAlg V κ).2.2.2.2 σ c hc m
  exact ⟨Φ, hΦ, hsub Φ hΦ⟩

theorem isLawOf_of_match {G : Over (Sp V)} [GrpObj G] {d : ℕ} (F : Fin d → PS V 2 d)
    (hF : ∀ i, MvPowerSeries.constantCoeff (F i) = 0) (xT : JetPts G (Fin 1 × Fin d))
    (law : ∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ xT m =
      (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d m (0 : Fin 2)) ≫ xT m) *
        (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d m (1 : Fin 2)) ≫ xT m))
    (x : JetSer.Fam G (Fin d)) (hM : Match (oneCol d) xT x) : JetSer.IsLawOf x F := by
  refine ⟨hF, fun n a b y z hy hz => ?_⟩
  have hab : ∀ (i : Fin 2) j, MvPowerSeries.constantCoeff ((![a, b] : Fin 2 → Pt V n d) i j) = 0 := by
    intro i j
    fin_cases i
    · exact hy.1 j
    · exact hz.1 j
  refine ⟨fun j => constantCoeff_ev _ hab _ (hF j), fun m => ?_⟩
  obtain ⟨e, he1, he2⟩ := hM m
  obtain ⟨ψa, ha1, ha2⟩ := hy.2 m
  obtain ⟨ψb, hb1, hb2⟩ := hz.2 m
  obtain ⟨Φ, hΦ, hsub⟩ := exists_subst
    (fun p : Fin 2 × Fin d => (![a, b] : Fin 2 → Pt V n d) p.1 p.2) (fun p => hab p.1 p.2) m
  have key : ∀ i : Fin 2, ∀ j, (Φ.comp ((jetCopy d m i).comp
      (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m))) (Chart.zR m j) =
      JetSer.toJet m ((![a, b] : Fin 2 → Pt V n d) i j) := by
    intro i j
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom, he1, jetCopy, jetMap_coord]
    exact hΦ (i, j)
  have ea : ψa = Φ.comp ((jetCopy d m 0).comp
      (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)) :=
    Chart.jet_ext fun j => (ha1 j).trans (key 0 j).symm
  have eb : ψb = Φ.comp ((jetCopy d m 1).comp
      (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)) :=
    Chart.jet_ext fun j => (hb1 j).trans (key 1 j).symm
  refine ⟨Φ.comp ((jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)).comp
    (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)), fun j => ?_, ?_⟩
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom, he1,
      jetSubstP_coord m (fun p : Fin 1 × Fin d => F p.2) _ (hF _)]
    exact hsub _
  · show y m * z m = _
    rw [← read_match (xT m) (x m) e he2, law m, MonObj.comp_mul,
      read_match (xT m) (x m) e he2, read_match (xT m) (x m) e he2, ← ea, ← eb, ← ha2, ← hb2]

theorem isMapOf_of_match {G : Over (Sp V)} {d : ℕ} (φ : Pt V 1 d)
    (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (xT : JetPts G (Fin 1 × Fin d)) (f : G ⟶ G)
    (hf : ∀ m, xT m ≫ f =
      Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (φ p.2)) ≫ xT m)
    (x : JetSer.Fam G (Fin d)) (hM : Match (oneCol d) xT x) : JetSer.IsMapOf x x f φ := by
  refine ⟨hφ, fun n a y hy => ?_⟩
  have hab : ∀ (i : Fin 1) j, MvPowerSeries.constantCoeff ((![a] : Fin 1 → Pt V n d) i j) = 0 := by
    intro i j
    fin_cases i
    exact hy.1 j
  refine ⟨fun j => constantCoeff_ev _ hab _ (hφ j), fun m => ?_⟩
  obtain ⟨e, he1, he2⟩ := hM m
  obtain ⟨ψa, ha1, ha2⟩ := hy.2 m
  obtain ⟨Φ, hΦ, hsub⟩ := exists_subst
    (fun p : Fin 1 × Fin d => (![a] : Fin 1 → Pt V n d) p.1 p.2) (fun p => hab p.1 p.2) m
  have key : ∀ j, (Φ.comp ((AlgHom.id V _).comp
      (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m))) (Chart.zR m j) = JetSer.toJet m (a j) := by
    intro j
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom, he1, AlgHom.id_apply]
    exact hΦ (0, j)
  have ea : ψa = Φ.comp ((AlgHom.id V _).comp
      (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)) :=
    Chart.jet_ext fun j => (ha1 j).trans (key j).symm
  have hid : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (AlgHom.id V (Jet V (Fin 1 × Fin d) m)) = 𝟙 _ := by
    apply Over.OverMorphism.ext
    exact Spec.map_id _
  refine ⟨Φ.comp ((jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (φ p.2)).comp
    (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)), fun j => ?_, ?_⟩
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom, he1,
      jetSubstP_coord m (fun p : Fin 1 × Fin d => φ p.2) _ (hφ _)]
    exact hsub _
  · show y m ≫ f = _
    rw [← read_match (xT m) (x m) e he2, ← hf m, ha2, ea, ← read_match (xT m) (x m) e he2, hid,
      Category.id_comp]
    simp only [Category.assoc]

theorem linkLaw : LinkLawSt := by
  intro E _ _ _ H V _ t d BT tg xT eT wPT hC _ _ x _ hM
  letI := H.starRing
  exact ⟨isLawOf_of_match BT.G.F BT.G.const xT hC.law x hM,
    fun α => isMapOf_of_match (BT.A.act α) (BT.A.const α) xT _ (fun m => hC.act m α) x hM⟩

end GlobalTheory.LinkLaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalJetsReindexFin
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalJetsReindexFin
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PowGerm.UnivConv

variable {V : Type} [CommRing V]

def toAt (A : Type) [CommRing A] [Algebra V A] : Chart.sp (R₀ := V) A ⟶ overAt (𝟙 (Sp V)) A :=
  Over.homMk (𝟙 _) (by simp)

def ofAt (A : Type) [CommRing A] [Algebra V A] : overAt (𝟙 (Sp V)) A ⟶ Chart.sp (R₀ := V) A :=
  Over.homMk (𝟙 _) (by simp)

theorem toAt_ofAt (A : Type) [CommRing A] [Algebra V A] : toAt (V := V) A ≫ ofAt A = 𝟙 _ :=
  Over.OverMorphism.ext (Category.comp_id _)

theorem ofAt_toAt (A : Type) [CommRing A] [Algebra V A] : ofAt (V := V) A ≫ toAt A = 𝟙 _ :=
  Over.OverMorphism.ext (Category.comp_id _)

theorem spMap_toAt {A B : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] (f : A →ₐ[V] B) :
    Chart.spMap f ≫ toAt A = toAt B ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) f :=
  Over.OverMorphism.ext ((Category.comp_id _).trans (Category.id_comp _).symm)

theorem ofAt_spMap {A B : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] (f : A →ₐ[V] B) :
    ofAt B ≫ Chart.spMap f = Formalism.L2.Pj.homAt (𝟙 (Sp V)) f ≫ ofAt A :=
  Over.OverMorphism.ext ((Category.id_comp _).trans (Category.comp_id _).symm)

def ren {κ : Type} {N : ℕ} (β : Fin N ≃ κ) (m : ℕ) : Chart.JetR V (Fin N) m ≃ₐ[V] Jet V κ m :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.renameEquiv V β) (by
    rw [Ideal.map_pow, Ideal.map_span, ← Set.range_comp, orig]
    congr 2
    ext p
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨β.symm k, by simp⟩
    · rintro ⟨i, rfl⟩
      exact ⟨β i, by simp⟩)

theorem ren_zR {κ : Type} {N : ℕ} (β : Fin N ≃ κ) (m : ℕ) (i : Fin N) :
    ren (V := V) β m (Chart.zR m i) = Ideal.Quotient.mk _ (MvPolynomial.X (β i)) := by
  show Ideal.Quotient.mk _ (MvPolynomial.rename β (MvPolynomial.X i)) = _
  rw [MvPolynomial.rename_X]

theorem aug_ren {κ : Type} {N : ℕ} (β : Fin N ≃ κ) (m : ℕ) :
    (jetAug : Jet V κ m →ₐ[V] V).comp (ren (V := V) β m).toAlgHom = Chart.jetAug V (Fin N) m :=
  Chart.jet_ext fun j => by
    rw [Chart.jetAug_zR]
    show jetAug (ren (V := V) β m (Chart.zR m j)) = 0
    rw [ren_zR]
    show MvPolynomial.aeval (fun _ : κ => (0 : V)) (MvPolynomial.X (β j)) = 0
    simp

theorem trunc_ren {κ : Type} {N : ℕ} (β : Fin N ≃ κ) (m : ℕ) :
    (jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m).comp (ren (V := V) β (m + 1)).toAlgHom =
      (ren (V := V) β m).toAlgHom.comp (Chart.jetTruncR V (Fin N) m) :=
  Chart.jet_ext fun j => rfl

theorem aug_symm {κ : Type} {N : ℕ} (β : Fin N ≃ κ) (m : ℕ) :
    (Chart.jetAug V (Fin N) m).comp (ren (V := V) β m).symm.toAlgHom = jetAug := by
  rw [← aug_ren β m]
  exact AlgHom.ext fun a => by simp

theorem trunc_symm {κ : Type} {N : ℕ} (β : Fin N ≃ κ) (m : ℕ) :
    (Chart.jetTruncR V (Fin N) m).comp (ren (V := V) β (m + 1)).symm.toAlgHom =
      (ren (V := V) β m).symm.toAlgHom.comp (jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) :=
  AlgHom.ext fun a => by
    obtain ⟨b, rfl⟩ := (ren (V := V) β (m + 1)).surjective a
    have h : jetTrunc (ren (V := V) β (m + 1) b) = ren (V := V) β m (Chart.jetTruncR V (Fin N) m b) :=
      AlgHom.congr_fun (trunc_ren (V := V) β m) b
    show Chart.jetTruncR V (Fin N) m ((ren (V := V) β (m + 1)).symm (ren (V := V) β (m + 1) b)) =
      (ren (V := V) β m).symm (jetTrunc (ren (V := V) β (m + 1) b))
    rw [h, AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]

theorem zero_eq (N m : ℕ) : Chart.jetZeroR V (Fin N) m =
    (Algebra.ofId V (Chart.JetR V (Fin N) 0)).comp (Chart.jetAug V (Fin N) m) :=
  Chart.jet_ext fun j => by
    rw [AlgHom.comp_apply, Chart.jetAug_zR, map_zero]
    show Ideal.Quotient.mk _ (MvPolynomial.X j) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one]
    exact Ideal.subset_span ⟨j, rfl⟩

end GlobalTheory.PowGerm.UnivConv

namespace GlobalTheory.PowGerm
open UnivConv

theorem univConv : UnivConvSt := by
  intro V _ G _ κ z hz N β
  obtain ⟨h1, h2, h3⟩ := hz
  refine ⟨fun m => Chart.spMap (ren (V := V) β m).symm.toAlgHom ≫ toAt _ ≫ z m, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro m
    rw [← Category.assoc, Chart.spMap_comp, trunc_symm, ← Chart.spMap_comp, Category.assoc,
      ← Category.assoc (Chart.spMap jetTrunc), spMap_toAt, Category.assoc, h1]
  · intro m
    rw [← Category.assoc, Chart.spMap_comp, zero_eq, AlgHom.comp_assoc, aug_symm, ← Chart.spMap_comp, Category.assoc,
      ← Category.assoc (Chart.spMap jetAug), spMap_toAt, Category.assoc, h2, ← Category.assoc]
    exact MonObj.comp_one _
  · intro A _ _ aug m hm y hy
    obtain ⟨φ, ⟨hφ1, hφ2⟩, hu⟩ := h3 A aug m hm (ofAt A ≫ y) (by
      rw [← Category.assoc, ← ofAt_spMap, Category.assoc, hy]
      exact MonObj.comp_one _)
    refine ⟨φ.comp (ren (V := V) β m).toAlgHom, ⟨?_, ?_⟩, ?_⟩
    · rw [← AlgHom.comp_assoc, hφ1, aug_ren]
    · have e : (φ.comp (ren (V := V) β m).toAlgHom).comp (ren (V := V) β m).symm.toAlgHom = φ :=
        AlgHom.ext fun a => by simp
      rw [← Category.assoc, Chart.spMap_comp, e, ← Category.assoc, spMap_toAt, Category.assoc, ← hφ2,
        ← Category.assoc, toAt_ofAt, Category.id_comp]
    · rintro ψ ⟨hψ1, hψ2⟩
      have e := hu (ψ.comp (ren (V := V) β m).symm.toAlgHom) ⟨by rw [← AlgHom.comp_assoc, hψ1, aug_symm], by
        rw [hψ2, ← Category.assoc (Chart.spMap ψ), Chart.spMap_comp, ← Category.assoc, ofAt_spMap, Category.assoc,
          ← Category.assoc (ofAt _), ofAt_toAt, Category.id_comp]⟩
      rw [← e]
      exact AlgHom.ext fun a => by simp
  · intro m
    refine ⟨ren β m, ren_zR β m, ?_⟩
    have e : Chart.spMap (ren (V := V) β m).toAlgHom ≫
        Chart.spMap (ren (V := V) β m).symm.toAlgHom ≫ toAt _ ≫ z m = toAt _ ≫ z m := by
      have e' : (ren (V := V) β m).toAlgHom.comp (ren (V := V) β m).symm.toAlgHom = AlgHom.id V _ :=
        AlgHom.ext fun a => by simp
      have e'' : Chart.spMap (AlgHom.id V (Jet V κ m)) = 𝟙 _ :=
        Over.OverMorphism.ext (Spec.map_id _)
      rw [← Category.assoc, Chart.spMap_comp, e', e'', Category.id_comp]
    exact (Category.id_comp _).symm.trans (congrArg CommaMorphism.left e).symm

end GlobalTheory.PowGerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalJetsReindexFinStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universalJets_reindex_fin : UnivConvSt := by
  first | exact @GlobalTheory.PowGerm.univConv | exact GlobalTheory.PowGerm.univConv | (intros; apply GlobalTheory.PowGerm.univConv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TruncationFramesLocalSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TruncationFramesLocalSeries
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PowGerm

namespace GlobalTheory.LinkEps

theorem linkEps : LinkEpsSt := by
  intro E _ _ _ H V _ _ t d FT act ph1 ph2 sy ad tg xT eT wPT hch _ _ htr j hj
  have hL := t.PP.isLB
  have hi0 : (e0 t (𝟙 (Sp V))) ⁻¹ᵁ t.PP.L.U j = ⊤ := by
    refine top_unique fun y _ => ?_
    exact hj (x := (toUnit (overAt (𝟙 (Sp V)) V)).left y) trivial
  have hW : ∀ m, LB.wchart t.PP.L
      (cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)]) (fun _ => j) = ⊤ := fun m =>
    wchart_top t (𝟙 (Sp V)) d j hi0 _ fun i => by
      rw [vec2 (fun i => jptG t (𝟙 (Sp V)) d xT m i)]; exact jpt_aug hch m i
  have hU : ∀ m, ∃ u : Γ((jOG (𝟙 (Sp V)) d m 2).left, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ (jOG (𝟙 (Sp V)) d m 2).left) (z : Z)
      (J : (Z ⟶ t.G.left) → t.PP.L.ι),
      (∀ I, J (r ≫ cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)] I) = j) →
      (val (eT m) r z J).val = gs r z ⊤ u := by
    intro m
    refine ⟨((jOG (𝟙 (Sp V)) d m 2).left.presheaf.map (homOfLE (hW m).ge).op).hom ((eT m).s (fun _ => j)).val,
      fun Z r z J hJ => ?_⟩
    exact (congrArg Units.val (val_of (eT m) r z J (fun _ => j) hJ)).trans
      ((gs_unit r z _ ((hW m).ge trivial) _).symm.trans (gs_res r z (hW m).ge trivial _).symm)
  choose U hU using hU
  have hUc : ∀ m, U m = (ρn (𝟙 (Sp V)) d 2 m).left.appTop.hom (U (m + 1)) := by
    intro m
    refine fn_ext (V := ⊤) fun y _ => ?_
    obtain ⟨J, hJ, hJi⟩ := exists_good t.PP.L hL y
      (cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)]) (fun _ => j)
      (fun _ _ _ => rfl) (fun I => Set.mem_iInter.1 ((hW m).ge (Set.mem_univ y)) I)
    have hmor : ∀ I : ULift (Finset (Fin 2)), (𝟙 _ ≫ (ρn (𝟙 (Sp V)) d 2 m).left) ≫
        cφG t ![jptG t (𝟙 (Sp V)) d xT (m + 1) (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT (m + 1) (1 : Fin 2)] I =
        cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)] I := by
      intro I
      rw [Category.id_comp, vec2 (fun i => jptG t (𝟙 (Sp V)) d xT (m + 1) i),
        vec2 (fun i => jptG t (𝟙 (Sp V)) d xT m i)]
      simp only [cφG, ← Over.comp_left]
      refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
      exact congrArg (fun f => psum t.G f I.down) (funext fun i => jpt_trunc hch m i)
    have e0' := hU m _ (𝟙 _) y J (fun I => (congrArg J (Category.id_comp _)).trans (hJi I))
    have e1 := hU (m + 1) _ (𝟙 _ ≫ (ρn (𝟙 (Sp V)) d 2 m).left) y J (fun I => (congrArg J (hmor I)).trans (hJi I))
    have e2 := (val_pull hJ (eT (m + 1)) _ _).symm.trans (val_corr hJ (htr m) (𝟙 _))
    have e3 := gs_pull (𝟙 _) (ρn (𝟙 (Sp V)) d 2 m).left y ⊤ trivial (U (m + 1))
    exact e0'.symm.trans ((congrArg Units.val e2).symm.trans (e1.trans e3.symm))
  choose a ha using fun m => (⟨_, congrArg (fun f => CommRingCat.Hom.hom f (U m))
    (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of (Jet V (Fin 2 × Fin d) m))))⟩ :
      ∃ b, toΓ (Jet V (Fin 2 × Fin d) m) b = U m)
  have hac : ∀ m, (jetTrunc : Jet V (Fin 2 × Fin d) (m + 1) →ₐ[V] _) (a (m + 1)) = a m := by
    intro m
    apply toΓ_injective
    rw [ha m, hUc m, ← ha (m + 1)]
    exact congrArg (fun f => CommRingCat.Hom.hom f (a (m + 1)))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ((jetTrunc : Jet V (Fin 2 × Fin d) (m + 1) →ₐ[V] _) :
        Jet V (Fin 2 × Fin d) (m + 1) →+* Jet V (Fin 2 × Fin d) m)))
  obtain ⟨f, hf⟩ := exists_ps_of_jets a hac
  refine ⟨f, fun m y J _ hJ => ?_⟩
  rw [hf m, ha m]
  exact hU m _ (𝟙 _) y J hJ

end GlobalTheory.LinkEps
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TruncationFramesLocalSeriesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncation_frames_local_series : LinkEpsSt := by
  first | exact @GlobalTheory.LinkEps.linkEps | exact GlobalTheory.LinkEps.linkEps | (intros; apply GlobalTheory.LinkEps.linkEps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinorStProdRange
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm

@[to_additive]
theorem minorSt_prod_range {M : Type} [CommMonoid M] {N r : ℕ} (hr : r ≤ N) (g : ℕ → M)
    (hg : ∀ s, ¬ (1 ≤ s ∧ s ≤ r) → g s = 1) :
    ∏ s ∈ Finset.range (N + 1), g s = ∏ s : Fin r, g (s.val + 1) := by
  rw [Finset.prod_range_succ', hg 0 (by omega), _root_.mul_one, Fin.prod_univ_eq_prod_range (fun s => g (s + 1)) r]
  symm
  apply Finset.prod_subset (Finset.range_subset_range.mpr hr)
  intro s _ hs
  apply hg
  rw [Finset.mem_range] at hs
  omega

theorem minorSt : MinorSt := by
  classical
  intro E _ _ _ H Dw K _ typ m n₁ n₂ hm
  let rk : (E →+* ℂ) → ℕ := fun τ => min (Dw.mult τ) (if typ τ then n₁ else n₂)
  have hrk : ∀ τ, rk τ ≤ Dw.mult τ := fun τ => min_le_left _ _
  have hrk1 : ∀ τ, typ τ → rk τ ≤ n₁ := fun τ h => (min_le_right _ _).trans (by simp [h])
  have hrk2 : ∀ τ, ¬ typ τ → rk τ ≤ n₂ := fun τ h => (min_le_right _ _).trans (by simp [h])
  have hm0 : ∀ τ s, ¬ (1 ≤ s ∧ s ≤ rk τ) → m τ s = 0 := by
    intro τ s hs
    by_contra h
    obtain ⟨h1, h2, h3⟩ := hm τ s h
    exact hs ⟨h1, le_min h2 h3⟩
  let col : ∀ τ, Fin (rk τ) → Fin (n₁ + n₂) := fun τ i =>
    if h : typ τ then Fin.castAdd n₂ (Fin.castLE (hrk1 τ h) i) else Fin.natAdd n₁ (Fin.castLE (hrk2 τ h) i)
  refine ⟨rk, hrk, col, fun τ s => m τ (s.val + 1), ?_, ?_, ?_, ?_⟩
  · intro τ i j hij
    by_cases h : typ τ
    · simp only [col, dif_pos h] at hij
      have := congrArg Fin.val hij
      exact Fin.ext (by simpa using this)
    · simp only [col, dif_neg h] at hij
      have := congrArg Fin.val hij
      exact Fin.ext (by simpa using this)
  · intro τ i
    by_cases h : typ τ
    · have := hrk1 τ h
      have := i.isLt
      simp only [col, dif_pos h, h, iff_true, Fin.val_castAdd, Fin.val_castLE]
      omega
    · simp [col, h]
  · unfold degOf
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [minorSt_sum_range (hrk τ) (fun s => s * m τ s) (fun s hs => by simp [hm0 τ s hs])]
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  · unfold minorProd FamGerm.minorsP
    rw [← Finset.prod_mul_distrib, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_prod]
    by_cases h : typ τ
    · rw [if_pos h, if_neg (not_not.mpr h), _root_.mul_one,
        minorSt_prod_range (hrk τ) _ (fun s hs => by rw [hm0 τ s hs, pow_zero])]
      refine Finset.prod_congr rfl fun s _ => ?_
      have hs : s.val + 1 ≤ Dw.mult τ ∧ s.val + 1 ≤ n₁ :=
        ⟨(Nat.succ_le_of_lt s.isLt).trans (hrk τ), (Nat.succ_le_of_lt s.isLt).trans (hrk1 τ h)⟩
      rw [dif_pos hs, map_pow, AlgHom.map_det]
      unfold leadMinor
      congr 2
      ext a i : 2
      simp only [col, dif_pos h, Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, MvPolynomial.rename_X]
      rfl
    · rw [if_neg h, if_pos h, _root_.one_mul,
        minorSt_prod_range (hrk τ) _ (fun s hs => by rw [hm0 τ s hs, pow_zero])]
      refine Finset.prod_congr rfl fun s _ => ?_
      have hs : s.val + 1 ≤ Dw.mult τ ∧ s.val + 1 ≤ n₂ :=
        ⟨(Nat.succ_le_of_lt s.isLt).trans (hrk τ), (Nat.succ_le_of_lt s.isLt).trans (hrk2 τ h)⟩
      rw [dif_pos hs, map_pow, AlgHom.map_det]
      unfold leadMinor
      congr 2
      ext a i : 2
      simp only [col, dif_neg h, Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, MvPolynomial.rename_X]
      rfl

end GlobalTheory.PowGerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilyFunctionalCoefficient
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_coef_family : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (s₀ : ℂ), IsFam lam q0 R → (haveI := FiniteDimensional.complete ℂ Wp; SideFam p.T.base.z p.T.base.π p.T.base.μW p.T.base.μN p.T.base.μG q0 R l dg) → (haveI := FiniteDimensional.complete ℂ Wq; SideFam p.T.base.z' p.T.base.π' p.T.base.μW' p.T.base.μN p.T.base.μG q0 R l' dg) → IsCoef (R 0) (l 0) (l' 0) f s₀ → s₀ ≠ 0 → ∃ (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (t : ℝ), 0 < t ∧ J 0 = (fun g => (t : ℂ) • f g) ∧ (NzOn (R 0) (l 0) ∧ NzOn (R 0) (l' 0)) ∧ (∀ ν, n1 ν ≤ q0 → NzOn (R ν) (l ν) → NzOn (R ν) (l' ν) → IsCoef (R ν) (l ν) (l' ν) (J ν) (s ν) ∧ ‖s ν‖ = dg ν) ∧ (∀ ν, ¬ (n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)) → J ν = 0) := by
  intro hH P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg f s₀ hfam hL hR hf hs₀
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  classical
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have h0 : n1 (0 : Fin (2 * P.r + P.k + 1) → ℤ) ≤ q0 := by simp [n1]
  have hDS : ∀ ν, n1 ν ≤ q0 → (R ν).IsDS (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν a : ℝ)) :=
    fun ν hν => hfam ν hν
  have hdg0 : 0 < dg 0 := (hL 0 h0).2.1
  have hsn : 0 < ‖s₀‖ := norm_pos_iff.mpr hs₀
  have hnz : NzOn (R 0) (l 0) ∧ NzOn (R 0) (l' 0) := by
    obtain ⟨m, x, y, X, hxy, -, hs⟩ := hf
    have hsm := (GlobalTheory.rep_basic_of_isDS hK _ _ _ _ (R 0) (hDS 0 h0)).2.2.2.2.1
    rw [hs] at hs₀
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs₀
    refine ⟨⟨x i, hsm _ (hxy i).1, fun h => hi ?_⟩, ⟨y i, hsm _ (hxy i).2, fun h => hi ?_⟩⟩
    · rw [h, inner_zero_left]
    · rw [h, map_zero, inner_zero_right]
  have hex : ∀ ν, ∃ (s : ℂ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)),
      (ν = 0 → F = fun g => ((dg 0 / ‖s₀‖ : ℝ) : ℂ) • f g) ∧
      (n1 ν ≤ q0 → NzOn (R ν) (l ν) → NzOn (R ν) (l' ν) → IsCoef (R ν) (l ν) (l' ν) F s ∧ ‖s‖ = dg ν) ∧
      (¬ (n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)) → F = 0) := by
    intro ν
    by_cases hν : ν = 0
    · subst hν
      refine ⟨((dg 0 / ‖s₀‖ : ℝ) : ℂ) * s₀, _, fun _ => rfl, fun _ _ _ => ⟨?_, ?_⟩, fun hn => ?_⟩
      · exact (GlobalTheory.isCoef_of_translate_smul_exists hK _ _ _ _ (R 0) Wp Wq (l 0) (l' 0) (hDS 0 h0)).2.1 f s₀ _ hf
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_pos hdg0 hsn).le]
        field_simp
      · exact absurd ⟨h0, hnz⟩ hn
    · by_cases hc : n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)
      · obtain ⟨h1, h2, h3⟩ := hc
        have e1 := GlobalTheory.bessel_nonzero_on_translates hH _ _ _ _ (R ν) Wp _ _ (l ν) (hDS ν h1) (hL ν h1).1.1 h2
        have e2 := GlobalTheory.bessel_nonzero_on_translates hH _ _ _ _ (R ν) Wq _ _ (l' ν) (hDS ν h1) (hR ν h1).1.1 h3
        obtain ⟨F, hF⟩ := (GlobalTheory.isCoef_of_translate_smul_exists hK _ _ _ _ (R ν) Wp Wq (l ν) (l' ν)
          (hDS ν h1)).2.2 e1 e2 (dg ν : ℂ)
        refine ⟨_, F, fun h => absurd h hν, fun _ _ _ => ⟨hF, ?_⟩, fun hn => absurd ⟨h1, h2, h3⟩ hn⟩
        rw [Complex.norm_real, Real.norm_of_nonneg (hL ν h1).2.1.le]
      · exact ⟨0, 0, fun h => absurd h hν, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hc, fun _ => rfl⟩
  choose s J h1 h2 h3 using hex
  exact ⟨s, J, dg 0 / ‖s₀‖, div_pos hdg0 hsn, h1 0 rfl, hnz, h2, h3⟩

end GlobalTheory
end
