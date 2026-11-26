module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ALevRe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeTranslateLocallyNoetherianBase
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ASysExt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.CoreAOf
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct

namespace UpperTheory.Gal.FiniteEtaleModels

private theorem keyC {A B V U E₁ E₂ : Scheme.{0}} {ψ : A ⟶ B} {χ : B ⟶ V} {mv : V ⟶ U} {m : U ⟶ E₂} {ψ₂ : A ⟶ V} {c : A ⟶ E₁}
    {ψ₁ : E₁ ⟶ U} {n₁ : B ⟶ U} {n₂ : B ⟶ E₂} (h₁ : n₁ = χ ≫ mv) (h₂ : n₂ = n₁ ≫ m) (h₃ : ψ ≫ χ = ψ₂) (h₄ : ψ₂ ≫ mv = c ≫ ψ₁) :
    ψ ≫ n₂ = c ≫ ψ₁ ≫ m := by
  rw [h₂, h₁, ← Category.assoc, ← Category.assoc, h₃, h₄, Category.assoc]

private theorem keyL {X A B U Y₁ Y₂ E₁ E₂ : Scheme.{0}} {ψ : A ⟶ B} {n : B ⟶ E₂} {c : A ⟶ E₁} {ψ₁ : E₁ ⟶ U} {m : U ⟶ E₂}
    {x : X ⟶ A} {j : X ⟶ Y₁} {t : Y₁ ⟶ Y₂} {l₁ : Y₁ ⟶ E₁} {l₂ : Y₂ ⟶ E₂} (h₁ : ψ ≫ n = c ≫ ψ₁ ≫ m) (h₂ : x ≫ c = j ≫ l₁)
    (h₃ : (l₁ ≫ ψ₁) ≫ m = t ≫ l₂) : (x ≫ ψ) ≫ n = ((𝟙 X ≫ j) ≫ t) ≫ l₂ := by
  rw [Category.assoc, h₁, ← Category.assoc, h₂, Category.id_comp, Category.assoc, Category.assoc, ← h₃, Category.assoc]

theorem coreA_of (hP : TrPull) (hS : TrSame) (hL : LevTr) (hR : LevRe) (hC : ClsEx) : CoreA := by
  intro q _ D R R' _ _ _ b gb β hm N κ c 𝔟₁ 𝔟₂ E₁ E₂ hno hN hNq hκ hck hle hq f u hs ρ hρ X s M₁ M₂ c₁ c₂ a₁ a₂ e₁ e₂ h₁ h₂ hg o₁ o₂ ψ
    hA hlv C₁ C₂
  have hc : c.Coprime q := Nat.Coprime.coprime_dvd_left hck (hκ.pow_left 2)
  obtain ⟨u', ψ₁, hT⟩ := GlobalTheory.T.exists_hecke_translate_locallyNoetherian_base q D R b f u c κ N hN hNq hc hκ hck hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 E₁.X E₁.s E₁.univ
  have hl := hR q D R b N 𝔟₁ 𝔟₂ ρ hle hρ _ _ u' _ (hL q D R b _ c κ N 𝔟₁ hκ hq _ _ E₁.univ u' ψ₁ E₁.lv hT E₁.isLev)
  obtain ⟨t, ⟨ht, m, hmlv⟩, -⟩ := E₂.rep E₁.X E₁.s u' _ hl
  let m₁ : ObjMap (ob hm o₁ (N * κ) c₁ e₁ h₁) E₁.univ C₁.j :=
    ⟨C₁.m.φ, C₁.m.φ₂, C₁.m.cart, C₁.m.sq, C₁.m.act, C₁.m.pol, C₁.m.eta⟩
  have hv : ∃ v : Obj b N (s ≫ spMap β), Nonempty (ObjMap v u' C₁.j) := by
    rw [← C₁.ov]; exact GlobalTheory.HTPull.exists_objMap_pull q D R b N _ _ E₁.s C₁.j u'
  obtain ⟨v, ⟨mv⟩⟩ := hv
  obtain ⟨ψ₂, hT₂, hψ₂⟩ := hP q D R b _ c κ N _ _ _ _ C₁.j E₁.univ u' ψ₁ _ v m₁ mv hT
  obtain ⟨χ, hχ⟩ := hS q D R b _ c κ N _ _ (ob hm o₁ (N * κ) c₁ e₁ h₁) (ob hm o₂ N c₂ e₂ h₂) v ψ ψ₂ hA hT₂
  obtain ⟨n₁, hn₁⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ χ mv
  obtain ⟨n₂, hn₂⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ n₁ m
  have key : ψ.left ≫ n₂.φ = C₁.m.φ ≫ ψ₁.left ≫ m.φ := keyC hn₁ hn₂ hχ hψ₂
  let B : Cls E₂ β o₂ c₂ a₂ :=
    { j := (𝟙 X ≫ C₁.j) ≫ t
      ov := by rw [Category.assoc, ht, Category.id_comp, C₁.ov]
      m := ⟨n₂.φ, n₂.φ₂, n₂.cart, n₂.sq, n₂.act, n₂.pol, n₂.eta⟩
      lv := fun y => by
        show (o₂.eta _).left ≫ n₂.φ = _
        rw [← hlv y]
        exact keyL key (C₁.lv (ρ y)) (hmlv y) }
  obtain ⟨ej, eφ⟩ := (hC q D R R' b gb β hm M₂ N c₂ a₂ 𝔟₂ e₂ h₂ hN hNq hg E₂ X s o₂).2 B C₂
  refine ⟨t, ψ₁.left ≫ m.φ, ht, ?_, ?_, ?_⟩
  · rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w]
  · rw [← ej]; show _ = (𝟙 X ≫ C₁.j) ≫ t; rw [Category.id_comp]
  · rw [← eφ]; exact key.symm

end UpperTheory.Gal.FiniteEtaleModels
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ABetaLat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

private theorem gen_facts {A : Type} [CommRing A] {a : A} {n : ℕ} {𝔟 : Ideal A} (G : IsGen a n 𝔟) :
    (n : A) ∈ 𝔟 ∧ ∀ c ∈ 𝔟, ∃ d, c * a = (n : A) * d := by
  have G' : (Ideal.span {a} ⊔ Ideal.span {(n : A)}) * 𝔟 = Ideal.span {(n : A)} := G
  have hle : (Ideal.span {a} ⊔ Ideal.span {(n : A)}) * 𝔟 ≤ 𝔟 :=
    Ideal.mul_le.mpr fun x _ y hy => 𝔟.mul_mem_left x hy
  have hN : (n : A) ∈ 𝔟 := by
    apply hle
    rw [G']
    exact Ideal.mem_span_singleton_self _
  refine ⟨hN, fun c hc => ?_⟩
  have hmem : a * c ∈ (Ideal.span {a} ⊔ Ideal.span {(n : A)}) * 𝔟 :=
    Ideal.mul_mem_mul (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)) hc
  rw [G', Ideal.mem_span_singleton] at hmem
  obtain ⟨d, hd⟩ := hmem
  exact ⟨d, by rw [mul_comm]; exact hd⟩

private theorem reindex_lattice_of_ideals {A O L : Type} [CommRing A] [Ring O] [Algebra A O] [AddCommGroup L] [Module O L]
    (cancel : ∀ k : ℕ, 0 < k → ∀ x y : L, k • x = k • y → x = y)
    (𝔟₁ 𝔟₂ : Ideal A) (W₁ W₂ : Submodule O L) (n m₁ : ℕ) (a₁ a₂ : A) (hn : 0 < n) (hm : 0 < m₁) (hle : 𝔟₁ ≤ 𝔟₂)
    (hn2 : (n : A) ∈ 𝔟₂) (hc2 : ∀ c ∈ 𝔟₂, ∃ d, c * a₂ = n * d)
    (BaseTypeSubspacesMapOntoBothSides : ∀ y : L, (∃ z, algebraMap A O a₁ • y = (n * m₁) • z) ↔ y ∈ W₁)
    (PairingFactorsThroughPeriods : ∀ x : L, (∀ c ∈ 𝔟₁, ∃ z, algebraMap A O c • x = (n * m₁) • z) →
      ∃ y z, x = algebraMap A O a₁ • y + (n * m₁) • z)
    (ProjectionSandwichLength : ∀ y : L, (∃ z, algebraMap A O a₂ • y = n • z) ↔ y ∈ W₂)
    (DegreeKernelLowerBound : ∀ x : L, (∀ c ∈ 𝔟₂, ∃ z, algebraMap A O c • x = n • z) → ∃ y z, x = algebraMap A O a₂ • y + n • z)
    (g : L →+ L) (h1 : ∀ (a : O) x, ∃ z, g (a • x) = a • g x + n • z)
    (h2 : ∀ x z, g x = n • z → ∃ v, x = n • v) (h3 : ∀ x, ∃ y z, g y = x + n • z) :
    ∃ β : L → L, (∀ x y, β (x + y) - (β x + β y) ∈ W₁) ∧ (∀ (c : O) x, β (c • x) - c • β x ∈ W₁) ∧
      (∀ y, β y ∈ W₁ ↔ y ∈ W₂) ∧
      (∀ x, (∀ c ∈ 𝔟₂, algebraMap A O c • x ∈ W₁) → ∃ y, x - β y ∈ W₁) ∧
      ∀ y, ∃ z, m₁ • g (algebraMap A O a₂ • y) = algebraMap A O a₁ • β y + (n * m₁) • z := by
  have hnm : ∀ v : L, m₁ • (n • v) = (n * m₁) • v := by
    intro v
    rw [mul_comm, mul_smul]
  have memW1 : ∀ v : L, (∃ z, algebraMap A O a₁ • v = (n * m₁) • z) → v ∈ W₁ := fun v h => (BaseTypeSubspacesMapOntoBothSides v).mp h
  have ex : ∀ y : L, ∃ y' z, m₁ • g (algebraMap A O a₂ • y) = algebraMap A O a₁ • y' + (n * m₁) • z := by
    intro y
    apply PairingFactorsThroughPeriods
    intro c hc
    obtain ⟨d, hd⟩ := hc2 c (hle hc)
    obtain ⟨z, hz⟩ := h1 (algebraMap A O c) (algebraMap A O a₂ • y)
    have e1 : algebraMap A O c • algebraMap A O a₂ • y = n • (algebraMap A O d • y) := by
      rw [smul_smul, ← map_mul, hd, map_mul, map_natCast, ← smul_smul, Nat.cast_smul_eq_nsmul]
    refine ⟨g (algebraMap A O d • y) - z, ?_⟩
    rw [e1, map_nsmul] at hz
    rw [smul_comm (algebraMap A O c) m₁, eq_sub_of_add_eq hz.symm, mul_comm n m₁, mul_smul]
    simp only [smul_sub]
  choose β z0 hβ using ex
  refine ⟨β, ?_, ?_, ?_, ?_, fun y => ⟨z0 y, hβ y⟩⟩
  · intro x y
    apply memW1
    refine ⟨z0 x + z0 y - z0 (x + y), ?_⟩
    have h := hβ (x + y)
    rw [smul_add, map_add (f := _), smul_add, hβ x, hβ y] at h
    rw [smul_sub, smul_add, eq_sub_of_add_eq h.symm]
    simp only [smul_add, smul_sub]
    abel
  · intro c x
    apply memW1
    obtain ⟨w, hw⟩ := h1 c (algebraMap A O a₂ • x)
    have hc := hβ (c • x)
    have comm1 : algebraMap A O a₂ • c • x = c • algebraMap A O a₂ • x := by
      rw [smul_smul, smul_smul, Algebra.commutes]
    have comm2 : algebraMap A O a₁ • c • β x = c • algebraMap A O a₁ • β x := by
      rw [smul_smul, smul_smul, Algebra.commutes]
    refine ⟨w - z0 (c • x) + c • z0 x, ?_⟩
    rw [comm1, hw, smul_add, hnm] at hc
    have hx' : c • (m₁ • g (algebraMap A O a₂ • x)) = c • (algebraMap A O a₁ • β x + (n * m₁) • z0 x) := by
      rw [hβ x]
    rw [smul_add, smul_comm c m₁, smul_comm c (n * m₁)] at hx'
    rw [hx'] at hc
    rw [smul_sub, comm2, eq_sub_of_add_eq hc.symm]
    simp only [smul_add, smul_sub]
    abel
  · intro y
    constructor
    · intro hy
      obtain ⟨z, hz⟩ := (BaseTypeSubspacesMapOntoBothSides (β y)).mpr hy
      have h := hβ y
      rw [hz, ← smul_add, ← hnm] at h
      have e := cancel m₁ hm _ _ h
      obtain ⟨v, hv⟩ := h2 _ _ e
      exact (ProjectionSandwichLength y).mp ⟨v, hv⟩
    · intro hy
      obtain ⟨v, hv⟩ := (ProjectionSandwichLength y).mpr hy
      apply memW1
      refine ⟨g v - z0 y, ?_⟩
      have h := hβ y
      rw [hv, map_nsmul, hnm] at h
      rw [smul_sub, eq_sub_of_add_eq h.symm]
  · intro x hx
    have hu : ∀ c ∈ 𝔟₂, ∃ z, algebraMap A O c • (algebraMap A O a₁ • x) = (n * m₁) • z := by
      intro c hc
      obtain ⟨z, hz⟩ := (BaseTypeSubspacesMapOntoBothSides _).mpr (hx c hc)
      exact ⟨z, by rw [smul_smul, ← Algebra.commutes a₁, ← smul_smul, hz]⟩
    obtain ⟨w, hw⟩ := hu _ hn2
    rw [map_natCast, Nat.cast_smul_eq_nsmul, mul_smul] at hw
    have hu1 := cancel n hn _ _ hw
    have hw2 : ∀ c ∈ 𝔟₂, ∃ z, algebraMap A O c • w = n • z := by
      intro c hc
      obtain ⟨z, hz⟩ := hu c hc
      rw [hu1, smul_comm (algebraMap A O c) m₁ w, ← hnm] at hz
      exact ⟨z, cancel m₁ hm _ _ hz⟩
    obtain ⟨y0, z0', hy0⟩ := DegreeKernelLowerBound w hw2
    obtain ⟨y1, z1, hy1⟩ := h3 y0
    obtain ⟨z2, hz2⟩ := h1 (algebraMap A O a₂) y1
    refine ⟨y1, memW1 _ ⟨z0' - algebraMap A O a₂ • z1 - z2 + z0 y1, ?_⟩⟩
    have hb := hβ y1
    rw [hz2, hy1] at hb
    simp only [smul_add] at hb
    rw [smul_comm (algebraMap A O a₂) n z1] at hb
    simp only [hnm] at hb
    rw [smul_sub, hu1, hy0, smul_add, hnm, eq_sub_of_add_eq hb.symm]
    simp only [smul_add, smul_sub]
    abel

theorem UpperTheory.Gal.FiniteEtaleModels.betaLat_holds :
    LatGen → BetaLat := by
  intro hL q _ D 𝔟₁ 𝔟₂ n m₁ a₁ a₂ hn hm hle G1 G2 g h1 h2 h3
  have cancel : ∀ k : ℕ, 0 < k → ∀ x y : D.La, k • x = k • y → x = y := by
    intro k hk x y h
    haveI := D.freeLa
    have h' : (k : ℤ) • (x - y) = 0 := by
      rw [smul_sub, natCast_zsmul, natCast_zsmul, h, sub_self]
    rcases smul_eq_zero.mp h' with h0 | h0
    · exact absurd h0 (by exact_mod_cast hk.ne')
    · exact sub_eq_zero.mp h0
  obtain ⟨BaseTypeSubspacesMapOntoBothSides, PairingFactorsThroughPeriods⟩ := hL q D a₁ (n * m₁) 𝔟₁ (Nat.mul_pos hn hm) G1
  obtain ⟨ProjectionSandwichLength, DegreeKernelLowerBound⟩ := hL q D a₂ n 𝔟₂ hn G2
  obtain ⟨hn2, hc2⟩ := gen_facts G2
  obtain ⟨β, hadd, hlin, hker, honto, hmain⟩ :=
    reindex_lattice_of_ideals cancel 𝔟₁ 𝔟₂ (wSub D 𝔟₁ 1) (wSub D 𝔟₂ 1) n m₁ a₁ a₂ hn hm hle hn2 hc2
      BaseTypeSubspacesMapOntoBothSides PairingFactorsThroughPeriods ProjectionSandwichLength DegreeKernelLowerBound g h1 h2 h3
  exact ⟨β, ⟨hadd, hlin, hker, honto⟩, hmain⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ALevTr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels
open GlobalTheory.UPel.HT.EtLev.HeckeLev

private theorem UpperTheory.Gal.FiniteEtaleModels.pow_one_of_killed_tr {p : ℕ} [Fact p.Prime] {D : Datum p} {S : Scheme.{0}} {A T : Over S}
    [GrpObj A] (act : OActN D.O A) {I : Ideal (𝓞 D.F)} {n : ℕ} (hn : (n : 𝓞 D.F) ∈ I) (t : T ⟶ A)
    (h : ∀ c ∈ I, t ≫ act.act (algebraMap (𝓞 D.F) D.O c) = 1) : t ^ n = 1 := by
  have := h _ hn
  rwa [map_natCast, act_natCast, MonObj.comp_pow, Category.comp_id] at this

theorem UpperTheory.Gal.FiniteEtaleModels.levTr_holds :
    LevTr := by
  intro q _ D R _ b f c k N 𝔟 hk hq S s o o' ψ lv hT hL
  obtain ⟨e, he⟩ := hq
  obtain ⟨hψ, hact, -, hgal, -, -⟩ := hT
  obtain ⟨hadd, hlin, hkill, hgeo⟩ := hL
  haveI := hψ
  have hnI : ((q ^ e : ℕ) : 𝓞 D.F) ∈ 𝔟 := he
  have hkn : k.Coprime (q ^ e) := Nat.Coprime.pow_right e hk
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hkn
    (pow_ne_zero e (Fact.out : q.Prime).ne_zero)
  have hmod : ∀ {Q : Type} [Monoid Q] (z : Q) (n j : ℕ), z ^ n = 1 → z ^ j = z ^ (j % n) := by
    intro Q _ z n j hz
    exact pow_eq_pow_mod j hz
  have hlv0 : lv 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.mp this.symm
  obtain ⟨φ, hφm, hψφ⟩ := GlobalTheory.HomDescent.exists_desc S o.A o'.A o.A (heckeSubA o f N) ψ hψ hgal
    (𝟙 o.A ^ k) (isMonHom_idPow o.A k) (fun h hh => by
      rw [MonObj.comp_pow, Category.comp_id]
      exact HeckeAd.pow_eq_one_of_mem o f h hh)
  haveI := hφm
  haveI : Epi ψ := by
    haveI := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hgal
    exact Over.epi_of_epi_left ψ
  have hφψ : φ ≫ ψ = 𝟙 o'.A ^ k := by
    apply (cancel_epi ψ).1
    rw [← Category.assoc, hψφ, pow_comp_hom, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  have hφact : ∀ a : D.O, φ ≫ o.act.act a = o'.act.act a ≫ φ := by
    intro a
    haveI := o.act.hom a
    apply (cancel_epi ψ).1
    rw [← Category.assoc, hψφ, ← Category.assoc, ← hact a, Category.assoc, hψφ, pow_comp_hom,
      MonObj.comp_pow, Category.id_comp, Category.comp_id]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    beta_reduce
    rw [hadd, MonObj.mul_comp]
  · intro a x
    beta_reduce
    rw [hlin, Category.assoc, hact, Category.assoc]
  · intro x hx
    beta_reduce
    rw [hkill x hx, MonObj.one_comp]
  · intro K _ _ x
    obtain ⟨hA, hB⟩ := hgeo K x
    constructor
    · intro y hy
      beta_reduce at hy
      apply hA
      have hPk : (toUnit (Over.mk x) ≫ lv y) ^ k = 1 := by
        calc (toUnit (Over.mk x) ≫ lv y) ^ k = (toUnit (Over.mk x) ≫ lv y) ≫ 𝟙 o.A ^ k := by
              rw [MonObj.comp_pow, Category.comp_id]
          _ = (toUnit (Over.mk x) ≫ lv y ≫ ψ) ≫ φ := by rw [← hψφ]; simp only [Category.assoc]
          _ = 1 := by rw [hy, MonObj.one_comp]
      have hPn : (toUnit (Over.mk x) ≫ lv y) ^ (q ^ e) = 1 :=
        UpperTheory.Gal.FiniteEtaleModels.pow_one_of_killed_tr o.act hnI _ (fun c hc => by
          rw [Category.assoc, ← hlin,
            hkill _ (Submodule.subset_span ⟨c, by rw [pow_one]; exact hc, y, rfl⟩), MonObj.comp_one])
      calc toUnit (Over.mk x) ≫ lv y = (toUnit (Over.mk x) ≫ lv y) ^ 1 := (pow_one _).symm
        _ = (toUnit (Over.mk x) ≫ lv y) ^ (1 % q ^ e) := hmod _ _ 1 hPn
        _ = (toUnit (Over.mk x) ≫ lv y) ^ (k * m % q ^ e) := by rw [hm]
        _ = (toUnit (Over.mk x) ≫ lv y) ^ (k * m) := (hmod _ _ _ hPn).symm
        _ = 1 := by rw [pow_mul, hPk, one_pow]
    · intro g hg
      have hg0 : ∀ c ∈ 𝔟 ^ 1, (g ≫ φ) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
        intro c hc
        rw [Category.assoc, hφact, ← Category.assoc, hg c hc, MonObj.one_comp]
      obtain ⟨y0, hy0⟩ := hB (g ≫ φ) hg0
      have hgk : g ^ k = toUnit (Over.mk x) ≫ lv y0 ≫ ψ := by
        rw [← Category.assoc, hy0, Category.assoc, hφψ, MonObj.comp_pow, Category.comp_id]
      have hgn : g ^ (q ^ e) = 1 :=
        UpperTheory.Gal.FiniteEtaleModels.pow_one_of_killed_tr o'.act hnI g (fun c hc => hg c (by rw [pow_one]; exact hc))
      refine ⟨m • y0, ?_⟩
      show toUnit (Over.mk x) ≫ lv (m • y0) ≫ ψ = g
      rw [map_nsmul_pow lv hadd hlv0 m y0, pow_comp_hom, MonObj.comp_pow, ← hgk, ← pow_mul,
        hmod g _ _ hgn, hm, ← hmod g _ 1 hgn, pow_one]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.AGalOfKer
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.galOfKer_holds :
    GalOfKer := by
  intro S A B _ _ _ _ hA hB ψ ψ' κ hψ hψ' h1 h2 hκ H hfin hHψ hinj hsurj
  haveI := hA
  haveI := hB
  obtain ⟨-, haF, haE, -⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective S A κ hA hκ
  obtain ⟨-, -, hbE, hbS⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective S B κ hB hκ
  haveI : IsProper A.hom := IsAbelianScheme.proper
  haveI : IsProper B.hom := IsAbelianScheme.proper
  haveI : Smooth B.hom := IsAbelianScheme.smooth
  haveI : IsSeparated (ψ'.left ≫ A.hom) := by rw [Over.w ψ']; infer_instance
  haveI : IsSeparated ψ'.left := IsSeparated.of_comp ψ'.left A.hom
  haveI : LocallyOfFiniteType (ψ'.left ≫ A.hom) := by rw [Over.w ψ']; infer_instance
  haveI : LocallyOfFiniteType ψ'.left := locallyOfFiniteType_of_comp ψ'.left A.hom
  haveI : IsFinite (ψ.left ≫ ψ'.left) := by rw [← Over.comp_left, h1]; exact haF
  haveI : Etale (ψ.left ≫ ψ'.left) := by rw [← Over.comp_left, h1]; exact haE
  haveI : Etale (ψ'.left ≫ ψ.left) := by rw [← Over.comp_left, h2]; exact hbE
  haveI : Surjective (ψ'.left ≫ ψ.left) := by rw [← Over.comp_left, h2]; exact hbS
  haveI : FormallyUnramified ψ'.left := FormallyUnramified.of_comp ψ'.left ψ.left
  refine ⟨hfin, ?_, ?_, ?_, IsFinite.of_comp ψ.left ψ'.left, Etale.of_comp ψ.left ψ'.left,
    Surjective.of_comp ψ'.left ψ.left, ?_⟩
  · simp [Hecke.PullHecke.transl_one]
  · intro a c
    simp [Hecke.PullHecke.transl_mul]
  · intro a
    have ht : Hecke.transl (a : 𝟙_ (Over S) ⟶ A) ≫ ψ = ψ := by
      have e := Hecke.Comp.comp_transl (𝟙 A) (a : 𝟙_ (Over S) ⟶ A)
      rw [Category.id_comp] at e
      rw [e, MonObj.mul_comp, Category.id_comp, Category.assoc, hHψ a a.2, comp_one, _root_.mul_one]
    rw [← Over.comp_left, ht]
  · intro K _ _ y y' hyy
    have hz : y' ≫ A.hom = y ≫ A.hom := by
      rw [← Over.w ψ]
      simp only [← Category.assoc, hyy]
    let Y0 : Over.mk (y ≫ A.hom) ⟶ A := Over.homMk y rfl
    let Y1 : Over.mk (y ≫ A.hom) ⟶ A := Over.homMk y' hz
    have hY : Y1 ≫ ψ = Y0 ≫ ψ := by
      ext
      simp [Y0, Y1, hyy]
    have hg : (Y1 * Y0⁻¹) ≫ ψ = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hY, _root_.mul_inv_cancel]
    obtain ⟨g₀, hg₀H, hgg₀⟩ := hsurj K (y ≫ A.hom) (Y1 * Y0⁻¹) hg
    have key : ∀ h : 𝟙_ (Over S) ⟶ A, (y ≫ Over.Hom.left (Hecke.transl h) = y' ↔
        toUnit (Over.mk (y ≫ A.hom)) ≫ h = Y1 * Y0⁻¹) := by
      intro h
      have e := Hecke.Comp.comp_transl Y0 h
      constructor
      · intro hh
        have e' : Y0 ≫ Hecke.transl h = Y1 := by
          ext
          simpa [Y0, Y1] using hh
        rw [e'] at e
        rw [e, mul_comm Y0, _root_.mul_assoc, _root_.mul_inv_cancel, _root_.mul_one]
      · intro hh
        rw [hh, mul_comm Y1, ← _root_.mul_assoc, _root_.mul_inv_cancel, _root_.one_mul] at e
        have := congrArg Over.Hom.left e
        simpa [Y0, Y1] using this
    refine ⟨⟨g₀, hg₀H⟩, (key g₀).mpr hgg₀.symm, ?_⟩
    rintro ⟨h, hH⟩ hh
    have h3 := (key h).mp hh
    apply Subtype.ext
    have h4 : toUnit (Over.mk (y ≫ A.hom)) ≫ (h * g₀⁻¹) = 1 := by
      rw [MonObj.comp_mul, GrpObj.comp_inv, h3, hgg₀, _root_.mul_inv_cancel]
    exact mul_inv_eq_one.mp (hinj K (y ≫ A.hom) _ (H.mul_mem hH (H.inv_mem hg₀H)) h4)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ATrSame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels
open GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Hecke.Comp

theorem UpperTheory.Gal.FiniteEtaleModels.trSame_holds :
    TrSame := by
  intro q _ D R _ b f c k N S s o o₁ o₂ ψ₁ ψ₂ h₁ h₂
  obtain ⟨m₁, a₁, e₁, g₁, l₁, -⟩ := h₁
  obtain ⟨m₂, a₂, e₂, g₂, l₂, -⟩ := h₂
  have ep₁ := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover g₁
  have ep₂ := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover g₂
  have kill : ∀ {X : Over S} [GrpObj X] (ψ : o.A ⟶ X), IsMonHom ψ →
      GlobalTheory.ZM.IsGaloisCover (↥(heckeSubA o f N)) (fun h ↦ Over.Hom.left (transl h.1)) (Over.Hom.left ψ) →
      ∀ h ∈ heckeSubA o f N, h ≫ ψ = 1 := by
    intro X _ ψ hψ g h hh
    exact comp_eq_one_of_transl ψ h (g.inv ⟨h, hh⟩)
  obtain ⟨φ, hφ, hφc⟩ := GlobalTheory.HomDescent.exists_desc S o.A o₁.A o₂.A _ ψ₁ m₁ g₁ ψ₂ m₂ (kill ψ₂ m₂ g₂)
  obtain ⟨φ', hφ', hφ'c⟩ := GlobalTheory.HomDescent.exists_desc S o.A o₂.A o₁.A _ ψ₂ m₂ g₂ ψ₁ m₁ (kill ψ₁ m₁ g₁)
  have canc : ∀ {X Y : Over S} (π : X ⟶ Y) [Epi π.left] {Z : Over S} (u v : Y ⟶ Z), π ≫ u = π ≫ v → u = v := by
    intro X Y π _ Z u v h
    ext1
    rw [← cancel_epi π.left, ← Over.comp_left, h, Over.comp_left]
  let e : o₁.A ≅ o₂.A :=
    { hom := φ, inv := φ',
      hom_inv_id := canc ψ₁ _ _ (by rw [reassoc_of% hφc, hφ'c, Category.comp_id])
      inv_hom_id := canc ψ₂ _ _ (by rw [reassoc_of% hφ'c, hφc, Category.comp_id]) }
  haveI : IsMonHom e.hom := hφ
  haveI : IsMonHom ψ₁ := m₁
  haveI : IsMonHom ψ₂ := m₂
  have hc : ψ₁.left ≫ φ.left = ψ₂.left := by rw [← Over.comp_left, hφc]
  refine ⟨⟨φ.left, sq2 φ, isGrpPullback_of_iso e, ⟨grpSchemeSquareProductMap_fst φ, grpSchemeSquareProductMap_snd φ⟩, ?_, ?_, ?_⟩, hc⟩
  · intro a
    have t₁ := congrArg Over.Hom.left (a₁ a)
    have t₂ := congrArg Over.Hom.left (a₂ a)
    simp only [Over.comp_left] at t₁ t₂
    rw [← cancel_epi ψ₁.left, ← Category.assoc, ← t₁, Category.assoc, hc, reassoc_of% hc, ← t₂]
  · have hP := o₂.isLB
    have Z : ∀ (u : o₁.A.left ⟶ (G2 o₁.A).left) (v : o₂.A.left ⟶ (G2 o₂.A).left),
        u ≫ sq2 φ = φ.left ≫ v → (∃ t : (o₂.P.pull v).Gen, t.IsGen) →
        ∃ t : ((o₂.P.pull (sq2 φ)).pull u).Gen, t.IsGen := by
      intro u v huv hv
      rw [← GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB (pull_isLB hP _) _),
        GlobalTheory.CechPic.cls_pull (pull_isLB hP _), GlobalTheory.CechPic.cls_pull hP, ← GlobalTheory.CechPic.pull_comp, huv,
        GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull hP v (pull_isLB hP v),
        (GlobalTheory.CechPic.cls_eq_zero_iff _).2 hv, map_zero]
    obtain ⟨l₁⟩ := l₁
    obtain ⟨l₂⟩ := l₂
    have lA := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_linComb o.isLB (fun _ : Fin (k ^ 2 / c) ↦ 𝟙 _) (fun _ ↦ (1 : ℤ))
    have Y : LBIso (o₂.P.pull (sq2 ψ₂)) ((o₂.P.pull (sq2 φ)).pull (sq2 ψ₁)) := by
      rw [← GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _),
        GlobalTheory.CechPic.cls_pull hP, GlobalTheory.CechPic.cls_pull (pull_isLB hP _), GlobalTheory.CechPic.cls_pull hP,
        ← GlobalTheory.CechPic.pull_comp, ← grpSchemeSquareProductMap_comp, hφc]
    refine GlobalTheory.T.pullback_prod_injective_birigidified_galois_isogeny S o.A o₁.A _ ψ₁ o.ab o₁.ab m₁ g₁ o₁.P (o₂.P.pull (sq2 φ)) o₁.isLB
      (pull_isLB o₂.isLB _) o₁.rig₁ o₁.rig₂ ?_ ?_ ?_
    · exact Z _ _ (lift_one_id_grpSchemeSquareProductMap φ) o₂.rig₁
    · exact Z _ _ (lift_id_one_grpSchemeSquareProductMap φ) o₂.rig₂
    · exact LBIso.trans (pull_isLB o₁.isLB _) lA (pull_isLB (pull_isLB hP _) _) (LBIso.symm l₁)
        (LBIso.trans lA (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) l₂ Y)
  · intro y
    rw [e₁ y, e₂ y, Over.comp_left, Over.comp_left, Category.assoc, hc, Category.id_comp]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ADictP
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels
open GlobalTheory GlobalTheory.HeckeApprox

namespace UpperTheory.Gal.FiniteEtaleModels.SimilarityMultiplicityForm

variable {p : ℕ} [Fact p.Prime]

private def Mult (g : ℤ) (a : AfP p) : Prop := ∃ t : AfP p, IsIntAf t ∧ a = (g : AfP p) * t

private theorem Mult.add {g : ℤ} {a b : AfP p} (ha : Mult g a) (hb : Mult g b) : Mult g (a + b) := by
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  exact ⟨s + t, isInt_add hs ht, by rw [mul_add]⟩

private theorem Mult.zero (g : ℤ) : Mult g (0 : AfP p) := by
  refine ⟨0, ?_, by rw [mul_zero]⟩
  simpa using isInt_natCast (p := p) 0

private theorem Mult.neg {g : ℤ} {a : AfP p} (ha : Mult g a) : Mult g (-a) := by
  obtain ⟨t, ht, rfl⟩ := ha
  refine ⟨-t, ?_, by rw [mul_neg]⟩
  simpa using isInt_sub (isInt_natCast (p := p) 0) ht

private theorem mult_form (D : Datum p) (g : ℤ) (hg : ∀ x y, g ∣ D.EF x y) {v w : AfP p ⊗[ℚ] VQ D}
    (hv : v ∈ LaHat D) (hw : w ∈ LaHat D) : Mult g (fAf D v w) := by
  have gen : ∀ (a b : AfP p) (x y : D.La), IsIntAf a → IsIntAf b →
      Mult g (fAf D (a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x)) (b ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] y))) := by
    intro a b x y ha hb
    obtain ⟨k, hk⟩ := hg x y
    refine ⟨a * b * k, isInt_mul (isInt_mul ha hb) (isInt_intCast k), ?_⟩
    have e1 : a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x) = a • inAf D x := by
      rw [inAf, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    have e2 : b ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] y) = b • inAf D y := by
      rw [inAf, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [e1, e2, LinearMap.map_smul₂, LinearMap.map_smul, form_inAf, hk]
    push_cast
    simp only [smul_eq_mul]
    ring
  have step : ∀ (b : AfP p) (y : D.La), IsIntAf b → ∀ u ∈ LaHat D,
      Mult g (fAf D u (b ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] y))) := by
    intro b y hb u hu
    unfold LaHat at hu
    induction hu using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, x, ha, rfl⟩ := hz
      exact gen a b x y ha hb
    | zero =>
      simpa using Mult.zero (p := p) g
    | add z z' _ _ h1 h2 =>
      rw [map_add (f := _), LinearMap.add_apply]
      exact Mult.add h1 h2
    | neg z _ h =>
      rw [map_neg, LinearMap.neg_apply]
      exact Mult.neg h
  unfold LaHat at hw
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, y, hb, rfl⟩ := hz
    exact step b y hb v hv
  | zero =>
    simpa using Mult.zero (p := p) g
  | add z z' _ _ h1 h2 =>
    rw [map_add (f := _)]
    exact Mult.add h1 h2
  | neg z _ h =>
    rw [map_neg]
    exact Mult.neg h

private theorem form_ne (D : Datum p) : ∃ x y, D.EF x y ≠ 0 := by
  haveI := D.freeLa
  haveI := D.finLa
  have hrank : 0 < Module.finrank ℤ D.La := by
    rw [D.rankLa]
    exact Nat.mul_pos (Nat.mul_pos D.m_pos D.n_pos) Module.finrank_pos
  haveI : Nontrivial D.La := Module.nontrivial_of_finrank_pos hrank
  obtain ⟨x, hx⟩ := exists_ne (0 : D.La)
  have hne : D.EF x ≠ 0 := fun h => hx (D.nondeg (by rw [h, map_zero]))
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp hne
  exact ⟨x, y, by simpa using hy⟩

private theorem int_of_sim (D : Datum p) (h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)) (mu : AfP p)
    (hint : ∀ v ∈ LaHat D, h₀ v ∈ LaHat D) (hsim : ∀ v w, fAf D (h₀ v) (h₀ w) = mu * fAf D v w) : IsIntAf mu := by
  let I : Ideal ℤ := Ideal.span {z | ∃ x y, D.EF x y = z}
  let g : ℤ := Submodule.IsPrincipal.generator I
  have hI : Ideal.span {g} = I := Ideal.span_singleton_generator I
  have hg : ∀ x y, g ∣ D.EF x y := by
    intro x y
    have h : D.EF x y ∈ I := Ideal.subset_span ⟨x, y, rfl⟩
    rw [← hI, Ideal.mem_span_singleton] at h
    exact h
  have hg0 : g ≠ 0 := by
    intro h0
    obtain ⟨x, y, hxy⟩ := form_ne D
    have h := hg x y
    rw [h0, zero_dvd_iff] at h
    exact hxy h
  have hP : ∀ z ∈ I, Mult g (mu * (z : AfP p)) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, y, rfl⟩ := hz
      rw [← form_inAf, ← hsim]
      exact mult_form D g hg (hint _ (inAf_mem D x)) (hint _ (inAf_mem D y))
    | zero =>
      simpa using Mult.zero (p := p) g
    | add a b _ _ ha hb =>
      rw [Int.cast_add, mul_add]
      exact Mult.add ha hb
    | smul k a _ ha =>
      obtain ⟨t, ht, he⟩ := ha
      refine ⟨k * t, isInt_mul (isInt_intCast k) ht, ?_⟩
      rw [smul_eq_mul, Int.cast_mul, mul_left_comm, he]
      ring
  obtain ⟨t, ht, he⟩ := hP g (Submodule.IsPrincipal.generator_mem I)
  have hu : IsUnit (g : AfP p) := by
    have hq : IsUnit (algebraMap ℚ (AfP p) (g : ℚ)) :=
      (isUnit_iff_ne_zero.mpr (by exact_mod_cast hg0)).map _
    simpa using hq
  have hmt : mu = t := hu.mul_left_cancel (by rw [mul_comm (g : AfP p) mu, he])
  rw [hmt]
  exact ht

end UpperTheory.Gal.FiniteEtaleModels.SimilarityMultiplicityForm

open UpperTheory.Gal.FiniteEtaleModels.SimilarityMultiplicityForm in
theorem UpperTheory.Gal.FiniteEtaleModels.dictP_holds :
    MultUnit → DictP := by
  intro hMU p _ D G L h κ c' hκ hκp hc' hI hpre hsim
  obtain ⟨_, hMU2⟩ := hMU p D G L
  obtain ⟨t, t', ht, ht', htt, hct⟩ := hsim
  let h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) := κ • L.actG h⁻¹
  have hinv : ∀ v, L.actG h⁻¹ (L.actG h v) = v := by
    intro v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hint : ∀ v ∈ LaHat D, h₀ v ∈ LaHat D := by
    intro v hv
    obtain ⟨v', hv', he⟩ := hpre v hv
    have e : h₀ v = v' := by
      simp only [h₀, LinearMap.smul_apply]
      rw [← map_nsmul, ← he, hinv]
    rw [e]
    exact hv'
  obtain ⟨f, hf⟩ := T.lattice_endomorphism_integral_approximation p D h₀ hint
  have hs0 := T.harrisTaylor_action_form_eq_similitude_mul p D G L h⁻¹
  have hone : ((h⁻¹ : G.GAf).val.2 : AfP p) * (h.val.2 : AfP p) = 1 := by simp
  let mu : AfP p := (κ : AfP p) ^ 2 * ((h⁻¹ : G.GAf).val.2 : AfP p)
  have hsim0 : ∀ v w, fAf D (h₀ v) (h₀ w) = mu * fAf D v w := by
    intro v w
    simp only [h₀, LinearMap.smul_apply, mu]
    rw [map_nsmul, map_nsmul, LinearMap.smul_apply]
    dsimp only [fAf]
    rw [hs0]
    simp only [nsmul_eq_mul]
    ring
  have hmu : IsIntAf mu := int_of_sim D h₀ mu hint hsim0
  have hprod : mu * ((c' : AfP p) * t) = ((κ ^ 2 : ℕ) : AfP p) := by
    rw [← hct]
    simp only [mu]
    rw [_root_.mul_assoc, hone, _root_.mul_one]
    push_cast
    rfl
  obtain ⟨c, ε, ε', hcp, _, hε, hε', hεε, hmuc⟩ :=
    T.exists_divisor_mul_integralUnit_finiteAdelesAwayP p mu ((c' : AfP p) * t) (κ ^ 2) (pow_pos hκ 2) (Nat.Coprime.pow_left 2 hκp) hmu
      (isInt_mul (isInt_natCast c') ht) hprod
  have hcc : κ ^ 2 = c * c' := by
    refine hMU2 (κ ^ 2) (c * c') (ε * t) (ε' * t') (Nat.Coprime.pow_left 2 hκp)
      (Nat.Coprime.mul_left hcp hc') (isInt_mul hε ht) (isInt_mul hε' ht') ?_ ?_
    · calc ε * t * (ε' * t') = (ε * ε') * (t * t') := by ring
        _ = 1 := by rw [hεε, htt, _root_.mul_one]
    · rw [← hprod, hmuc]
      push_cast
      ring
  have hcomm : ∀ (a : D.O) v, h₀ (actAf D a v) = actAf D a (h₀ v) := by
    intro a v
    simp only [h₀, LinearMap.smul_apply]
    rw [actG_actAf, map_nsmul]
  have hlin : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, (f n) (a • x) = a • (f n) x + n • z := by
    intro n hn hnp a x
    obtain ⟨w1, hw1, he1⟩ := hf n hn hnp (a • x)
    obtain ⟨w2, hw2, he2⟩ := hf n hn hnp x
    have key : inAf D ((f n) (a • x) - a • (f n) x) = n • (actAf D a w2 - w1) := by
      rw [inAf_sub, ← actAf_inAf, smul_sub]
      have e3 : inAf D ((f n) (a • x)) = actAf D a (h₀ (inAf D x)) - n • w1 := by
        rw [← hcomm, actAf_inAf, he1, add_sub_cancel_right]
      rw [e3, he2, map_add (f := _), map_nsmul]
      abel
    have hmem : actAf D a w2 - w1 ∈ LaHat D := (LaHat D).sub_mem (actAf_mem_laHat D a hw2) hw1
    obtain ⟨z, hz⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ n hn hnp _ hmem key
    exact ⟨z, by rw [← hz, add_sub_cancel]⟩
  have hcompat : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → ∀ x : D.La, ∃ z, (f (n * m)) x = (f n) x + n • z := by
    intro n m hn hm hnmp x
    have hnp : n.Coprime p := Nat.Coprime.coprime_mul_right hnmp
    obtain ⟨w1, hw1, he1⟩ := hf (n * m) (Nat.mul_pos hn hm) hnmp x
    obtain ⟨w2, hw2, he2⟩ := hf n hn hnp x
    have key : inAf D ((f (n * m)) x - (f n) x) = n • (w2 - m • w1) := by
      have e3 : inAf D ((f (n * m)) x) = inAf D ((f n) x) + n • w2 - (n * m) • w1 := by
        rw [← he2, he1, add_sub_cancel_right]
      rw [inAf_sub, e3, smul_sub, ← mul_smul]
      abel
    have hmem : w2 - m • w1 ∈ LaHat D := (LaHat D).sub_mem hw2 ((LaHat D).nsmul_mem hw1 m)
    obtain ⟨z, hz⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ n hn hnp _ hmem key
    exact ⟨z, by rw [← hz, add_sub_cancel]⟩
  obtain ⟨u, hu1, hu2⟩ := T.integral_adele_unit_congruence_sequence p ε ε' hε hε' hεε
  have hform : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y : D.La, (n : ℤ) ∣ D.EF ((f n) x) ((f n) y) - c * u n * D.EF x y := by
    intro n hn hnp x y
    obtain ⟨_, β, hβ, hεβ⟩ := hu2 n hn hnp
    obtain ⟨w1, hw1, he1⟩ := hf n hn hnp x
    obtain ⟨w2, hw2, he2⟩ := hf n hn hnp y
    have ex : inAf D ((f n) x) = h₀ (inAf D x) - n • w1 := by rw [he1, add_sub_cancel_right]
    have ey : inAf D ((f n) y) = h₀ (inAf D y) - n • w2 := by rw [he2, add_sub_cancel_right]
    have hA := formInt_laHat p D _ _ (hint _ (inAf_mem D x)) hw2
    have hB := formInt_laHat p D _ _ hw1 (hint _ (inAf_mem D y))
    have hC := formInt_laHat p D _ _ hw1 hw2
    refine IntDvdAdele.dvd_of_eq_mul_int p n hn hnp _
      ((c : AfP p) * β * (D.EF x y : AfP p) - fAf D (h₀ (inAf D x)) w2 - fAf D w1 (h₀ (inAf D y))
        + (n : AfP p) * fAf D w1 w2)
      (isInt_add (isInt_sub (isInt_sub (isInt_mul (isInt_mul (isInt_natCast c) hβ) (isInt_intCast _)) hA) hB)
        (isInt_mul (isInt_natCast n) hC)) ?_
    push_cast
    rw [← form_inAf D ((f n) x) ((f n) y), ← form_inAf D x y, ex, ey]
    simp only [map_sub, LinearMap.sub_apply, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
    rw [hsim0, hmuc, hεβ]
    ring
  clear hs0 hone hpre hMU2 htt hprod
  refine ⟨f, u, c, hcc.symm, ?_, ?_⟩
  · have hIh : ∀ v ∈ LaHat D, L.actG h v ∈ LaHat D := hI
    refine ⟨hlin, fun n m hn hm hnm => ⟨hcompat n m hn hm hnm, hu1 n m hn hm hnm⟩,
      fun n hn hnp => ⟨(hu2 n hn hnp).1, hform n hn hnp⟩, ?_⟩
    intro n hn hnp x
    change D.La at x
    obtain ⟨y, w, hw, hyw⟩ := exists_inAf_add_nsmul_of_mem_laHat p D n hn hnp _ (hIh _ (inAf_mem D x))
    obtain ⟨w', hw', he'⟩ := hf n hn hnp y
    have hh : h₀ (L.actG h (inAf D x)) = κ • inAf D x := by
      simp only [h₀, LinearMap.smul_apply]
      rw [hinv]
    rw [hyw, map_add (f := _), map_nsmul, he'] at hh
    have key : inAf D ((f n) y - κ • x) = n • (-(w' + h₀ w)) := by
      rw [inAf_sub, inAf_nsmul, ← hh, smul_neg, smul_add]
      abel
    have hmem : -(w' + h₀ w) ∈ LaHat D := (LaHat D).neg_mem ((LaHat D).add_mem hw' (hint w hw))
    obtain ⟨z, hz⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ n hn hnp _ hmem key
    exact ⟨y, z, eq_add_of_sub_eq' hz⟩
  · intro n hn hnp x
    obtain ⟨w, hw, he⟩ := hf n hn hnp x
    refine ⟨w, hw, ?_⟩
    rw [← he]
    simp only [h₀, LinearMap.smul_apply]

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ATrKer
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

private theorem ev_eq {Λ Q : Type} [AddCommGroup Λ] [Group Q] (E : ℕ → Λ → Q)
    (add : ∀ n x y, E n (x + y) = E n x * E n y) (ker : ∀ n, 0 < n → ∀ x, E n x = 1 ↔ ∃ y, x = n • y)
    (tower : ∀ n m, 0 < n → 0 < m → ∀ x, E (n * m) x ^ m = E n x) {κ m N : ℕ} (hN : N = κ * m) (hκ : 0 < κ)
    (hm : 0 < m) {a b c : Λ} (h : a = b + κ • c) : E κ a = E N (m • b) := by
  have hz : ∀ n, E n 0 = 1 := by
    intro n
    have h0 := add n 0 0
    rw [_root_.add_zero] at h0
    exact (_root_.mul_eq_left.mp h0.symm)
  have hpow : ∀ n (k : ℕ) x, E n (k • x) = E n x ^ k := by
    intro n k x
    induction k with
    | zero => simp [hz]
    | succ k ih => rw [succ_nsmul, add, ih, _root_.pow_succ]
  have hc : E κ (κ • c) = 1 := (ker κ hκ _).mpr ⟨c, rfl⟩
  rw [h, add, hc, _root_.mul_one, hN, hpow, tower κ m hκ hm]

theorem UpperTheory.Gal.FiniteEtaleModels.trKer_holds :
    TrKer := by
  intro p _ D G L R _ _ gb h X s M₁ M₂ o' o ψ hT n κ c₁ hM hsurj f hf Ω _ _ z g hg hgk
  obtain ⟨hM3, hMc⟩ := M₁.2
  have hne : (M₁ : ℕ) ≠ 0 := by omega
  rw [hM] at hne hMc
  have hn0 : 0 < n := Nat.pos_of_ne_zero (fun h0 => hne (by simp [h0]))
  have hκ0 : 0 < κ := Nat.pos_of_ne_zero (fun h0 => hne (by simp [h0]))
  have hc0 : 0 < c₁ := Nat.pos_of_ne_zero (fun h0 => hne (by simp [h0]))
  have hκc : κ.Coprime p := Nat.Coprime.coprime_dvd_left ⟨n * c₁, by ring⟩ hMc
  have hnκc : (n * κ).Coprime p := Nat.Coprime.coprime_dvd_left ⟨c₁, rfl⟩ hMc
  obtain ⟨β, hβ⟩ := GlobalTheory.UPel.HT.GenCmp.exists_spMap (z ≫ s)
  obtain ⟨I', I'', h1, h2, hev⟩ := hT.2.2.2.2 Ω z β hβ
  obtain ⟨a, ha⟩ := (I'.onto κ hκ0 g).mp hgk
  have h0 : I''.ev κ 0 = 1 := (I''.ker κ hκ0 0).mpr ⟨0, by simp⟩
  have hψ : I'.ev κ a ≫ ψ = I''.ev κ 0 := by rw [ha, hg, h0]
  obtain ⟨v, hv, hav⟩ := (hev κ hκ0 hκc a 0).mp hψ
  have hin0 : inAf D 0 = 0 := by
    have := GlobalTheory.HeckeApprox.inAf_sub D 0 0
    rw [_root_.sub_zero, _root_.sub_self] at this
    exact this
  rw [hin0, _root_.zero_add] at hav
  have hinv : ∀ y, L.actG h⁻¹ (L.actG h y) = y := by
    intro y
    rw [← Module.End.mul_apply, ← map_mul, _root_.inv_mul_cancel, map_one, Module.End.one_apply]
  obtain ⟨x, w, hw, hvx⟩ := GlobalTheory.T.latticeCompletion_eq_latticeVector_add_nsmul p D (n * κ) (Nat.mul_pos hn0 hκ0) hnκc v hv
  obtain ⟨w', hw', hfx⟩ := hf x
  obtain ⟨w'', hw'', hw''e⟩ := hsurj w hw
  have e2 : κ • L.actG h⁻¹ w = w'' := by rw [← map_nsmul, ← hw''e, hinv]
  have key : inAf D ((show D.La from a) - f x) = κ • (n • (w' + w'')) := by
    have e1 : inAf D a = L.actG h⁻¹ (κ • v) := by rw [← hav, hinv]
    rw [GlobalTheory.HeckeApprox.inAf_sub, e1, hvx, map_nsmul, map_add (f := _), map_nsmul, _root_.smul_add, hfx,
      smul_comm κ (n * κ), e2, smul_smul κ n, mul_comm κ n, _root_.smul_add]
    abel
  have hmem : n • (w' + w'') ∈ LaHat D := AddSubgroup.nsmul_mem _ (AddSubgroup.add_mem _ hw' hw'') n
  obtain ⟨y, hy⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ κ hκ0 hκc _ hmem key
  have hay : (show D.La from a) = f x + κ • y := by rw [← hy]; abel
  refine ⟨x, ?_⟩
  calc g = I'.ev κ a := ha.symm
    _ = I'.ev (M₁ : ℕ) ((n * c₁) • f x) :=
        ev_eq I'.ev I'.add I'.ker I'.tower (by rw [hM]; ring) hκ0 (Nat.mul_pos hn0 hc0) hay
    _ = I'.ev (M₁ : ℕ) (c₁ • n • f x) := by rw [smul_smul, mul_comm n c₁]
    _ = _ := (h1 _).symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ABetaH
set_option autoImplicit false

noncomputable section

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open GlobalTheory.HeckeApprox (inAf_sub inAf_nsmul inAf_mem inAfH)
open scoped TensorProduct

namespace UpperTheory.Gal.FiniteEtaleModels

theorem betaH_holds : BetaH := by
  intro p _ D G L h κ n hn hnp hnκ hI hκ
  set u := L.actG h with hu
  set ui := L.actG h⁻¹ with hui
  have hinv : ∀ v, ui (u v) = v := by
    intro v
    rw [hu, hui, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hinv' : ∀ v, u (ui v) = v := by
    intro v
    rw [hu, hui, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hIu : ∀ v ∈ LaHat D, u v ∈ LaHat D := hI
  set h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) := κ • ui with hh₀
  have h₀app : ∀ v, h₀ v = κ • ui v := fun v => rfl
  have h₀mem : ∀ v ∈ LaHat D, h₀ v ∈ LaHat D := by
    intro v hv
    obtain ⟨v', hv', e⟩ := hκ v hv
    rw [h₀app, ← map_nsmul, ← e, hinv]
    exact hv'
  have h₀u : ∀ v, u (h₀ v) = κ • v := by
    intro v
    rw [h₀app, map_nsmul, hinv']
  have h₀c : ∀ (c : D.O) v, h₀ (actAf D c v) = actAf D c (h₀ v) := by
    intro c v
    rw [h₀app, h₀app, hui, actG_actAf, map_nsmul]
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.lattice_endomorphism_integral_approximation p D h₀ h₀mem
  obtain ⟨k, m, hkm⟩ : ∃ k : ℕ, ∃ m : ℤ, (κ : ℤ) * k = 1 + n * m := by
    have hc : Nat.Coprime κ n := hnκ.symm
    have e := Nat.gcd_eq_gcd_ab κ n
    rw [hc.gcd_eq_one] at e
    have hn' : (0:ℤ) < n := by exact_mod_cast hn
    refine ⟨(Nat.gcdA κ n % n).toNat, -(Nat.gcdB κ n) - κ * (Nat.gcdA κ n / n), ?_⟩
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hn'.ne'), Int.emod_def]
    push_cast at e
    linear_combination -e
  have hsm : ∀ {M : Type} [AddCommGroup M] (y : M), (κ * k) • y = y + n • (m • y) := by
    intro M _ y
    have : (((κ * k : ℕ) : ℤ)) • y = ((1:ℤ) + n * m) • y := by push_cast; rw [hkm]
    rw [natCast_zsmul] at this
    rw [this, add_smul, one_smul, mul_smul, natCast_zsmul]
  have key : ∀ x, ∃ v ∈ LaHat D, u (inAf D (k • φ n x)) = inAf D x + n • v := by
    intro x
    obtain ⟨w, hw, e⟩ := hφ n hn hnp x
    refine ⟨m • inAf D x - k • u w, ?_, ?_⟩
    · exact sub_mem (zsmul_mem (inAf_mem D x) _) (nsmul_mem (hIu w hw) _)
    · have e2 : inAf D (φ n x) = h₀ (inAf D x) - n • w := by rw [e]; abel
      rw [inAf_nsmul, e2, map_nsmul, map_sub, h₀u, map_nsmul, smul_sub, smul_smul, mul_comm k κ, hsm,
        smul_sub n, smul_comm n k (u w)]
      abel
  have hg : ∀ x, (k • φ n) x = k • φ n x := fun x => rfl
  refine ⟨k • φ n, ?_, ?_, ?_, ?_⟩
  · intro c x
    rw [hg, hg]
    obtain ⟨w1, hw1, e1⟩ := hφ n hn hnp (c • x)
    obtain ⟨w2, hw2, e2⟩ := hφ n hn hnp x
    have a1 : inAf D (φ n (c • x)) = h₀ (inAf D (c • x)) - n • w1 := by rw [e1]; abel
    have a2 : inAf D (φ n x) = h₀ (inAf D x) - n • w2 := by rw [e2]; abel
    have hE : inAf D (k • φ n (c • x) - c • (k • φ n x)) = n • (k • (actAf D c w2 - w1)) := by
      rw [inAf_sub, inAf_nsmul, ← actAf_inAf, inAf_nsmul, map_nsmul, a1, a2, ← actAf_inAf, h₀c, map_sub,
        map_nsmul, smul_sub, smul_sub, smul_sub, smul_sub, smul_comm k n w1, smul_comm k n (actAf D c w2)]
      abel
    obtain ⟨z, hz⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ n hn hnp _
      (nsmul_mem (sub_mem (actAf_mem_laHat D c hw2) hw1) k) hE
    exact ⟨z, by rw [← hz]; abel⟩
  · intro x z hxz
    rw [hg] at hxz
    obtain ⟨v, hv, e⟩ := key x
    rw [hxz, inAf_nsmul, map_nsmul] at e
    have hx : inAf D x = n • (u (inAf D z) - v) := by rw [smul_sub, e]; abel
    exact LatDiv.eq_nsmul_of_inAf_eq_nsmul p D x n hn hnp _ (sub_mem (hIu _ (inAf_mem D z)) hv) hx
  · intro x
    obtain ⟨y, w, hw, e⟩ := exists_inAf_add_nsmul_of_mem_laHat p D n hn hnp (u (inAf D x)) (hIu _ (inAf_mem D x))
    obtain ⟨v, hv, ev⟩ := key y
    have hd : inAf D (k • φ n y) - inAf D x = ui (n • (v - w)) := by
      rw [← hinv (inAf D (k • φ n y) - inAf D x), map_sub, ev, e]
      congr 1
      rw [smul_sub]
      abel
    have h1 : inAf D (κ • (k • φ n y - x)) = n • h₀ (v - w) := by
      rw [inAf_nsmul, inAf_sub, hd, map_nsmul, h₀app, smul_comm κ n]
    obtain ⟨z1, hz1⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ n hn hnp _ (h₀mem _ (sub_mem hv hw)) h1
    refine ⟨y, k • z1 - m • (k • φ n y - x), ?_⟩
    have ht := hsm (k • φ n y - x)
    rw [mul_comm κ k, ← smul_smul, hz1] at ht
    rw [hg, smul_sub, smul_comm n k z1, ht]
    abel
  · intro x
    rw [hg]
    exact key x

end UpperTheory.Gal.FiniteEtaleModels
end
end

open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.FiniteEtaleModels

theorem stepA_holds (h₁ : MultUnit) (h₂ : LatGen) (h₃ : ClsEx) (h₄ : TrEta) (h₅ : TrBack) (h₆ : QComp) : StepA :=
  stepA_of (dictP_holds h₁) sysExt_holds trEtaK_holds trKer_holds galOfKer_holds betaH_holds (betaLat_holds h₂) numSplit_holds
    (coreA_of trPull trSame_holds levTr_holds levRe_holds h₃) h₄ h₅ h₆

end UpperTheory.Gal.FiniteEtaleModels
