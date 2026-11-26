module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.GalOfKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntIntCast
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorInverseHeckeTranslatesForgetLevel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.SecInjG
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedCommGroupSchemeArtinFibreProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeTjCorrespondenceTargetFiniteEtal

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ALevRe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.levRe_holds :
    LevRe := by
  intro q _ D R _ b N 𝔟₁ 𝔟₂ β hle hR S s o lv h
  obtain ⟨h1, h2, h3, h4⟩ := id h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    dsimp only
    rw [h.congr (hR.add x y), h1]
  · intro c x
    dsimp only
    rw [h.congr (hR.lin c x), h2]
  · intro x hx
    exact h3 _ ((hR.ker x).mpr hx)
  · intro k _ _ x
    refine ⟨fun y hy => (hR.ker y).mp ((h4 k x).1 _ hy), ?_⟩
    intro g hg
    have hg₁ : ∀ c ∈ 𝔟₁ ^ 1, g ≫ o.act.act ((algebraMap (𝓞 D.F) D.O) c) = 1 := by
      intro c hc
      rw [pow_one] at hc
      exact hg c (by rw [pow_one]; exact hle hc)
    obtain ⟨y0, hy0⟩ := (h4 k x).2 g hg₁
    obtain ⟨y, hy⟩ := hR.onto y0 (by
      intro c hc
      apply (h4 k x).1
      rw [h2, ← Category.assoc, hy0]
      exact hg c (by rw [pow_one]; exact hc))
    exact ⟨y, by dsimp only; rw [← h.congr hy, hy0]⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ANumSplit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

private theorem natCast_gcd_mem {A : Type} [CommRing A] {I : Ideal A} {x y : ℕ} (hx : (x : A) ∈ I) (hy : (y : A) ∈ I) :
    ((Nat.gcd x y : ℕ) : A) ∈ I := by
  have h : ((Nat.gcd x y : ℕ) : A) = (x : A) * (Nat.gcdA x y : A) + (y : A) * (Nat.gcdB x y : A) := by
    have := congrArg (Int.cast : ℤ → A) (Nat.gcd_eq_gcd_ab x y)
    push_cast at this
    exact this
  rw [h]
  exact I.add_mem (I.mul_mem_right _ hx) (I.mul_mem_right _ hy)

private theorem natCast_mem_of_isGen {A : Type} [CommRing A] {a : A} {N : ℕ} {𝔞 : Ideal A} (h : IsGen a N 𝔞) :
    (N : A) ∈ 𝔞 := by
  unfold IsGen at h
  have hN : (N : A) ∈ Ideal.span {(N : A)} := Ideal.mem_span_singleton_self _
  rw [← h] at hN
  have hle : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 ≤ 𝔞 := Ideal.mul_le_right
  exact hle hN

theorem UpperTheory.Gal.FiniteEtaleModels.numSplit_holds :
    NumSplit := by
  intro A _ _ _ 𝔟₁ 𝔟₂ M₁ M₂ Q a₁ a₂ hM₁ hM₂ hle h₁ h₂ hQ
  have hgM₁ : Nat.gcd Q (Nat.gcd M₁ M₂) ∣ M₁ := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  have hgM₂ : Nat.gcd Q (Nat.gcd M₁ M₂) ∣ M₂ := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  have hgQ : Nat.gcd Q (Nat.gcd M₁ M₂) ∣ Q := Nat.gcd_dvd_left _ _
  have hg_mem : ((Nat.gcd Q (Nat.gcd M₁ M₂) : ℕ) : A) ∈ 𝔟₂ :=
    natCast_gcd_mem (hle hQ) (natCast_gcd_mem (hle (natCast_mem_of_isGen h₁)) (natCast_mem_of_isGen h₂))
  have hgpos : 0 < Nat.gcd Q (Nat.gcd M₁ M₂) := Nat.pos_of_dvd_of_pos hgM₂ hM₂
  generalize Nat.gcd Q (Nat.gcd M₁ M₂) = g at hgM₁ hgM₂ hgQ hg_mem hgpos
  obtain ⟨m₁, hm₁⟩ := hgM₁
  obtain ⟨m₂, hm₂⟩ := hgM₂
  have h1 : a₂ * (g : A) ∈ Ideal.span {(M₂ : A)} := by
    rw [← h₂]
    exact Ideal.mul_mem_mul (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a₂)) hg_mem
  rw [Ideal.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  have hg0 : (g : A) ≠ 0 := by exact_mod_cast hgpos.ne'
  have hm₂pos : 0 < m₂ := by
    rcases Nat.eq_zero_or_pos m₂ with h | h
    · subst h; omega
    · exact h
  have hm₂0 : (m₂ : A) ≠ 0 := by exact_mod_cast hm₂pos.ne'
  have hM₂c : (M₂ : A) = (g : A) * (m₂ : A) := by rw [hm₂]; push_cast; ring
  have ha : a₂ = (m₂ : A) * c := by
    apply mul_right_cancel₀ hg0
    rw [hc, hM₂c]; ring
  refine ⟨g, m₁, m₂, c, hgQ, hm₁, hm₂, ha, ?_⟩
  unfold IsGen at h₂ ⊢
  have hs : Ideal.span {(m₂ : A)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hm₂0
  apply mul_left_cancel₀ hs
  calc Ideal.span {(m₂ : A)} * ((Ideal.span {c} ⊔ Ideal.span {(g : A)}) * 𝔟₂)
      = (Ideal.span {(m₂ : A)} * Ideal.span {c} ⊔ Ideal.span {(m₂ : A)} * Ideal.span {(g : A)}) * 𝔟₂ := by
        rw [← _root_.mul_assoc, Ideal.mul_sup]
    _ = (Ideal.span {a₂} ⊔ Ideal.span {(M₂ : A)}) * 𝔟₂ := by
        rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton, ← ha, hM₂c,
          _root_.mul_comm (m₂ : A)]
    _ = Ideal.span {(M₂ : A)} := h₂
    _ = Ideal.span {(m₂ : A)} * Ideal.span {(g : A)} := by
        rw [Ideal.span_singleton_mul_span_singleton, hM₂c, _root_.mul_comm]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ATrEtaK
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.trEtaK_holds :
    TrEtaK := by
  intro p _ D G L R _ _ gb h X s M₁ M₂ o' o ψ hT n κ c₁ c₂ hM1 hM2 x y hxy
  obtain ⟨v, hv, hxv⟩ := hxy
  haveI : IsMonHom ψ := hT.1
  obtain ⟨hM13, hM1c⟩ := M₁.2
  obtain ⟨hM23, hM2c⟩ := M₂.2
  have hne1 : (M₁ : ℕ) ≠ 0 := by omega
  have hne2 : (M₂ : ℕ) ≠ 0 := by omega
  have hne1' := hne1
  have hne2' := hne2
  rw [hM1] at hne1 hM1c
  rw [hM2] at hne2 hM2c
  have hn0 : 0 < n := Nat.pos_of_ne_zero (fun h0 => hne2 (by simp [h0]))
  have hκ0 : 0 < κ := Nat.pos_of_ne_zero (fun h0 => hne1 (by simp [h0]))
  have hc10 : 0 < c₁ := Nat.pos_of_ne_zero (fun h0 => hne1 (by simp [h0]))
  have hc20 : 0 < c₂ := Nat.pos_of_ne_zero (fun h0 => hne2 (by simp [h0]))
  have hnc : n.Coprime p := Nat.Coprime.coprime_dvd_left ⟨c₂, rfl⟩ hM2c
  have hnκc : (n * κ).Coprime p := Nat.Coprime.coprime_dvd_left ⟨c₁, rfl⟩ hM1c
  have hpc : ∀ (f : 𝟙_ (Over X) ⟶ o'.A) (k : ℕ), (f ^ k) ≫ ψ = (f ≫ ψ) ^ k := by
    intro f k
    induction k with
    | zero => rw [_root_.pow_zero, _root_.pow_zero, MonObj.one_comp]
    | succ k ih => rw [_root_.pow_succ, _root_.pow_succ, MonObj.mul_comp, ih]
  set a := o'.eta (c₁ • x) ≫ ψ with ha
  set b := o.eta (c₂ • y) with hb
  have haN : a ^ (M₁ : ℕ) = 1 := by
    rw [ha, ← hpc]
    exact (congrArg (· ≫ ψ) ((GObj.eta_nsmul o' _ _).symm.trans (GObj.eta_ker o' _))).trans
      (MonObj.one_comp ψ)
  have hbN : b ^ (M₂ : ℕ) = 1 := (GObj.eta_nsmul o _ _).symm.trans (GObj.eta_ker o _)
  have hunit : IsUnit (((M₁ : ℕ) * (M₂ : ℕ) : ℕ) : Γ(X, ⊤)) := by
    have hR : IsUnit (((M₁ : ℕ) * (M₂ : ℕ) : ℕ) : R) := by
      rw [← map_natCast (algebraMap ℚ R)]
      refine IsUnit.map (algebraMap ℚ R) (IsUnit.mk0 _ ?_)
      exact_mod_cast Nat.mul_ne_zero hne1' hne2'
    have := hR.map ((s.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    simpa using this
  rw [← _root_.mul_inv_eq_one]
  have hpow : (a * b⁻¹) ^ ((M₁ : ℕ) * (M₂ : ℕ)) = 1 := by
    rw [mul_pow, _root_.inv_pow, _root_.pow_mul, haN, _root_.mul_comm (M₁ : ℕ), _root_.pow_mul, hbN,
      _root_.one_pow, _root_.one_pow, inv_one, _root_.mul_one]
  have := GlobalTheory.TorsGeomPow.pow_eq_one_of_geometric_points X o.A o.ab _ hunit _ (a * b⁻¹) hpow 1 ?_
  · simpa using this
  intro k _ _ ξ
  rw [_root_.pow_one, MonObj.comp_mul, GrpObj.comp_inv, _root_.mul_inv_eq_one]
  rw [show Over.homMk ξ _ = toUnit (Over.mk (ξ ≫ (𝟙_ (Over X)).hom)) from Subsingleton.elim _ _]
  obtain ⟨β, hβ⟩ := GlobalTheory.UPel.HT.GenCmp.exists_spMap ((ξ ≫ (𝟙_ (Over X)).hom) ≫ s)
  obtain ⟨I', I'', h1, h2, hev⟩ := hT.2.2.2.2 k (ξ ≫ (𝟙_ (Over X)).hom) β hβ
  have e1 : I'.ev (M₁ : ℕ) (c₁ • x) = I'.ev (n * κ) x :=
    (KerBy.ev_nsmul _ (I'.add _) c₁ x).trans
      ((congrArg (fun m => I'.ev m x ^ c₁) hM1).trans (I'.tower (n * κ) c₁ (Nat.mul_pos hn0 hκ0) hc10 x))
  have e2 : I''.ev (M₂ : ℕ) (c₂ • y) = I''.ev n y :=
    (KerBy.ev_nsmul _ (I''.add _) c₂ y).trans
      ((congrArg (fun m => I''.ev m y ^ c₂) hM2).trans (I''.tower n c₂ hn0 hc20 y))
  have e3 : I''.ev (n * κ) (κ • y) = I''.ev n y :=
    (KerBy.ev_nsmul _ (I''.add _) κ y).trans (I''.tower n κ hn0 hκ0 y)
  have e4 : I'.ev (n * κ) x ≫ ψ = I''.ev (n * κ) (κ • y) :=
    (hev (n * κ) (Nat.mul_pos hn0 hκ0) hnκc x (κ • y)).mpr
      ⟨v, hv, by rw [GlobalTheory.HeckeApprox.inAf_nsmul]; exact hxv⟩
  rw [ha, hb, ← Category.assoc]
  exact (congrArg (· ≫ ψ) ((h1 _).trans e1)).trans (e4.trans (e3.trans (e2.symm.trans (h2 _).symm)))
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.StepAOf
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct

namespace UpperTheory.Gal.FiniteEtaleModels

theorem stepA_of (hD : DictP) (hX : SysExt) (hE : TrEtaK) (hK : TrKer) (hG : GalOfKer) (hH : BetaH) (hB : BetaLat) (hN : NumSplit)
    (hC : CoreA) (hE' : TrEta) (hBk : TrBack) (hQ : QComp) : StepA := by
  intro p _ D G L _ E _ _ gb w q _ r 𝔴 𝔫 S k T N₀ κ 𝔟₁ 𝔟₂ X₁ X₂ hle h hI hκ M₁ M₂ c₁ c₂ a₁ a₂ hn₁ hn₂ C₁ C₂ W
  obtain ⟨e₁, g₁⟩ : M₁.1 = N₀ * κ * c₁ ∧ IsGen a₁ M₁.1 𝔟₁ := hn₁
  obtain ⟨e₂, g₂⟩ : M₂.1 = N₀ * c₂ ∧ IsGen a₂ M₂.1 𝔟₂ := hn₂
  obtain ⟨l3, lq, lp, -, e, he⟩ := X₁.lev
  obtain ⟨l3', lq', -, -, -⟩ := X₂.lev
  have h₁ : 0 < M₁.1 := lt_of_lt_of_le (by norm_num) M₁.2.1
  have h₂ : 0 < M₂.1 := lt_of_lt_of_le (by norm_num) M₂.2.1
  have hNκ : 0 < N₀ * κ := by omega
  have hκ0 : 0 < κ := Nat.pos_of_mul_pos_left hNκ
  have hκp : κ.Coprime p := Nat.Coprime.coprime_dvd_left (dvd_mul_left _ _) lp
  have hκq : κ.Coprime q := Nat.Coprime.coprime_dvd_left (dvd_mul_left _ _) lq
  have hqe : ((q ^ e : ℕ) : 𝓞 D.F) ∈ 𝔟₁ := by
    rw [Nat.cast_pow]
    exact he (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_insert _ _)) e)
  obtain ⟨hmon, hlin, -, ⟨c', hc'p, hpol, hmult⟩, -⟩ := id W.trans
  obtain ⟨f, u, c, hcc, hsys, hrel⟩ := hD p D G L h κ c' hκ0 hκp hc'p hI hκ hmult
  obtain ⟨f', u', hsys', hff⟩ := hX D.toG p Fact.out f u c c' κ hcc hc'p hsys
  let F : D.La →+ D.La := f' (N₀ * κ)
  have hF : ∀ x, ∃ v ∈ LaHat D, κ • L.actG h⁻¹ (inAf D x) = inAf D (F x) + (N₀ * κ) • v := fun x => by
    obtain ⟨v, hv, ev⟩ := hrel _ hNκ lp x
    obtain ⟨z, hz⟩ : ∃ z : D.La, F x = f (N₀ * κ) x + (N₀ * κ) • z := hff _ hNκ lp x
    refine ⟨v - inAf D z, sub_mem hv (GlobalTheory.HeckeApprox.inAf_mem D z), ?_⟩
    rw [ev, hz, GlobalTheory.HeckeApprox.inAf_add, GlobalTheory.HeckeApprox.inAf_nsmul, smul_sub]
    abel
  have heta : ∀ y : D.La, (T.M M₁).univ.eta (c₁ • F y) ≫ W.ψ = W.o.eta (c₂ • y) := fun y => by
    refine hE p D G L E gb h _ _ M₁ M₂ _ _ W.ψ W.trans N₀ κ c₁ c₂ e₁ e₂ (F y) y ?_
    obtain ⟨v, hv, ev⟩ := hF y
    refine ⟨-L.actG h v, neg_mem (hI v hv), ?_⟩
    have := congrArg (L.actG h) ev
    rw [map_nsmul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, map_add (f := _), map_nsmul] at this
    rw [this, smul_neg]
    abel
  obtain ⟨n, m₁, m₂, a, hnQ, en₁, en₂, ea, ga⟩ := hN (𝓞 D.F) 𝔟₁ 𝔟₂ M₁.1 M₂.1 (q ^ e) a₁ a₂ h₁ h₂ hle g₁ g₂ hqe
  have hn0 : 0 < n := Nat.pos_of_mul_pos_right (en₁ ▸ h₁)
  have hm0 : 0 < m₁ := Nat.pos_of_mul_pos_left (en₁ ▸ h₁)
  obtain ⟨g, gl, gi, gs, gr⟩ := hH p D G L h κ n hn0 (Nat.Coprime.coprime_dvd_left ⟨m₁, en₁⟩ M₁.2.2)
    (Nat.Coprime.coprime_dvd_left hnQ (hκq.symm.pow_left e)) hI hκ
  obtain ⟨ρ, hρ, hρe⟩ := hB q (datAt S.atq S.sp) 𝔟₁ 𝔟₂ n m₁ a₁ a hn0 hm0 hle (en₁ ▸ g₁) ga g gl gi gs
  have hlv : ∀ y : D.La, (T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • (ρ y : D.La)) ≫ W.ψ =
      W.o.eta (algebraMap (𝓞 D.F) D.O a₂ • y) := fun y => by
    obtain ⟨z, hz⟩ : ∃ z : D.La, m₁ • g (algebraMap (𝓞 D.F) D.O a • y) = algebraMap (𝓞 D.F) D.O a₁ • (ρ y : D.La) + (n * m₁) • z := hρe y
    have t₁ := hE' p D G L E gb h _ _ M₁ M₂ _ _ W.ψ W.trans n m₁ m₂ en₁ en₂ _ _ (gr (algebraMap (𝓞 D.F) D.O a • y))
    have t₂ : (T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • (ρ y : D.La) + M₁.1 • z) =
        (T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • (ρ y : D.La)) :=
      ((T.M M₁).univ.eta_add _ _).trans (by
        rw [show (T.M M₁).univ.eta (M₁.1 • z : D.La) = 1 from (T.M M₁).univ.eta_ker z, _root_.mul_one])
    have t₃ : algebraMap (𝓞 D.F) D.O a₂ • y = m₂ • algebraMap (𝓞 D.F) D.O a • y := by
      rw [ea, map_mul, map_natCast, mul_smul, Nat.cast_smul_eq_nsmul]
    rw [hz, ← en₁] at t₁
    rw [t₃, ← t₂]
    exact t₁
  obtain ⟨ψ', hm', b₁, b₂⟩ := hBk p D G L E gb h _ _ M₁ M₂ _ _ W.ψ W.trans κ hκp hκ
  have hdiv : κ ^ 2 / c = c' := by
    have hc0 : 0 < c := Nat.pos_of_mul_pos_right (hcc ▸ pow_pos hκ0 2)
    rw [← hcc, Nat.mul_div_cancel_left _ hc0]
  let o₁ := ob (D := datAt S.atq S.sp) (gb := gb) S.mat (T.M M₁).univ (N₀ * κ) c₁ e₁ h₁
  have hA : IsTranslA (D := datAt S.atq S.sp) F c κ N₀ o₁ (ob (D := datAt S.atq S.sp) (gb := gb) S.mat W.o N₀ c₂ e₂ h₂) W.ψ := by
    obtain ⟨hfin, hfree⟩ := HeckeAd.heckeSubA_finite_free S.b F κ N₀ hκ0 (by omega) hκq lq' _ o₁
    refine ⟨hmon, hlin, fun y => (heta y).symm, ?_, hdiv ▸ hpol, ⟨c', hcc.symm⟩⟩
    haveI := hmon
    refine hG _ _ _ (T.M M₁).univ.ab W.o.ab W.ψ ψ' κ hmon hm' b₁ b₂ (Hecke.Comp.isUnit_natCast S.b ((T.M M₁).s ≫ spMap (algebraMap (Ow w) E)) κ hκq) _ hfin ?_ hfree ?_
    · rintro _ ⟨x, rfl⟩
      show (T.M M₁).univ.eta (c₁ • N₀ • F x) ≫ W.ψ = 1
      rw [← map_nsmul, heta, smul_smul, mul_comm c₂, ← e₂]
      exact W.o.eta_ker x
    · intro Ω _ _ z y₀ hy₀
      obtain ⟨x, hx⟩ := hK p D G L E gb h _ _ M₁ M₂ _ _ W.ψ W.trans N₀ κ c₁ e₁ hκ F hF Ω z y₀ hy₀ (by
        haveI := hm'
        rw [← Category.comp_id y₀, ← MonObj.comp_pow, ← b₁, ← Category.assoc, hy₀, MonObj.one_comp])
      exact ⟨_, HeckeAd.mem_heckeSubA o₁ F N₀ x, hx⟩
  obtain ⟨n', hn'⟩ := (hQ q (datAt S.atq S.sp) (Ow w) E S.b gb M₂.1 N₀ c₂ _ _ _ _ _ _ (T.M M₂).univ X₂.Y.univ X₂.Y.univ C₂.j (𝟙 _)).2.2.2
    _ _ W.o W.π W.φ C₂.m
  let C₂' : Cls (D := datAt S.atq S.sp) (gb := gb) X₂.Y (algebraMap (Ow w) E) W.o c₂ a₂ :=
    { j := W.π ≫ C₂.j
      ov := by rw [Category.assoc, C₂.ov, ← Category.assoc, W.ov]
      m := n'
      lv := fun y => by
        rw [hn', ← Category.assoc]
        erw [W.φ.eta]
        rw [Category.assoc, Category.assoc]
        exact congrArg _ (C₂.lv y) }
  haveI : Smooth X₁.M.s := X₁.M.smooth.smooth
  haveI := X₁.et
  haveI : IsLocallyNoetherian X₁.Y.X := LocallyOfFiniteType.isLocallyNoetherian (X₁.π ≫ X₁.M.s)
  obtain ⟨t, Φ, ht, hΦ, j₁, j₂⟩ := hC q (datAt S.atq S.sp) (Ow w) E S.b gb _ S.mat N₀ κ c 𝔟₁ 𝔟₂ X₁.Y X₂.Y this l3' lq' hκq ⟨c', hcc.symm⟩ hle
    ⟨e, hqe⟩ f' u' (hsys'.mono q) ρ hρ _ _ M₁.1 M₂.1 c₁ c₂ a₁ a₂ e₁ e₂ h₁ h₂ g₂ (T.M M₁).univ W.o W.ψ hA hlv C₁ C₂'
  exact ⟨⟨t, ht, Φ, hΦ⟩, j₁, j₂.trans (by rw [← hn'])⟩

end UpperTheory.Gal.FiniteEtaleModels
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsDominantGenericFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

private theorem exists_geomPoint (P : Scheme.{0}) (p : P) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (t : Sp Ω ⟶ P) (q : Sp Ω), t q = p := by
  refine ⟨AlgebraicClosure (P.residueField p), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (P.residueField p) (AlgebraicClosure (P.residueField p)))) ≫
      P.fromSpecResidueField p, IsLocalRing.closedPoint _, ?_⟩
  change (P.fromSpecResidueField p) ((Spec.map (CommRingCat.ofHom (algebraMap (P.residueField p)
    (AlgebraicClosure (P.residueField p))))) (IsLocalRing.closedPoint _)) = p
  exact Scheme.fromSpecResidueField_apply p _

private theorem isDominant_genericFibre (O E : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E]
    [IsFractionRing O E] {X : Scheme.{0}} (s : X ⟶ Sp O) [Flat s] :
    IsDominant (pullback.fst s (spMap (algebraMap O E))) := by
  refine ⟨fun x => ?_⟩
  let gp : Sp E := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum E)
  have hgp : spMap (algebraMap O E) gp ⤳ s x := by
    refine (PrimeSpectrum.le_iff_specializes (R := O) _ _).1 ?_
    show Ideal.comap (algebraMap O E) ⊥ ≤ _
    rw [Ideal.comap_bot_of_injective _ (IsFractionRing.injective O E)]
    exact bot_le
  obtain ⟨x', hx', e⟩ := Flat.generalizingMap s hgp
  refine hx'.mem_closed isClosed_closure (subset_closure ?_)
  rw [Scheme.Pullback.range_fst]
  exact ⟨gp, e.symm⟩

private theorem eq_of_geomPoints {P Y B : Scheme.{0}} [IsReduced P] (a b : P ⟶ Y) (g : Y ⟶ B) [IsSeparated g]
    (hab : a ≫ g = b ≫ g)
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ P), t ≫ a = t ≫ b) : a = b := by
  let d : P ⟶ pullback g g := pullback.lift a b hab
  let k₀ : pullback d (pullback.diagonal g) ⟶ P := pullback.fst d (pullback.diagonal g)
  have hd₁ : d ≫ pullback.fst g g = a := pullback.lift_fst _ _ _
  have hd₂ : d ≫ pullback.snd g g = b := pullback.lift_snd _ _ _
  have hc : k₀ ≫ d = pullback.snd d (pullback.diagonal g) ≫ pullback.diagonal g := pullback.condition
  have hk : k₀ ≫ a = k₀ ≫ b := by
    have h1 : k₀ ≫ a = pullback.snd d (pullback.diagonal g) := by
      calc k₀ ≫ a = (k₀ ≫ d) ≫ pullback.fst g g := by rw [Category.assoc, hd₁]
        _ = _ := by rw [hc]; simp
    have h2 : k₀ ≫ b = pullback.snd d (pullback.diagonal g) := by
      calc k₀ ≫ b = (k₀ ≫ d) ≫ pullback.snd g g := by rw [Category.assoc, hd₂]
        _ = _ := by rw [hc]; simp
    rw [h1, h2]
  have hsur : Surjective k₀ := ⟨fun p => by
    obtain ⟨Ω, _, _, t, q, rfl⟩ := exists_geomPoint P p
    have hd : t ≫ d = (t ≫ a) ≫ pullback.diagonal g := by
      apply pullback.hom_ext
      · rw [Category.assoc, hd₁]; simp
      · rw [Category.assoc, hd₂, ← h Ω t]; simp
    refine ⟨(pullback.lift t (t ≫ a) hd : Sp Ω ⟶ _) q, ?_⟩
    rw [← Scheme.Hom.comp_apply]
    exact congrArg (fun m : Sp Ω ⟶ P => m q) (pullback.lift_fst _ _ _)⟩
  have : IsDominant k₀ := inferInstance
  exact ext_of_isDominant_of_isSeparated g hab k₀ hk

theorem UpperTheory.Gal.FiniteEtaleModels.descExt_of :
    NormExt → DescExt := by
  intro hN O E _ _ _ _ _ _ V X Y B s σ j ov hs hfin het hgeo f g y hg hy hker
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have : IsLocalization.Away ϖ E := GlobalTheory.Reg.ChartOpens.away_irreducible hϖ
  have : IsOpenImmersion (spMap (algebraMap O E)) := IsOpenImmersion.of_isLocalization ϖ
  let e : Sp E ⟶ Sp O := spMap (algebraMap O E)
  let u : pullback s e ⟶ X := pullback.fst s e
  let j' : V ⟶ pullback s e := pullback.lift j σ ov
  have hj' : j' ≫ u = j := pullback.lift_fst _ _ _
  have hjσ : j' ≫ pullback.snd s e = σ := pullback.lift_snd _ _ _
  have hdom : IsDominant u := isDominant_genericFibre O E s
  have hsurj : Surjective j' := ⟨fun w => by
    obtain ⟨Ω, _, _, t, q, rfl⟩ := exists_geomPoint _ w
    obtain ⟨v, hv₁, hv₂⟩ := hgeo Ω (t ≫ u) (t ≫ pullback.snd s e) (by
      rw [Category.assoc, Category.assoc]
      exact congrArg (t ≫ ·) pullback.condition)
    have hv : v ≫ j' = t := by
      apply pullback.hom_ext
      · rw [Category.assoc]
        change v ≫ j' ≫ u = t ≫ u
        rw [hj', hv₁]
      · rw [Category.assoc, hjσ, hv₂]
    refine ⟨v q, ?_⟩
    rw [← Scheme.Hom.comp_apply, hv]⟩

  have stalk_normal (T : Scheme.{0}) (t : T ⟶ Sp O) [Smooth t] (x : T) :
      IsDomain (T.presheaf.stalk x) ∧ IsIntegrallyClosed (T.presheaf.stalk x) := by
    refine GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth t (fun q => ?_) x
    haveI : q.asIdeal.IsPrime := PrimeSpectrum.isPrime q
    let _ : Algebra O ((Sp O).presheaf.stalk q) := StructureSheaf.stalkAlgebra O q
    have h : IsLocalization.AtPrime ((Sp O).presheaf.stalk q) q.asIdeal :=
      StructureSheaf.IsLocalization.to_stalk O q
    have hle : q.asIdeal.primeCompl ≤ nonZeroDivisors O := q.asIdeal.primeCompl_le_nonZeroDivisors
    have hd : IsDomain ((Sp O).presheaf.stalk q) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
    exact ⟨hd, isIntegrallyClosed_of_isLocalization _ _ hle⟩
  have hsm : Smooth (pullback.fst j' j' ≫ j' ≫ u ≫ s) := inferInstance
  have hred : IsReduced (pullback j' j') := by
    have : ∀ x : (pullback j' j' : Scheme.{0}), _root_.IsReduced ((pullback j' j' : Scheme.{0}).presheaf.stalk x) := fun x => by
      letI : IsDomain ((pullback j' j' : Scheme.{0}).presheaf.stalk x) :=
        (stalk_normal _ (pullback.fst j' j' ≫ j' ≫ u ≫ s) x).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  have hP : pullback.fst j' j' ≫ y = pullback.snd j' j' ≫ y := by
    refine eq_of_geomPoints _ _ g ?_ fun Ω _ _ t => ?_
    · rw [Category.assoc, Category.assoc, hy, ← hj', Category.assoc, pullback.condition_assoc]
    · rw [← Category.assoc, ← Category.assoc]
      refine hker Ω _ _ ?_
      rw [Category.assoc, Category.assoc, ← hj', pullback.condition_assoc]
  have hee : EffectiveEpi j' := inferInstance
  let z : pullback s e ⟶ Y := EffectiveEpi.desc j' y (fun {T} g₁ g₂ h => by
    calc g₁ ≫ y = (pullback.lift g₁ g₂ h ≫ pullback.fst j' j') ≫ y := by rw [pullback.lift_fst]
      _ = (pullback.lift g₁ g₂ h ≫ pullback.snd j' j') ≫ y := by
        rw [Category.assoc, Category.assoc, hP]
      _ = g₂ ≫ y := by rw [pullback.lift_snd])
  have hz : j' ≫ z = y := EffectiveEpi.fac _ _ _
  have hzg : z ≫ g = u ≫ f := by
    rw [← cancel_epi j', ← Category.assoc, hz, hy, ← hj', Category.assoc]
  obtain ⟨y', h₁, h₂⟩ := hN _ X Y B u f g z inferInstance hdom (LocallyOfFiniteType.isLocallyNoetherian s)
    (fun x => (stalk_normal X s x).1)
    (fun x => (stalk_normal X s x).2) hg hzg
  exact ⟨y', by rw [← hj', Category.assoc, h₁, hz], h₂⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ATrPull
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
open GlobalTheory.UPel.HT.Hecke.PullHecke
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA mem_heckeSubA)

attribute [local instance] Over.cartesianMonoidalCategory

namespace UpperTheory.Gal.FiniteEtaleModels

theorem trPull : TrPull := by
  intro q _ D R _ b f c k N S S' s s' j o o' ψ o₁ o₁' m m' hT
  obtain ⟨hmon, hact, heta, hgal, ⟨hlb⟩, hck⟩ := hT
  have hc1 : m.φ ≫ o.A.hom = o₁.A.hom ≫ j := m.cart.1.w
  have hc2 : m'.φ ≫ o'.A.hom = o₁'.A.hom ≫ j := m'.cart.1.w
  have hψw : ψ.left ≫ o'.A.hom = o.A.hom := Over.w ψ
  let l : o₁.A.left ⟶ o₁'.A.left := m'.cart.1.lift (m.φ ≫ ψ.left) o₁.A.hom
    (by rw [Category.assoc, hψw, hc1])
  have hl1 : l ≫ m'.φ = m.φ ≫ ψ.left := m'.cart.1.lift_fst _ _ _
  have hl2 : l ≫ o₁'.A.hom = o₁.A.hom := m'.cart.1.lift_snd _ _ _
  let ψ₁ : o₁.A ⟶ o₁'.A := Over.homMk l hl2
  have hψ₁ : ψ₁.left = l := rfl
  have hext : ∀ {Z : Scheme} (u v : Z ⟶ o₁'.A.left), u ≫ m'.φ = v ≫ m'.φ →
      u ≫ o₁'.A.hom = v ≫ o₁'.A.hom → u = v := fun u v h1 h2 => m'.cart.1.hom_ext h1 h2
  have hl1' : ∀ {Z : Scheme} (u : Z ⟶ o₁.A.left), u ≫ l ≫ m'.φ = u ≫ m.φ ≫ ψ.left := by
    intro Z u
    rw [hl1]
  have hl2' : ∀ {Z : Scheme} (u : Z ⟶ o₁.A.left), u ≫ l ≫ o₁'.A.hom = u ≫ o₁.A.hom := by
    intro Z u
    rw [hl2]
  refine ⟨ψ₁, ⟨?_, ?_, ?_, ?_, ?_, hck⟩, hl1⟩
  · apply isMonHom_of_mul
    intro T x y
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, hψ₁]
    apply hext
    · have h1 := m.cart.2 T x y (pushPt hc1 x) (pushPt hc1 y) rfl rfl
      have h2 := m'.cart.2 T (x ≫ ψ₁) (y ≫ ψ₁) (pushPt hc1 x ≫ ψ) (pushPt hc1 y ≫ ψ)
        (by simp only [Over.comp_left, hψ₁, Category.assoc, hl1]; rfl)
        (by simp only [Over.comp_left, hψ₁, Category.assoc, hl1]; rfl)
      rw [Category.assoc, hl1', ← h2, ← MonObj.mul_comp, Over.comp_left, h1, Category.assoc]
    · simp only [Category.assoc, hl2', Over.w]
  · intro a
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, hψ₁]
    have hA : (o.act.act a).left ≫ ψ.left = ψ.left ≫ (o'.act.act a).left := by
      rw [← Over.comp_left, hact a, Over.comp_left]
    apply hext
    · rw [Category.assoc, hl1', ← Category.assoc, m.act a, Category.assoc, hA,
        Category.assoc, m'.act a, ← Category.assoc l, hl1, Category.assoc]
    · simp only [Category.assoc, hl2', Over.w, hl2]
  · intro x
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, hψ₁]
    apply hext
    · rw [m'.eta x, heta x, Over.comp_left, Category.assoc, hl1', ← Category.assoc (o₁.eta (f x)).left,
        m.eta (f x), Category.assoc]
    · simp only [Category.assoc, hl2', Over.w]
  · have hkey : ∀ y : D.La, (transl (o₁.eta y)).left ≫ m.φ = m.φ ≫ (transl (o.eta y)).left := by
      intro y
      let e : Over.mk (o₁.A.hom ≫ j) ⟶ o.A := pushPt hc1 (𝟙 o₁.A)
      have he : e.left = m.φ := by simp [e, pushPt]
      have h1 := m.cart.2 o₁.A (𝟙 o₁.A) (toUnit o₁.A ≫ o₁.eta y) e (toUnit _ ≫ o.eta y) rfl
        (by simp [m.eta])
      have h2 : e ≫ transl (o.eta y) = e * (toUnit _ ≫ o.eta y) := by
        simp only [transl, MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]
      calc (transl (o₁.eta y)).left ≫ m.φ = (e * (toUnit _ ≫ o.eta y)).left := by unfold transl; exact h1.symm
        _ = (e ≫ transl (o.eta y)).left := by rw [h2]
        _ = m.φ ≫ (transl (o.eta y)).left := by rw [Over.comp_left, he]
    have hpb : IsPullback m.φ ψ₁.left ψ.left m'.φ :=
      IsPullback.of_bot (by rw [hψ₁, hl2, hψw]; exact m.cart.1) hl1.symm m'.cart.1
    refine isGaloisCover_of_isPullback hgal hpb ?_ ?_ ?_ ?_ ?_ ?_
    · show (transl (1 : 𝟙_ (Over S') ⟶ o₁.A)).left = _
      rw [transl_one]
      rfl
    · intro a a'
      simp only [Subgroup.coe_mul, transl_mul, Over.comp_left]
    · intro a a' h
      exact Subtype.ext (transl_injective h)
    · rintro ⟨h, x, rfl⟩
      simp only [hψ₁]
      apply hext
      · rw [Category.assoc, hl1', ← Category.assoc, hkey, Category.assoc,
          hgal.inv ⟨o.eta (N • f x), mem_heckeSubA o f N x⟩, hl1]
      · simp only [Category.assoc, hl2', Over.w, hl2]
    · rintro ⟨h, x, rfl⟩
      exact ⟨⟨o.eta (N • f x), mem_heckeSubA o f N x⟩, hkey _⟩
    · rintro ⟨h, x, rfl⟩
      exact ⟨⟨o₁.eta (N • f x), mem_heckeSubA o₁ f N x⟩, hkey _⟩
  · have hsq : sq2 ψ₁ ≫ m'.φ₂ = m.φ₂ ≫ sq2 ψ := by
      apply grpScheme_square_hom_ext
      · have e1 : m'.φ₂ ≫ (fst o'.A o'.A).left = (fst o₁'.A o₁'.A).left ≫ m'.φ := m'.sq.1
        have e2 : m.φ₂ ≫ (fst o.A o.A).left = (fst o₁.A o₁.A).left ≫ m.φ := m.sq.1
        calc (sq2 ψ₁ ≫ m'.φ₂) ≫ (fst o'.A o'.A).left
            = (sq2 ψ₁ ≫ (fst o₁'.A o₁'.A).left) ≫ m'.φ := by
              rw [Category.assoc, e1, Category.assoc]
          _ = (fst o₁.A o₁.A).left ≫ m.φ ≫ ψ.left := by
              rw [grpSchemeSquareProductMap_comp_fst, Category.assoc, hψ₁, hl1]
          _ = (m.φ₂ ≫ (fst o.A o.A).left) ≫ ψ.left := by
              rw [e2, Category.assoc]
          _ = (m.φ₂ ≫ sq2 ψ) ≫ (fst o'.A o'.A).left := by
              rw [Category.assoc, Category.assoc, grpSchemeSquareProductMap_comp_fst]
      · have e1 : m'.φ₂ ≫ (snd o'.A o'.A).left = (snd o₁'.A o₁'.A).left ≫ m'.φ := m'.sq.2
        have e2 : m.φ₂ ≫ (snd o.A o.A).left = (snd o₁.A o₁.A).left ≫ m.φ := m.sq.2
        calc (sq2 ψ₁ ≫ m'.φ₂) ≫ (snd o'.A o'.A).left
            = (sq2 ψ₁ ≫ (snd o₁'.A o₁'.A).left) ≫ m'.φ := by
              rw [Category.assoc, e1, Category.assoc]
          _ = (snd o₁.A o₁.A).left ≫ m.φ ≫ ψ.left := by
              rw [grpSchemeSquareProductMap_comp_snd, Category.assoc, hψ₁, hl1]
          _ = (m.φ₂ ≫ (snd o.A o.A).left) ≫ ψ.left := by
              rw [e2, Category.assoc]
          _ = (m.φ₂ ≫ sq2 ψ) ≫ (snd o'.A o'.A).left := by
              rw [Category.assoc, Category.assoc, grpSchemeSquareProductMap_comp_snd]
    have hL1 : (Hecke.lbPow o₁.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hL0 : (Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
    refine ⟨(GlobalTheory.CechPic.cls_eq_iff hL1 (pull_isLB o₁'.isLB (sq2 ψ₁))).1 ?_⟩
    rw [cls_heckePow o₁.isLB, GlobalTheory.CechPic.cls_pull o₁'.isLB,
      (GlobalTheory.CechPic.cls_eq_iff o₁.isLB (pull_isLB o.isLB m.φ₂)).2 m.pol, GlobalTheory.CechPic.cls_pull o.isLB,
      (GlobalTheory.CechPic.cls_eq_iff o₁'.isLB (pull_isLB o'.isLB m'.φ₂)).2 m'.pol, GlobalTheory.CechPic.cls_pull o'.isLB,
      ← GlobalTheory.CechPic.pull_comp, hsq, GlobalTheory.CechPic.pull_comp,
      ← GlobalTheory.CechPic.cls_pull o'.isLB (sq2 ψ) (pull_isLB o'.isLB _),
      ← (GlobalTheory.CechPic.cls_eq_iff hL0 (pull_isLB o'.isLB (sq2 ψ))).2 hlb,
      cls_heckePow o.isLB, map_nsmul]

end UpperTheory.Gal.FiniteEtaleModels
end
end
