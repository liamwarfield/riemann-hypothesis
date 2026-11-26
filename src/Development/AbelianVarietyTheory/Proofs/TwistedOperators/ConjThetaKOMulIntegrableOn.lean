module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SizesOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqVolMulSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignBlockDeterminantOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicCuspFormsHermitianSpaceSignTwist

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjThetaKOMulIntegrableOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped ComplexConjugate

namespace GlobalTheory.UpArrowConv

theorem thetaKO_toSgn {D : D7} {S T : HSp D} (om : GlobalTheory.Grid.WRep S T) (h : GA D S) (g : GA D T) (f : WO S T → ℂ) :
    thetaKO om h g f = thetaKO (om.toSgn true) ((GlobalTheory.Grid.ofSgn true S).symm h) g f := by
  unfold thetaKO GlobalTheory.Grid.WRep.toSgn
  simp

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {f : WO S T → ℂ}

theorem thetaKO_left_snd (hω : IsWeilDatumO ψ S T χS χT om) (hf : IsThetaFunO ψ S T f) (h : GA D S) :
    ∀ γ ∈ GQ T, ∀ g, thetaKO om h (γ * g) f = thetaKO om h g f := fun γ hγ g => by
  have e : ((h, γ * g) : GA D S × GA D T) = (1, γ) * (h, g) := by simp
  unfold thetaKO
  rw [e, map_mul]
  exact hω.om_aut 1 (one_mem _) _ hγ _ (hω.om_pres _ _ hf)

theorem thetaKO_continuous_snd (hω : IsWeilDatumO ψ S T χS χT om) (hf : IsThetaFunO ψ S T f) (h : GA D S) :
    Continuous fun g => thetaKO om h g f :=
  (hω.om_cont f hf 0).comp (Continuous.prodMk_right h)

theorem conj_thetaKO_modGrowth_snd (hω : IsWeilDatumO ψ S T χS χT om) (hf : IsThetaFunO ψ S T f) (h : GA D S) :
    GlobalTheory.Grow.ModGrowth T fun g => conj (thetaKO om h g f) := by
  obtain ⟨C, A, hC⟩ := GlobalTheory.Core.Rk.ThetaGrowthBoth.thetaKO_modGrowth₂ D ψ S T χS χT om hω f hf
  refine ⟨C * GlobalTheory.Grow.height S h ^ A, A, fun g => ?_⟩
  rw [RCLike.norm_conj, mul_assoc, ← mul_pow]
  exact hC h g

theorem conj_thetaKO_mul_integrableOn (hP : GlobalTheory.Published.CuspRapidDecay)
    {θ : D.what₂.Tau → TensorProduct (↥D.host.F) (Ainf ↥D.host.F) D.host.E →+* ℂ} (hθ : IsInfFam θ)
    (hω : IsWeilDatumO ψ S T χS χT om) (hf : IsThetaFunO ψ S T f) {ν : Measure (GA D T)} {𝓕 : Set (GA D T)}
    (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ T) 𝓕 ν) {φ : GA D T → ℂ} (hφ : IsAutFunSm θ T φ)
    (hc : IsCuspFun T φ) (h : GA D S) :
    IntegrableOn (fun g => conj (thetaKO om h g f) * φ g) 𝓕 ν :=
  (GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ hφ hc).integrableOn_modGrowth_mul hν h𝓕
    (conj_thetaKO_modGrowth_snd hω hf h)
    (fun γ hγ g => by simp only [thetaKO_left_snd hω hf h γ hγ g])
    ((Complex.continuous_conj.comp (thetaKO_continuous_snd hω hf h)).measurable.aestronglyMeasurable)

end GlobalTheory.UpArrowConv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnThetaKOMulCusp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DownConv

open GlobalTheory.Grid

variable {D : D7}

theorem MeasDat.haar_fd {N : Node D} {m : N.MeasDat} {df : Prop} {K : Subgroup (GL (Fin N.V.rank) (Lev.EAf D))}
    (h : m.Is df K) : m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ N.V) m.fd m.ν := by
  by_cases hd : df
  · exact ⟨(h.1 hd).1.1, (h.1 hd).2⟩
  · exact ⟨(h.2 hd).1.1, (h.2 hd).2⟩

theorem integrableOn_thetaKO_mul_cusp (hP : GlobalTheory.Published.CuspRapidDecay) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    (hθ : IsInfFam θ) (ε : Bool) {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {ω : WRep S T}
    (hω : IsWeilDatumO ψ (sgn ε S) T χS χT (ω.toSgn ε)) {Φ : WO S T → ℂ} (hΦ : IsThetaFunO ψ (sgn ε S) T Φ)
    {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ S) 𝓕 ν)
    {φ : GA D S → ℂ} (hφ : IsAutFunSm θ S φ) (hc : IsCuspFun S φ) (h : GA D T) :
    IntegrableOn (fun g => thetaKO ω g h Φ * φ g) 𝓕 ν := by
  have : BorelSpace (GA D S) := ⟨rfl⟩
  have hR : GlobalTheory.Grow.RapidDec S φ := GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ hφ hc
  have e : ∀ g, thetaKO ω g h Φ = thetaKO (ω.toSgn ε) ((ofSgn ε S).symm g) h Φ := fun g => by
    show ω (g, h) Φ 0 = ω (ofSgn ε S ((ofSgn ε S).symm g), h) Φ 0
    rw [MulEquiv.apply_symm_apply]
  have hcont : Continuous fun g => thetaKO ω g h Φ := by
    simp only [e]
    exact (hω.om_cont Φ hΦ 0).comp ((continuous_ofSgn_symm ε S).prodMk continuous_const)
  have hinv : ∀ γ ∈ GQ S, ∀ g, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ := fun γ hγ g => by
    rw [e, e, map_mul]
    refine GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_left_fst hω hΦ h _ ?_ _
    rw [GlobalTheory.SgnIdent.mem_GQ_sgn, MulEquiv.apply_symm_apply]
    exact hγ
  have hg : GlobalTheory.Grow.ModGrowth S fun g => thetaKO ω g h Φ := by
    obtain ⟨C, A, hC⟩ := GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_modGrowth_fst hθ hω hΦ h
    exact ⟨C, A, fun g => by simp only [e]; exact hC _⟩
  exact hR.integrableOn_modGrowth_mul hν h𝓕 hg hinv hcont.measurable.aestronglyMeasurable

end GlobalTheory.DownConv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsChainPols
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipStart

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def colPure (W : G.Weil) (t : T) (f : ∀ j : Fin D.R.m, Sch G (.down t 0 j))
    (q : ∀ j : Fin D.R.m, PolF D (G.pT (.mu t 0 j)).rank (G.pS (.mu t 0 j)).rank) : PureT G (downPath t 0 D.R.m) :=
  downFam t 0 D.R.m fun j => W.fock (.mu t 0 j) (f j) (q j)

def givenFin (W : G.Weil) (t : T) (f : ∀ j : Fin D.R.m, Sch G (.down t 0 j)) (Φ : G.Datum) : PureT G (givenPath t D.R.m) :=
  Path.Fam.append (downFam t 0 D.R.m f) (rowFam 0 D.R.m fun i => W.cosVec i (Φ i))

def gPol (ρ : G.RealVec) (q : ∀ j : ℕ, PolF D (G.V (.grid 0 (j + 1))).rank (G.V (.grid 0 j)).rank) : PolE G
  | .ex i 0 => if h : i < D.R.m then ρ ⟨i, h⟩ else 0
  | .ex _ (_ + 1) => 0
  | .theta 0 j => q j
  | .theta (_ + 1) _ => 0

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def ChainVecs (ch : Choice R) (t : T) (f : ∀ j : Fin D.R.m, Sch ch.G (.down t 0 j)) : Prop :=
  ∀ j : Fin D.R.m, ((j : ℕ) + 1 < D.R.m → HEq (f j) (R.vY t j)) ∧ ((j : ℕ) + 1 = D.R.m → HEq (f j) (R.vX t))

def ChainPols (ch : Choice R) (q : ∀ j : ℕ, PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank) : Prop :=
  ∀ j : ℕ, (j + 1 < D.R.m → HEq (q j) (ch.cv.polY j)) ∧ (j + 1 = D.R.m → HEq (q j) ch.cv.polX)

theorem exists_heq_fun (Y Y' : LSp D) (S S' : HSp D) (Λ Λ') (hY : Y = ⟨S, Λ⟩) (hY' : Y' = ⟨S', Λ'⟩) (f : WO S S' → ℂ) :
    ∃ f' : WO Y.sp Y'.sp → ℂ, HEq f' f := by
  subst hY hY'; exact ⟨f, HEq.rfl⟩

theorem exists_heq_pol {a b a' b' : ℕ} (ha : a' = a) (hb : b' = b) (P : PolF D a b) : ∃ P' : PolF D a' b', HEq P' P := by
  subst ha hb; exact ⟨P, HEq.rfl⟩

theorem rank_col_lt (L : LevCh D T) {j : ℕ} (h : j < D.R.m) : (columnBlock L j).sp.rank = (Yc D j).rank := by
  rw [colY_lt L h]

theorem rank_col_m (L : LevCh D T) : (columnBlock L D.R.m).sp.rank = D.sp.X'.rank := by
  rw [colY_m L]

theorem exists_chainVecs (ch : Choice R) (t : T) : ∃ f, ChainVecs ch t f := by
  have H : ∀ j : Fin D.R.m, ∃ f : Sch ch.G (.down t 0 j),
      ((j : ℕ) + 1 < D.R.m → HEq f (R.vY t j)) ∧ ((j : ℕ) + 1 = D.R.m → HEq f (R.vX t)) := fun ⟨j, hj⟩ => by
    by_cases h : j + 1 < D.R.m
    · obtain ⟨f, e⟩ := exists_heq_fun (columnBlock R.toLevCh j) (columnBlock R.toLevCh (j + 1)) _ _ _ _ (colY_lt _ (by omega))
        (colY_lt _ h) (R.vY t j)
      exact ⟨f, fun _ => e, fun h' => by simp at h'; omega⟩
    · have e1 : j = D.R.m - 1 := by omega
      subst e1
      have e2 : columnBlock R.toLevCh (D.R.m - 1 + 1) = ⟨D.sp.X', R.ΛX⟩ := by
        rw [Nat.sub_add_cancel (by omega)]; exact colY_m _
      obtain ⟨f, e⟩ := exists_heq_fun (columnBlock R.toLevCh (D.R.m - 1)) (columnBlock R.toLevCh (D.R.m - 1 + 1)) _ _ _ _
        (colY_lt _ (by omega)) e2 (R.vX t)
      exact ⟨f, fun h' => absurd h' h, fun _ => e⟩
  choose f hf using H
  exact ⟨f, hf⟩

theorem exists_chainPols (ch : Choice R) : ∃ q, ChainPols ch q := by
  have H : ∀ j : ℕ, ∃ q : PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank,
      (j + 1 < D.R.m → HEq q (ch.cv.polY j)) ∧ (j + 1 = D.R.m → HEq q ch.cv.polX) := fun j => by
    by_cases h : j + 1 < D.R.m
    · obtain ⟨q, e⟩ := exists_heq_pol (rank_col_lt R.toLevCh h) (rank_col_lt R.toLevCh (by omega)) (ch.cv.polY j)
      exact ⟨q, fun _ => e, fun h' => by omega⟩
    · by_cases h' : j + 1 = D.R.m
      · have e1 : j = D.R.m - 1 := by omega
        subst e1
        have e2 : (columnBlock R.toLevCh (D.R.m - 1 + 1)).sp.rank = D.sp.X'.rank := by
          rw [Nat.sub_add_cancel (by omega)]; exact rank_col_m _
        obtain ⟨q, e⟩ := exists_heq_pol e2 (rank_col_lt R.toLevCh (by omega)) ch.cv.polX
        exact ⟨q, fun h'' => absurd h'' h, fun _ => e⟩
      · exact ⟨0, fun h'' => absurd h'' h, fun h'' => absurd h'' h'⟩
  choose q hq using H
  exact ⟨q, hq⟩

end GlobalTheory.FlipStart

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeIntegralUnitsEqResidueCharProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeIntegralUnitsEqResidueCharProduct
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TameProd

theorem val_lt_one_of_resS_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {K Γ : Type} [CommRing K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (P : Pl E) (g : Formalism.L2.Herm.intAf F E →+* K) (h1 : ∀ s, v (g s) ≤ 1)
    (h2 : ∀ a ∈ P.asIdeal, v (g (oToS F E a)) < 1) (s : Formalism.L2.Herm.intAf F E) (hs : resS F P s = 0) :
    v (g s) < 1 := by
  have hm : s ∈ idS F P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact (map_eq_zero_iff _ (RingEquiv.ofBijective (cmpS F P.asIdeal)
      (cmpS_bij (F := F) P.asIdeal P.ne_bot)).symm.injective).1 hs
  refine Submodule.span_induction (p := fun s _ => v (g s) < 1) ?_ ?_ ?_ ?_ hm
  · rintro _ ⟨a, ha, rfl⟩
    exact h2 a ha
  · rw [map_zero, map_zero]
    exact zero_lt_one
  · intro x y _ _ hx hy
    rw [map_add (f := _)]
    exact v.map_add_lt hx hy
  · intro c x _ hx
    rw [smul_eq_mul, map_mul, map_mul]
    exact (mul_le_of_le_one_left' (h1 c)).trans_lt hx

theorem val_sub_lt_one {D : D7} {K Γ : Type} [CommRing K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (P : Pl D.host.E) (G : Af D.host.F ⊗[D.host.F] D.host.E →+* K) (h1 : ∀ y ∈ intAE D, v (G y) ≤ 1)
    (h2 : ∀ a ∈ P.asIdeal, v (G ((1 : Af D.host.F) ⊗ₜ[D.host.F] (a : D.host.E))) < 1) (w : AE D)
    (hw : toEAf D w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (a : 𝓞 D.host.E)
    (h : resS D.host.F P ⟨toEAf D w, hw⟩ = Ideal.Quotient.mk _ a) :
    v (G (finPart D w) - G ((1 : Af D.host.F) ⊗ₜ[D.host.F] (a : D.host.E))) < 1 := by
  let c := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E)
  let g : Formalism.L2.Herm.intAf D.host.F D.host.E →+* K :=
    (G.comp c.symm.toRingEquiv.toRingHom).comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype
  have hg : ∀ s, g s = G (c.symm s.1) := fun _ => rfl
  have hgo : ∀ b : 𝓞 D.host.E, g (oToS D.host.F D.host.E b) =
      G ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) := fun _ => rfl
  have key := val_lt_one_of_resS_eq_zero v P g
    (fun s => h1 _ ((GlobalTheory.HostAdeleIso.mem_intAE_iff_comm D _).2 (by
      have : c (c.symm s.1) = s.1 := c.apply_symm_apply _
      exact this.symm ▸ s.2)))
    (fun b hb => by rw [hgo]; exact h2 b hb) (⟨toEAf D w, hw⟩ - oToS D.host.F D.host.E a)
    (by rw [RingHom.map_sub, h, resS_oToS, sub_self])
  rw [RingHom.map_sub, hgo, hg] at key
  have e : c.symm (toEAf D w) = finPart D w := c.symm_apply_apply _
  rwa [e] at key

theorem resS_idem_eq_zero {D : D7} {e : AE D} {P Q : Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e P) (hQ : P ≠ Q)
    (h : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) : resS D.host.F Q ⟨toEAf D e, h⟩ = 0 := by
  have hnle : ¬ Q.asIdeal ≤ P.asIdeal := fun hle =>
    hQ (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top hle)).symm
  obtain ⟨x, hxQ, hxP⟩ := Set.not_subset.1 hnle
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxP P.asIdeal.zero_mem
  have hx0' : (x : D.host.E) ≠ 0 := fun h => hx0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  have hi : finPart D (e * incA D ((x : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra hn
    exact hxP ((he.2 x hx0).2 hn)
  have e1 : (⟨toEAf D e, h⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      ⟨_, GlobalTheory.IdemRes.toEAf_mem_of_finPart hi⟩ * oToS D.host.F D.host.E x := by
    apply Subtype.ext
    change toEAf D e = toEAf D (e * incA D ((x : D.host.E)⁻¹)) * toEAf D (incA D (x : D.host.E))
    rw [← RingHom.map_mul, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ hx0', RingHom.map_one, mul_one]
  rw [e1, RingHom.map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hxQ, mul_zero]

theorem map_sum_ringHom {A B ι : Type} [Semiring A] [Semiring B] (f : A →+* B) (s : Finset ι) (g : ι → A) :
    f (∑ i ∈ s, g i) = ∑ i ∈ s, f (g i) := map_sum f g s

theorem resS_idemSum {D : D7} {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) :
    ∃ h : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ∀ Q ∈ P, resS D.host.F Q ⟨toEAf D e, h⟩ = 1 := by
  classical
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  choose hi hr using fun Q : P => GlobalTheory.IdemRes.resS_idem_eq_one D (es Q) Q (hes Q Q.2)
  let t : P → Formalism.L2.Herm.intAf D.host.F D.host.E := fun Q => ⟨toEAf D (es Q), hi Q⟩
  have ht : toEAf D (∑ PP ∈ P, es PP) = ((∑ Q, t Q : Formalism.L2.Herm.intAf D.host.F D.host.E) : Datum.EAf D) := by
    rw [← Finset.sum_coe_sort P]
    refine (map_sum_ringHom (toEAf D) _ _).trans ?_
    exact (map_sum (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype t Finset.univ).symm
  refine ⟨ht ▸ (∑ Q, t Q).2, fun Q hQ => ?_⟩
  have e1 : (⟨toEAf D (∑ PP ∈ P, es PP), ht ▸ (∑ Q, t Q).2⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ∑ Q, t Q :=
    Subtype.ext ht
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e1, map_sum, Finset.sum_eq_single (⟨Q, hQ⟩ : P)]
  · exact hr ⟨Q, hQ⟩
  · intro R _ hR
    exact resS_idem_eq_zero (hes R R.2) (fun h => hR (Subtype.ext h)) _
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem le_exp_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  by_cases h0 : x = 0
  · rw [h0]
    exact zero_le
  · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega

theorem loc_eq_of_tame {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (Q : HeightOneSpectrum (𝓞 L))
    (ht : χ.TameAt Q) (y z : (Q.adicCompletion L)ˣ) (hz : Valued.v (z : Q.adicCompletion L) = 1)
    (h : Valued.v ((y : Q.adicCompletion L) - z) < 1) : χ.loc Q y = χ.loc Q z := by
  have hy : Valued.v (y : Q.adicCompletion L) = 1 := by
    rw [← hz]
    exact Valuation.map_eq_of_sub_lt _ (hz ▸ h)
  have h1 : χ.loc Q (y * z⁻¹) = 1 := by
    refine ht _ ?_ (le_exp_of_lt_one ?_)
    · show Valued.v ((y * z⁻¹ : (Q.adicCompletion L)ˣ) : Q.adicCompletion L) = 1
      rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hy, hz, inv_one, mul_one]
    · have : ((y * z⁻¹ : (Q.adicCompletion L)ˣ) : Q.adicCompletion L) - 1 =
          ((y : Q.adicCompletion L) - z) * (z : Q.adicCompletion L)⁻¹ := by
        rw [Units.val_mul, Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ z.ne_zero]
      rw [this, map_mul, map_inv₀, hz, inv_one, mul_one]
      exact h
  rwa [map_mul, map_inv, mul_inv_eq_one] at h1

theorem tameOn_of_tame : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (e : AE D) (P : Finset (Pl D.host.E)) (cR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), ChrEq c χ → (∀ PP, χ.TameAt PP) → IsIdemSum e P → (∀ PP, PP ∉ P → (¬ ∃ PP' ∈ P, Lev.IsConjPl (D := D) PP' PP) → χ.UnrAt PP) → (∀ PP ∈ P, IsRes χ PP (cR PP)) → TameOn c e P cR := by
  classical
  intro D c χ e P cR hc ht he hunr hres x hx1 hx2 hx3 hxe u hu
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc
  let G : ∀ Q : Pl D.host.E, Af D.host.F ⊗[D.host.F] D.host.E →+* Q.adicCompletion D.host.E :=
    fun Q => (GlobalTheory.CharLocProd.evalAt Q).comp ι.toRingHom
  have hG : ∀ Q y, G Q y = ι y Q := fun _ _ => rfl
  have hG1 : ∀ (Q : Pl D.host.E) (a : D.host.E), G Q ((1 : Af D.host.F) ⊗ₜ[D.host.F] a) = algebraMap D.host.E _ a :=
    fun Q a => (congrArg (GlobalTheory.CharLocProd.evalAt Q) (h1 a)).trans (GlobalTheory.CharLocProd.evalAt_algebraMap Q a)
  have hGint : ∀ Q, ∀ y ∈ intAE D, Valued.v (G Q y) ≤ 1 := fun Q y hy => (h2 y).1 hy Q
  have hGlt : ∀ (Q : Pl D.host.E), ∀ a ∈ Q.asIdeal,
      Valued.v (G Q ((1 : Af D.host.F) ⊗ₜ[D.host.F] (a : D.host.E))) < 1 := by
    intro Q a ha
    rw [hG1, GlobalTheory.CharLocProd.val_algebraMap]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E) Q a).2 ha
  have hv : ∀ Q, Valued.v (G Q (finPart D (x : AE D))) = 1 := by
    intro Q
    have a := hGint Q _ (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf hx2)
    have b := hGint Q _ (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf hx3)
    have e' : Valued.v (G Q (finPart D (x : AE D))) * Valued.v (G Q (finPart D ((x⁻¹ : (AE D)ˣ) : AE D))) = 1 := by
      rw [← map_mul, ← RingHom.map_mul, ← RingHom.map_mul, Units.mul_inv, RingHom.map_one, RingHom.map_one, map_one]
    refine le_antisymm a ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := e'.symm
      _ ≤ Valued.v (G Q (finPart D (x : AE D))) * 1 := mul_le_mul_right b _
      _ = _ := mul_one _
  choose k hk using fun Q : Pl D.host.E => GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN Q
    (G Q (finPart D (x : AE D))) (fun h => by
      have := hv Q
      rw [h, map_zero] at this
      exact zero_ne_one this)
  have hkc : ∀ Q, Valued.v (G Q (finPart D (x : AE D)) - algebraMap D.host.E _ (k Q : D.host.E)) < 1 := by
    intro Q
    have b := (hk Q).2.2
    rw [← (hk Q).1, hv, mul_one] at b
    refine b.trans_lt ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hloc : ∀ (Q : Pl D.host.E) (z : D.host.Eˣ), Q.valuation D.host.E (z : D.host.E) = 1 →
      Valued.v (G Q (finPart D (x : AE D)) - algebraMap D.host.E _ (z : D.host.E)) < 1 →
      χ.locK Q (k Q) = χ.locK Q z := by
    intro Q z hz h
    refine loc_eq_of_tame χ Q (ht Q) _ _ ((GlobalTheory.CharLocProd.val_algebraMap Q _).trans hz) ?_
    have e4 : ((Formalism.L2.Host.atFin Q (k Q) : (Q.adicCompletion D.host.E)ˣ) : Q.adicCompletion D.host.E) -
        (Formalism.L2.Host.atFin Q z : (Q.adicCompletion D.host.E)ˣ) =
        (G Q (finPart D (x : AE D)) - algebraMap D.host.E _ (z : D.host.E)) -
          (G Q (finPart D (x : AE D)) - algebraMap D.host.E _ (k Q : D.host.E)) := by
      show algebraMap D.host.E _ (k Q : D.host.E) - algebraMap D.host.E _ (z : D.host.E) = _
      ring
    rw [e4]
    exact Valuation.map_sub_lt _ h (hkc Q)
  have hfin : {Q : Pl D.host.E | Q.asIdeal ∣ Ideal.span {(N : 𝓞 D.host.E)}}.Finite :=
    Ideal.finite_factors (by simpa [Ideal.span_singleton_eq_bot] using hN.ne')
  have key := hprod x hx1 (P ∪ hfin.toFinset) k (fun Q _ => ⟨(hk Q).1, (hk Q).2.1⟩) (fun Q hQ => ⟨hv Q, fun h =>
    hQ (Finset.mem_union_right _ (hfin.mem_toFinset.2 (Ideal.dvd_span_singleton.2 h)))⟩)
  obtain ⟨hei, her⟩ := resS_idemSum he
  rw [key]
  refine (Finset.prod_subset Finset.subset_union_left fun Q _ hQ => ?_).symm.trans
    (Finset.prod_congr rfl fun Q hQ => ?_)
  · rw [Units.val_eq_one]
    by_cases hcj : ∃ PP' ∈ P, Lev.IsConjPl (D := D) PP' Q
    · obtain ⟨R, hR, hRQ⟩ := hcj
      have h5 := val_sub_lt_one Valued.v R ((G Q).comp (sigR (Af D.host.F) D.sp.cm.sig))
        (fun y hy => hGint Q _ (GlobalTheory.PlaceIdem.sig_mem D hy))
        (fun a ha => by
          obtain ⟨b, hb, hab⟩ := hRQ a ha
          have := hGlt Q b hb
          rw [hab] at this
          exact this) e hei 1 (by rw [her R hR, RingHom.map_one])
      have h6 : ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E)) = 1 := rfl
      rw [h6, RingHom.map_one, RingHom.comp_apply, ← GlobalTheory.PlaceIdem.finPart_cA] at h5
      have h7 : G Q (finPart D (cA D e)) ≠ 0 := by
        intro h
        rw [h, zero_sub, Valuation.map_neg, map_one] at h5
        exact lt_irrefl _ h5
      have h8 : G Q (finPart D (x : AE D)) = 1 := by
        refine mul_left_cancel₀ h7 ?_
        rw [← RingHom.map_mul, ← RingHom.map_mul, hxe, mul_one]
      rw [hloc Q 1 (by rw [Units.val_one, map_one]) (by
        rw [h8, Units.val_one, map_one, sub_self, map_zero]
        exact zero_lt_one), map_one]
    · exact hunr Q hQ hcj _ ((GlobalTheory.CharLocProd.val_algebraMap Q _).trans ((hk Q).1.symm.trans (hv Q)))
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u Q : kP Q)
    have haQ : a ∉ Q.asIdeal := by
      intro h
      have := Q.isPrime
      exact (u Q).ne_zero (ha ▸ Ideal.Quotient.eq_zero_iff_mem.2 h)
    have ha0 : (a : D.host.E) ≠ 0 := fun h => haQ (RingOfIntegers.coe_eq_zero_iff.1 h ▸ Q.asIdeal.zero_mem)
    have h5 := val_sub_lt_one Valued.v Q (G Q) (hGint Q) (hGlt Q) x hx2 a ((hu Q hQ).symm.trans ha.symm)
    rw [hG1] at h5
    rw [hres Q hQ a (Units.mk0 _ ha0) (u Q) rfl ha.symm, hloc Q (Units.mk0 _ ha0)
      ((HeightOneSpectrum.valuation_eq_one_iff_notMem (K := D.host.E) Q (r := a)).2 haQ) h5]

end GlobalTheory.TameProd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeIntegralUnitsEqResidueCharProductStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameHecke_integralUnits_eq_residueCharProduct : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (e : AE D) (P : Finset (Pl D.host.E)) (cR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), ChrEq c χ → (∀ PP, χ.TameAt PP) → IsIdemSum e P → (∀ PP, PP ∉ P → (¬ ∃ PP' ∈ P, Lev.IsConjPl PP' PP) → χ.UnrAt PP) → (∀ PP ∈ P, IsRes χ PP (cR PP)) → TameOn c e P cR := by
  first | exact @GlobalTheory.TameProd.tameOn_of_tame | exact GlobalTheory.TameProd.tameOn_of_tame | (intros; apply GlobalTheory.TameProd.tameOn_of_tame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleNegSpaceUnitaryElementHeq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.UpConjLift

variable {D : D7}

theorem negSp_neg (S : HSp D) : negSp (GlobalTheory.Grid.neg S) = S := by
  cases S
  simp only [negSp, GlobalTheory.Grid.sgn, cond_true, neg_neg, Prod.swap_swap]

theorem isAutFunSm_of_eq {θ : InfFam D} {S₂ S : HSp D} (e : S₂ = S) {F : GA D S₂ → ℂ} {F' : GA D S → ℂ}
    (hF : ∀ x y, x ≍ y → F x = F' y) (h : IsAutFunSm θ S₂ F) : IsAutFunSm θ S F' := by
  subst e
  have : F = F' := funext fun x => hF x x HEq.rfl
  rwa [← this]

def j2 (S : HSp D) (y : GA D S) : GA D (negSp (GlobalTheory.Grid.neg S)) :=
  negGA (GlobalTheory.Grid.neg S) ((GlobalTheory.Grid.ofSgn true S).symm y)

theorem doubleNegSpaceUnitaryElement_heq (S : HSp D) (y : GA D S) : j2 S y ≍ y := by
  refine (Subtype.heq_iff_coe_eq fun z => ?_).2 rfl
  show z ∈ HR (AF D.host.F) D.sp.cm.sig (-(-S.gram)) ↔ z ∈ HR (AF D.host.F) D.sp.cm.sig S.gram
  rw [neg_neg]

theorem conj_lift (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ}
    {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} (ω : GlobalTheory.Grid.WRep S T)
    (hw : IsWeilDatumO ψ (GlobalTheory.Grid.neg S) T χS χT (ω.toSgn true)) {Φ : WO S T → ℂ}
    (hΦ : IsThetaFunO ψ (GlobalTheory.Grid.neg S) T Φ) {μ : Measure (GA D T)} {𝓕 : Set (GA D T)} (hq : GlobalTheory.Mem.Th.IsQuot T μ 𝓕)
    {φ : GA D T → ℂ} (hφ : GlobalTheory.Mem.Th.IsCuspForm θ T φ) :
    (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO ω h g Φ) * φ g) 𝓕 μ) ∧
      IsAutFunSm θ S fun h => ∫ g in 𝓕, starRingEnd ℂ (thetaKO ω h g Φ) * φ g ∂μ := by
  have hw2 := GlobalTheory.ConjWeil.weil_conjSource D ψ (GlobalTheory.Grid.neg S) T χS χT (ω.toSgn true) hw
  have K := (GlobalTheory.Mem.Lift.isKerSys_thKer hθ hw2.std (GlobalTheory.Ker.isWeak_of_datum hw2) hw2.om_cont).swap
  have hf : IsThetaFunO ψ (negSp (GlobalTheory.Grid.neg S)) T (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id Φ) :=
    ((GlobalTheory.CjNeg.theta_heis_neg D ψ hw.std (GlobalTheory.Grid.neg S) T).1 Φ).2.2 hΦ
  obtain ⟨h1, h2⟩ := K.lift hP hθ hq hφ ⟨_, hf⟩
  have key : ∀ y g, GlobalTheory.Mem.Lift.swapKer (GlobalTheory.Mem.Lift.thKer ψ _ T (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjSource (ω.toSgn true)))
      ⟨_, hf⟩ g (j2 S y) = starRingEnd ℂ (thetaKO ω y g Φ) := by
    intro y g
    show starRingEnd ℂ (ω (y, g) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id Φ)) 0) = starRingEnd ℂ (ω (y, g) Φ 0)
    rw [GlobalTheory.ConjWeil.cj_id_cj_id]
  refine ⟨fun h => ?_, isAutFunSm_of_eq (negSp_neg S) (fun x y hxy => ?_) h2⟩
  · have := h1 (j2 S h)
    simp only [key] at this
    exact this
  · have e : x = j2 S y := eq_of_heq (hxy.trans (doubleNegSpaceUnitaryElement_heq S y).symm)
    subst e
    simp only [key]

end GlobalTheory.UpConjLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqFinClSumAvg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.DefiniteClassReal

theorem isReps_transfer {Γ A B : Type} [Group Γ] [Group A] [Group B] (ι : Γ →* A) (ι' : Γ →* B) (e : A ≃* B)
    (he : ∀ γ, e (ι γ) = ι' γ) (J : Subgroup A) (J' : Subgroup B) (hJ : ∀ a, e a ∈ J' ↔ a ∈ J) {I : Type} (y : I → A)
    (h : Bridge.IsReps ι J y) : Bridge.IsReps ι' J' (fun i => e (y i)) := by
  intro b
  obtain ⟨i, ⟨γ, k, hk⟩, hu⟩ := h (e.symm b)
  refine ⟨i, ⟨γ, ⟨e k, (hJ k).2 k.2⟩, ?_⟩, ?_⟩
  · have := congrArg e hk
    rw [e.apply_symm_apply] at this
    rw [this, map_mul, map_mul, he]
  · rintro j ⟨γ', k', hk'⟩
    refine hu j ⟨γ', ⟨e.symm k', (hJ _).1 (by rw [e.apply_symm_apply]; exact k'.2)⟩, ?_⟩
    apply e.injective
    rw [e.apply_symm_apply, hk', map_mul, map_mul, he, e.apply_symm_apply]

theorem stab_transfer {Γ A B : Type} [Group Γ] [Group A] [Group B] (ι : Γ →* A) (ι' : Γ →* B) (e : A ≃* B)
    (he : ∀ γ, e (ι γ) = ι' γ) (J : Subgroup A) (J' : Subgroup B) (hJ : ∀ a, e a ∈ J' ↔ a ∈ J) (x : A) :
    Bridge.stab ι' J' (e x) = Bridge.stab ι J x := by
  ext γ
  rw [Bridge.mem_stab, Bridge.mem_stab, ← he, ← map_inv, ← map_mul, ← map_mul, hJ]

end GlobalTheory.DefiniteClassReal

namespace GlobalTheory.DefiniteClassReal
open GlobalTheory.FunObj GlobalTheory.ClassRegroup GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral GlobalTheory.DefiniteClassAvg

theorem integral_eq_finClSum_avg : ∀ {D : D7} (V : HSp D), (∀ φ : D.host.E →+* ℂ, (V.gram.map φ).PosDef) →
    ∀ (K K'' : Subgroup (GL (Fin V.rank) (Lev.EAf D))), IsOpenCompactLevel V K → IsOpenCompactLevel V K'' → K'' ≤ K →
    ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsMeasDef V K μ 𝓕 → ∀ (Φ : GA D V → ℂ),
    (∀ γ ∈ GQ V, ∀ g, Φ (γ * g) = Φ g) → (∀ k ∈ Lev.levA V K'', ∀ g, Φ (g * k) = Φ g) →
    (∀ z, Continuous fun k : GinfC V => Φ (z * k)) →
    Finite (FinCl V K'') ∧ ∃ κ : Measure (GinfC V), κ.IsHaarMeasure ∧ IsProbabilityMeasure κ ∧
      ∫ g in 𝓕, Φ g ∂μ = ∑ᶠ c : FinCl V K'',
        ((μ ((K''.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V))).toReal : ℂ) / (gamOrd V K'' c.out : ℂ) *
          ∫ k, Φ ((c.out : GA D V) * k) ∂κ := by
  intro D V hV K K'' hK hK'' hle μ 𝓕 hμ Φ hl hr hc

  let V' : HSp D := { V with sig := fun _ => (V.rank, 0) }
  have hS' : V'.SigOK := fun τ => GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef (hV τ)
  have hD' : V'.IsDefinite := fun τ => Or.inl rfl
  have hGc : IsCompact (GinfC V : Set (GA D V)) := Formalism.IndefR.Eqv.isCompact_GinfC (V := V') hS' hD'
  haveI : CompactSpace (GinfC V) := isCompact_iff_compactSpace.1 hGc
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hLC := hT.1
  have hSC := hT.2.1
  have hB := hT.2.2.2.1
  have hG := hT.2.2.2.2.1
  have hC := hT.2.2.2.2.2.2
  have hHaar := hμ.1.1
  have hfin0 : Finite (FinCl V K'') := (finite_finCl_and_gamOrd V K'' hV hK'').1
  letI : Fintype (FinCl V K'') := Fintype.ofFinite _

  let κ : Measure (GinfC V) := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (GinfC V))
  haveI hκH : κ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  have hκ1 : κ Set.univ = 1 := by
    have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (GinfC V)))
    simpa using this
  haveI : IsProbabilityMeasure κ := ⟨hκ1⟩
  refine ⟨hfin0, κ, hκH, inferInstance, ?_⟩

  let e := finEquiv V
  have he : ∀ γ, e (((finPt V).comp (GQ V).subtype) γ) = Bridge.ratF V γ := fun γ => e.apply_symm_apply _
  have hJe : ∀ a, e a ∈ levelFin V K'' ↔ a ∈ K''.comap (finG V) := fun a => Iff.rfl
  have hy := isReps_transfer _ _ e he _ _ hJe _ (isReps_out V K'')
  let y : FinCl V K'' → Bridge.Gf V := fun c => e (Quotient.out c)
  let z : FinCl V K'' → GA D V := fun c => ((Quotient.out c : GfC V) : GA D V)
  have hz : ∀ c, (finHom V).rangeRestrict (z c) = y c := fun c => rfl

  let J : Subgroup (GA D V) := K''.comap (Lev.finE V)
  let JK : Subgroup (GA D V) := K.comap (Lev.finE V)
  have hJo : IsOpen (J : Set (GA D V)) := hK''.1
  have hJJK : J ≤ JK := fun x hx => hle hx
  have hJK1 : μ JK = 1 := GlobalTheory.Mass.Levels.measure_comap_finE hμ.1
  have hJtop : μ J ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [hJK1]; exact ENNReal.one_ne_top) (measure_mono (fun x hx => hJJK hx))
  have hJ0 : μ J ≠ 0 := (hJo.measure_pos μ ⟨1, J.one_mem⟩).ne'
  have hinfJ : GinfC V ≤ J := by
    show GinfC V ≤ K''.comap (Lev.finE V)
    rw [GlobalTheory.Mass.Levels.comap_finE]
    exact le_sup_right
  have hcont : Continuous Φ := continuous_of_level V K'' hK''.1 Φ hr hc
  have hu : ∀ x : GA D V, ∃! c, ∃ γ ∈ GQ V, ∃ k ∈ J, x = γ * z c * k :=
    existsUnique_doubleCoset (finHom V).rangeRestrict (GQ V) (levelFin V K'') y hy z hz
  have hs : ∀ c, (classGroupAt V K'' (y c) : Set (GQ V)) = {γ : GQ V | (z c)⁻¹ * (γ : GA D V) * z c ∈ J} := by
    intro c
    ext γ
    rw [SetLike.mem_coe, ← hz c, mem_classGroupAt]
    rfl
  have hfinΓ : ∀ c, {γ : GQ V | (z c)⁻¹ * (γ : GA D V) * z c ∈ J}.Finite := fun c =>
    GlobalTheory.InnerClassSum.finite_stab_of_measure μ (GQ V) J hμ.2 hJ0 hJtop (z c)
  have him : ∀ c, {γ : GA D V | γ ∈ GQ V ∧ (z c)⁻¹ * γ * z c ∈ J} =
      Subtype.val '' {γ : GQ V | (z c)⁻¹ * (γ : GA D V) * z c ∈ J} := by
    intro c
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
    exact ⟨fun h => ⟨h.1, h.2⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩
  have hfin : ∀ c, {γ : GA D V | γ ∈ GQ V ∧ (z c)⁻¹ * γ * z c ∈ J}.Finite := fun c =>
    him c ▸ (hfinΓ c).image _
  have hdec : ∀ k ∈ J, ∃ k' ∈ Lev.levA V K'', ∃ w : GinfC V, k = k' * (GinfC V).subtype w := fun k hk =>
    ⟨finPart V k, finPart_mem_levA V hk, ⟨realPart V k, realPart_mem V k⟩, (finPart_mul_realPart V k).symm⟩
  have hcomm : ∀ k ∈ Lev.levA V K'', ∀ w : GinfC V, k * (GinfC V).subtype w = (GinfC V).subtype w * k :=
    fun k hk w => (Eqv.Act.comm_inf_fin w.2 (Subgroup.mem_inf.1 hk).1).symm
  have hrt : ∀ w : GinfC V, MeasurePreserving (· * (GinfC V).subtype w) μ μ := fun w =>
    measurePreserving_mul_right_of_mem μ J hJo hJ0 hJtop (hinfJ w.2)
  obtain ⟨-, heq⟩ := integral_eq_sum_avg (GA D V) μ (GQ V) J (Lev.levA V K'') 𝓕 hμ.2 hJo hJtop (GinfC V) κ
    (GinfC V).subtype continuous_subtype_val hrt hdec hcomm (FinCl V K'') z hu hfin Φ hcont hl hr
  rw [heq, Finset.mul_sum, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hcard : Nat.card (classGroupAt V K'' (y c)) = gamOrd V K'' (Quotient.out c) := by
    show Nat.card (Bridge.stab (Bridge.ratF V) (levelFin V K'') (e (Quotient.out c))) = _
    rw [stab_transfer _ _ e he _ _ hJe]
    exact card_stab V K'' _
  have hcard' : ((classGroupAt V K'' (y c) : Set (GQ V))).ncard = gamOrd V K'' (Quotient.out c) :=
    (Nat.card_coe_set_eq _).symm.trans hcard
  rw [him, Set.ncard_image_of_injective _ Subtype.val_injective, ← hs, hcard', div_eq_mul_inv, mul_assoc]
  rfl

end GlobalTheory.DefiniteClassReal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftLowerTowerVanishing
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftLowerTowerVanishing
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.ChainFr GlobalTheory.Size GlobalTheory.Grow GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift
open scoped ENNReal NNReal

namespace GlobalTheory.LowVanishObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Kernel

variable {V W : HSp D} (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (g : GA D V) (h : GA D W)

theorem thetaKO_zero : thetaKO ω g h 0 = 0 := by
  simp [thetaKO]

theorem thetaKO_add (f f' : WO V W → ℂ) : thetaKO ω g h (f + f') = thetaKO ω g h f + thetaKO ω g h f' := by
  simp [thetaKO]

theorem thetaKO_sub (f f' : WO V W → ℂ) : thetaKO ω g h (f - f') = thetaKO ω g h f - thetaKO ω g h f' := by
  simp [thetaKO]

theorem thetaKO_smul (c : ℂ) (f : WO V W → ℂ) : thetaKO ω g h (c • f) = c * thetaKO ω g h f := by
  simp [thetaKO]

end Kernel

theorem multT_apply_cusp {W : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel W S) (J : Set (GA D W))
    (χ : GA D W → ℂ) (F : SmT M →ₗ[ℂ] (GA D W → ℂ)) (hF : F ∈ MultT θ M J χ) (v : SmT M) :
    IsAutFunSm θ W (F v) ∧ IsCuspFun W (F v) := by
  have hT : IsMultMap θ M J χ (PiTensorProduct.lift.symm F) :=
    (GlobalTheory.MultMem.mem_mult_iff D θ W S M J χ _).1 ((mem_multT θ M J χ F).1 hF)
  have hFv : ∀ x, F x = PiTensorProduct.lift (PiTensorProduct.lift.symm F) x := fun x => by
    rw [LinearEquiv.apply_symm_apply]
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [hFv, LinearMap.map_smul, PiTensorProduct.lift.tprod]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_smul r (hT.aut x), GlobalTheory.MultMem.isCuspFun_smul r (hT.cusp x)⟩
  | add a b ha hb =>
    rw [map_add (f := _)]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add ha.1 hb.1,
      GlobalTheory.MultMem.isCuspFun_add ha.1.toIsAutFun hb.1.toIsAutFun ha.2 hb.2⟩

theorem liftInt_span_eq_zero {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {Φ : GA D W → ℂ}
    (hI : ∀ f, IsThetaFunO ψ V W f → ∀ x, IntegrableOn (fun h => thetaKO ω x h f * Φ h) 𝓕 ν)
    {s : Set (WO V W → ℂ)} (hs : ∀ g ∈ s, IsThetaFunO ψ V W g ∧ Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0) :
    ∀ g ∈ Submodule.span ℂ s, IsThetaFunO ψ V W g ∧ Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0 := by
  intro g hg
  induction hg using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero =>
    refine ⟨GlobalTheory.OrientedHeis.theta_zero, ?_⟩
    funext x
    simp [Lift.liftInt, thetaKO_zero]
  | add a b _ _ ha hb =>
    refine ⟨GlobalTheory.OrientedHeis.theta_add ha.1 hb.1, ?_⟩
    funext x
    have h1 := congrFun ha.2 x
    have h2 := congrFun hb.2 x
    simp only [Lift.liftInt, Pi.zero_apply] at h1 h2 ⊢
    simp only [thetaKO_add, add_mul]
    rw [integral_add (hI a ha.1 x) (hI b hb.1 x), h1, h2, add_zero]
  | smul c a _ ha =>
    refine ⟨GlobalTheory.OrientedHeis.theta_smul c ha.1, ?_⟩
    funext x
    have h1 := congrFun ha.2 x
    simp only [Lift.liftInt, Pi.zero_apply] at h1 ⊢
    simp only [thetaKO_smul, mul_assoc]
    rw [integral_const_mul, h1, mul_zero]

theorem eq_zero_of_le_mul_pos {a K : ℝ≥0∞} (hK : K ≠ ∞) (h : ∀ δ : ℝ≥0∞, 0 < δ → a ≤ K * δ) : a = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  rw [zero_add]
  rcases eq_or_ne K 0 with rfl | hK0
  · exact (h 1 one_pos).trans (by simp)
  · have hε' : (ε : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hε.ne'
    have := h (ε / K) (ENNReal.div_pos hε' hK)
    rwa [ENNReal.mul_div_cancel hK0 hK] at this

theorem liftInt_eq_zero_of_approx {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)}
    {cls : (GA D W → ℂ) → Prop} (hL : LiftLaws θ ψ ω ν 𝓕 cls) {Φ : GA D W → ℂ} (hΦ : cls Φ)
    {μ : Measure (WO V W)} {𝓓 : Set (WO V W)} (hμ : μ.IsAddHaarMeasure)
    (h𝓓 : IsAddFundamentalDomain (ratL W V) 𝓓 μ) {U : AddSubgroup (WO V W)} (hU : IsOpen (U : Set (WO V W)))
    {f : WO V W → ℂ} (hf : f ∈ GlobalTheory.Size.thetaLevel ψ V W U)
    (happ : ∀ (d : ℕ) (δ : ℝ≥0∞), 0 < δ → ∃ g ∈ GlobalTheory.Size.thetaLevel ψ V W U,
      Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0 ∧ sobO ψ θ μ 𝓓 d (f - g) < δ) :
    Lift.liftInt ν 𝓕 (thetaKO ω) f Φ = 0 := by
  obtain ⟨A, hA⟩ := hL.bound
  obtain ⟨d, hd⟩ := hA 0
  obtain ⟨C, hC⟩ := hd μ 𝓓 hμ h𝓓 U hU
  have hint : ∀ f', IsThetaFunO ψ V W f' → ∀ x,
      IntegrableOn (fun h => thetaKO ω x h f' * Φ h) 𝓕 ν := fun f' hf' x => by
    simpa [rTr] using hL.integ f' Φ hf' hΦ x 1
  have key : ∀ g ∈ GlobalTheory.Size.thetaLevel ψ V W U, Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0 →
      growthSob θ V 0 A (lift ω ν 𝓕 f Φ) ≤ C * sobO ψ θ μ 𝓓 d (f - g) * decayInt ν 𝓕 A Φ := by
    intro g hg hg0
    have hb := hC (f - g) (sub_mem hf hg) Φ hΦ
    have heq : lift ω ν 𝓕 (f - g) Φ = lift ω ν 𝓕 f Φ := by
      funext x
      have h0 := congrFun hg0 x
      simp only [lift, Lift.liftInt, Pi.zero_apply] at h0 ⊢
      simp only [thetaKO_sub, sub_mul]
      rw [integral_sub (hint f hf.1 x) (hint g hg.1 x), h0, sub_zero]
    rwa [heq] at hb
  have hdec := hL.decay_ne_top Φ hΦ A
  have hz : growthSob θ V 0 A (lift ω ν 𝓕 f Φ) = 0 := by
    refine eq_zero_of_le_mul_pos (K := C * decayInt ν 𝓕 A Φ) (ENNReal.mul_ne_top ENNReal.coe_ne_top hdec) ?_
    intro δ hδ
    obtain ⟨g, hg, hg0, hsm⟩ := happ d δ hδ
    calc growthSob θ V 0 A (lift ω ν 𝓕 f Φ)
        ≤ C * sobO ψ θ μ 𝓓 d (f - g) * decayInt ν 𝓕 A Φ := key g hg hg0
      _ ≤ C * δ * decayInt ν 𝓕 A Φ := by gcongr
      _ = C * decayInt ν 𝓕 A Φ * δ := by ring
  have hz' : growthSize V A (lift ω ν 𝓕 f Φ) = 0 := by simpa [growthSob] using hz
  unfold growthSize at hz'
  funext x
  have hx := ENNReal.ofReal_eq_zero.1 ((ENNReal.iSup_eq_zero.1 hz') x)
  have hpos : 0 < height V x ^ A := pow_pos (lt_of_lt_of_le one_pos ((height_laws V).1 x)) A
  rw [div_le_iff₀ hpos, zero_mul] at hx
  exact norm_le_zero_iff.1 hx

theorem lowVanish_obj : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.LowVanish D := by
  intro h1 h2 h3 D k i V' W M' θ ψ hθ hk hi hsig ω' hω' ν 𝓕 hν h𝓕 J χ F hF v f' hf'
  obtain ⟨χS, χT, hW, hexp⟩ := hω'
  have hLaws := GlobalTheory.Chain.LiftReg.liftProps_obj h3 D V' W θ ψ χS χT ω' hθ hW ν 𝓕 hν h𝓕
  have hcv := multT_apply_cusp θ M' J χ F hF v
  obtain ⟨A⟩ := (GlobalTheory.FrameExists.frame_exists_signCompat D V').1
  obtain ⟨μ, 𝓓, hcov⟩ := GlobalTheory.Size.exists_isCovolOne V' W
  have hstd : IsStdChar D ψ (-1) := hW.std
  obtain ⟨U, hU, hfU, happ⟩ :=
    GlobalTheory.FockDensity.fockDense D V' W A (Fr.ofModel M') θ ψ hstd hθ μ 𝓓 hcov f' hf'
  have hint : ∀ f, IsThetaFunO ψ V' W f → ∀ x, IntegrableOn (fun h => thetaKO ω' x h f * F v h) 𝓕 ν :=
    fun f hf x => by simpa [rTr] using hLaws.integ f (F v) hf hcv x 1
  refine liftInt_eq_zero_of_approx hLaws hcv (μ := μ) (𝓓 := 𝓓) hcov.1 hcov.2.1 hU hfU ?_
  intro d δ hδ
  obtain ⟨g, hg, hgU, hsm⟩ := happ d δ hδ
  refine ⟨g, hgU, ?_, hsm⟩
  refine (liftInt_span_eq_zero hint ?_ g hg).2
  rintro _ ⟨f₀, P, hvac, -, rfl⟩
  refine ⟨?_, ?_⟩
  · exact GlobalTheory.Chain.InnerSteps.theta_pureTensorO hstd hθ A.cart A.onb (Fr.ofModel M').cart
      (Fr.ofModel M').onb hvac.1 P
  · exact GlobalTheory.LowerMembers.lowVanishFock h1 h2 h3 D k i V' W M' θ ψ hθ hk hi hsig ω' ⟨χS, χT, hW, hexp⟩
      ν 𝓕 hν h𝓕 J χ F hF v A f₀ hvac P

end GlobalTheory.LowVanishObj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftLowerTowerVanishingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_lowerTower_vanishing : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.LowVanish D := by
  first | exact @GlobalTheory.LowVanishObj.lowVanish_obj | exact GlobalTheory.LowVanishObj.lowVanish_obj | (intros; apply GlobalTheory.LowVanishObj.lowVanish_obj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelSecond
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ArrowLiftAut

theorem isQuot_of_is {D : D7} {N : GlobalTheory.Grid.Node D} (m : N.MeasDat) (df : Prop)
    (K : Subgroup (GL (Fin N.V.rank) (Lev.EAf D))) (h : m.Is df K) :
    GlobalTheory.Mem.Th.IsQuot N.V m.ν m.fd := by
  by_cases hd : df
  · obtain ⟨⟨hH, -⟩, hF⟩ := h.1 hd
    exact And.intro hH hF
  · obtain ⟨⟨hH, -⟩, hF⟩ := h.2 hd
    exact And.intro hH hF

theorem isQuot_cast {D : D7} {S S' : GlobalTheory.Grid.Node D} (e : S = S') (m : S.MeasDat)
    (h : GlobalTheory.Mem.Th.IsQuot S.V m.ν m.fd) :
    GlobalTheory.Mem.Th.IsQuot S'.V (m.cast e).ν (m.cast e).fd := by
  subst e
  exact h

theorem lift_isAutFunSm (hCRD : GlobalTheory.Published.CuspRapidDecay) {D : D7} {θ : InfFam D} (hθ : IsInfFam θ)
    {ψ : AddChar (AF ↥D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {ω : GlobalTheory.Grid.WRep S T}
    (hω : IsWeilDatumO ψ (GlobalTheory.Grid.sgn true S) T χS χT (GlobalTheory.Grid.WRep.toSgn true ω))
    {ν : Measure (GA D T)} {𝓕 : Set (GA D T)} (hq : GlobalTheory.Mem.Th.IsQuot T ν 𝓕)
    {Φ : WO (GlobalTheory.Grid.sgn true S) T → ℂ} (hΦ : IsThetaFunO ψ (GlobalTheory.Grid.sgn true S) T Φ)
    {φ : GA D T → ℂ} (hφ : IsAutFunSm θ T φ) (hφc : IsCuspFun T φ) :
    IsAutFunSm θ S (fun h => ∫ g in 𝓕, thetaKO ω h g Φ * φ g ∂ν) := by
  have hW := GlobalTheory.Ker.isWeak_of_datum hω
  have hK := (GlobalTheory.Mem.Lift.isKerSys_thKer hθ hω.std hW hω.om_cont).swap
  have hL := (GlobalTheory.Mem.Lift.IsKerSys.lift hCRD hθ hK hq ⟨hφ, hφc⟩ ⟨Φ, hΦ⟩).2
  exact ((GlobalTheory.sgn_fun_cusp D θ hθ true S (fun h => ∫ g in 𝓕, thetaKO ω h g Φ * φ g ∂ν)).1).1 hL

private theorem isQuot_Yc_nuY_fdY_of_base {D : D7} {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (hR : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R) (t : T) (k : ℕ) (hk : k < D.R.m) :
    GlobalTheory.Mem.Th.IsQuot (Yc D k) (R.νY t k) (R.fdY t k) := by
  rcases Nat.lt_or_ge (k + 1) D.R.m with h | h
  · obtain ⟨⟨hH, -⟩, hF⟩ := hR.measY t k h
    exact And.intro hH hF
  · obtain rfl : k = D.R.m - 1 := by omega
    obtain ⟨⟨hH, -⟩, hF⟩ := hR.measY' t
    exact And.intro hH hF

theorem isQuot_meas {D : D7} {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {R : RealDat D A Ks} (G : GlobalTheory.Grid.GridPre R) (hR : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R) (hG : G.Is)
    (t : T) (i j : ℕ) (hi : i < D.R.m) (hj : j ≤ D.R.m) :
    GlobalTheory.Mem.Th.IsQuot (G.V i j).V (G.meas t i j).ν (G.meas t i j).fd := by
  have hM := hG.meas
  rcases i with _ | i
  · rcases j with _ | j
    · exact isQuot_of_is _ _ _ (hM.col 0 (Nat.zero_le _))
    · dsimp only [GlobalTheory.Grid.GridPre.meas, GlobalTheory.Grid.meas0]
      split_ifs with h1
      · exact isQuot_cast _ _ (isQuot_Yc_nuY_fdY_of_base R hR t (j + 1) h1)
      · refine isQuot_cast _ _ ?_
        obtain ⟨⟨hH, -⟩, hF⟩ := hR.measX t
        exact And.intro hH hF
  · rcases j with _ | j
    · exact isQuot_of_is _ _ _ (hM.col (i + 1) hi.le)
    · exact isQuot_of_is _ _ _ (hM.vert i j hi.le hj)

end GlobalTheory.ArrowLiftAut

namespace GlobalTheory.ArrowLiftAut

end GlobalTheory.ArrowLiftAut
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselColumnScalarFunctionContinuousLeftInvarianStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselColumnScalarFunction_continuous_leftInvariant : Big fun ch => ∀ a, Continuous (colFn ch a) ∧
    ∀ γ ∈ GQ (ch.G.V (.top 0)), ∀ g, colFn ch a (γ * g) = colFn ch a g := by
  first | exact @GlobalTheory.RowClaim.colFn_cont_left | exact GlobalTheory.RowClaim.colFn_cont_left | (intros; apply GlobalTheory.RowClaim.colFn_cont_left <;> assumption)
end
