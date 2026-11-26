module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryJacquetEigenvectorExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoExpMulPoly
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitarySwapReduction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryInverseReduction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatakePowerNonvanishing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CtGrowth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriGlCasselmanDatum

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryFrobeniusReciprocity
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryFrobeniusReciprocity
noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.FrobRec

section Abstract

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def coeffMap (ρ : Representation ℂ G V) (lam : Module.Dual ℂ V) : V →ₗ[ℂ] (G → ℂ) where
  toFun v g := lam (ρ g v)
  map_add' v w := by
    funext g
    simp
  map_smul' c v := by
    funext g
    simp

theorem coeffMap_apply (ρ : Representation ℂ G V) (lam : Module.Dual ℂ V) (v : V) (g : G) :
    coeffMap ρ lam v g = lam (ρ g v) := rfl

theorem coeffMap_equivariant (ρ : Representation ℂ G V) (lam : Module.Dual ℂ V) (g : G) (v : V) :
    coeffMap ρ lam (ρ g v) = rightReg ℂ G ℂ g (coeffMap ρ lam v) := by
  funext x
  change lam (ρ x (ρ g v)) = lam (ρ (x * g) v)
  rw [map_mul, Module.End.mul_apply]

theorem coeffMap_injective {ρ : Representation ℂ G V} (hρ : ρ.IsIrreducible) {lam : Module.Dual ℂ V}
    (hlam : lam ≠ 0) : Function.Injective (coeffMap ρ lam) := by
  let S : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker (coeffMap ρ lam)
      apply_mem_toSubmodule := by
        intro g v hv
        rw [LinearMap.mem_ker] at hv ⊢
        rw [coeffMap_equivariant, hv, map_zero] }
  rcases hρ.eq_bot_or_eq_top S with h | h
  · have h1 : LinearMap.ker (coeffMap ρ lam) = ⊥ := congrArg Subrepresentation.toSubmodule h
    exact LinearMap.ker_eq_bot.1 h1
  · exfalso
    have h1 : LinearMap.ker (coeffMap ρ lam) = ⊤ := congrArg Subrepresentation.toSubmodule h
    refine hlam (LinearMap.ext fun v => ?_)
    have h2 : v ∈ LinearMap.ker (coeffMap ρ lam) := h1 ▸ Submodule.mem_top
    have h3 := congrFun (LinearMap.mem_ker.1 h2) 1
    simpa [coeffMap_apply] using h3

end Abstract

section U

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem chiDeltaU_mul_uni {m : ℕ} (q : ℕ) (α : Fin m → ℂ) {t u : GU σ n}
    (ht : IsDiagM (t : GL (Fin n) L)) (hu : IsUniM (u : GL (Fin n) L)) :
    chiDeltaU q α (t * u) = chiDeltaU q α t := by
  have h : ∀ i : Fin n, (((t * u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i =
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i := by
    intro i
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
    rw [Finset.sum_eq_single i]
    · rw [hu.2 i, mul_one]
    · intro j _ hj
      rw [ht i j (Ne.symm hj), zero_mul]
    · simp
  unfold chiDeltaU
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [h]
  · rfl

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem form_uni {ρ : Representation ℂ (GU σ n) V} {lam : Module.Dual ℂ V}
    (hJ : ∀ x ∈ jacU ρ, lam x = 0) {u : GU σ n} (hu : IsUniM (u : GL (Fin n) L)) (w : V) :
    lam (ρ u w) = lam w := by
  have h : ρ u w - w ∈ jacU ρ := Submodule.subset_span ⟨u, hu, w, rfl⟩
  have h0 := hJ _ h
  rwa [map_sub, sub_eq_zero] at h0

theorem coeffMap_mem (hsplit : BorelSplitU) (hσ : ∀ x, σ (σ x) = x) {q : ℕ} {β : Fin (n / 2) → ℂˣ}
    {ρ : Representation ℂ (GU σ n) V} {lam : Module.Dual ℂ V} (hJ : ∀ x ∈ jacU ρ, lam x = 0)
    (hT : ∀ t : GU σ n, IsDiagM (t : GL (Fin n) L) → ∀ v,
      lam (ρ t v) = chiDeltaU q (fun i => (β i : ℂ)) t * lam v) (v : V) :
    coeffMap ρ lam v ∈ psSpaceU σ q β := by
  intro b g hb
  obtain ⟨t, u, ht, hu, rfl⟩ := hsplit L σ n hσ b hb
  rw [chiDeltaU_mul_uni q _ ht hu, coeffMap_apply, coeffMap_apply, map_mul, map_mul,
    Module.End.mul_apply, Module.End.mul_apply, hT t ht, form_uni hJ hu]

end U

theorem frobU_of_split (hsplit : BorelSplitU) : FrobU := by
  intro L _ _ _ ϖ σ q n V _ _ ρ α hU _ hIrr hSat β lam hJ hlam hT
  have hmem := coeffMap_mem hsplit hU.1 hJ hT
  have hinj := coeffMap_injective hIrr hlam
  have heq := coeffMap_equivariant ρ lam
  refine ⟨?_, (coeffMap ρ lam).codRestrict (psSpaceU σ q β) hmem, ?_, fun g v => ?_⟩
  · obtain ⟨v₀, hv₀⟩ := hSat.exists_vec
    have h0 : coeffMap ρ lam v₀ ≠ 0 := fun h => hv₀.1 (hinj (h.trans (map_zero _).symm))
    have hα : IsSatVecU ϖ q (rightReg ℂ _ ℂ) (coeffMap ρ lam v₀) α := hv₀.map hU _ heq h0
    have hsph : IsSphericalU q (fun i => (β i : ℂ)) (coeffMap ρ lam v₀) := by
      intro b g k hb hk
      have h1 : coeffMap ρ lam v₀ (b * g * k) = coeffMap ρ lam v₀ (b * g) := by
        rw [coeffMap_apply, coeffMap_apply, map_mul (ρ) (b * g) k, Module.End.mul_apply,
          GlobalTheory.LGrp.mem_fixed.1 hv₀.2.1 k hk]
      rw [h1]
      exact hmem v₀ b g hb
    exact hα.unique hU (isSatVecU_of_isSphericalU hU hsph h0)
  · intro a b hab
    exact hinj (congrArg Subtype.val hab)
  · exact Subtype.ext (heq g v)

theorem frobU : FrobU := frobU_of_split GlobalTheory.T.unitary_borel_splitting

end GlobalTheory.CompanionTheory.FrobRec

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryFrobeniusReciprocityStatement
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_frobenius_reciprocity : PositivityTheory.SphericalProduct.FrobU := by
  first | exact @GlobalTheory.CompanionTheory.FrobRec.frobU | exact GlobalTheory.CompanionTheory.FrobRec.frobU | (intros; apply GlobalTheory.CompanionTheory.FrobRec.frobU <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryJacquetNonzero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormHeckeVecDosetInd
noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.SphComp

theorem form_heckeVec_dosetInd {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {K : Subgroup G}
    (hK : IsCommensurated K) (ρ : Representation ℂ G V) {x : V} (hx : x ∈ fixed ρ K)
    (l : Module.Dual ℂ V) (hl : ∀ k ∈ K, l ∘ₗ ρ k = l) (g : G) :
    l (heckeVec ρ K (dosetInd ℂ K g) x) =
      (Nat.card {c : G ⧸ K // (c.out : G) ∈ DoubleCoset.doubleCoset g (K : Set G) K} : ℂ) * l (ρ g x) := by
  classical
  set D := DoubleCoset.doubleCoset g (K : Set G) K with hD
  have hm := Formalism.UG.Final.DosetIndMem G K ℂ g
  have hfin : {c : G ⧸ K | c.out ∈ D}.Finite := by
    refine (Formalism.UG.P.finite_support_cosets hK hm.2).subset ?_
    intro c hc
    have h' : c.out ∈ D := hc
    simp only [Set.mem_setOf_eq, dosetInd]
    rw [Set.indicator_of_mem h']
    simp
  have hterm : ∀ γ ∈ D, l (ρ γ x) = l (ρ g x) := by
    intro γ hγ
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hγ
    have e := LinearMap.congr_fun (hl a ha) (ρ g (ρ b x))
    simp only [LinearMap.comp_apply] at e
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e, GlobalTheory.LGrp.mem_fixed.1 hx _ hb]
  have e1 : l (heckeVec ρ K (dosetInd ℂ K g) x) =
      ∑ᶠ c : G ⧸ K, l (dosetInd ℂ K g c.out • ρ c.out x) :=
    l.toAddMonoidHom.map_finsum (finite_heckeVec hK hm ρ x)
  have e2 : (fun c : G ⧸ K => l (dosetInd ℂ K g c.out • ρ c.out x)) =
      Set.indicator {c : G ⧸ K | c.out ∈ D} (fun _ => l (ρ g x)) := by
    funext c
    by_cases h : c.out ∈ D
    · have h1 : dosetInd ℂ K g c.out = 1 := by
        simp only [dosetInd]
        rw [Set.indicator_of_mem h]
        simp
      rw [Set.indicator_of_mem (show c ∈ {c : G ⧸ K | c.out ∈ D} from h), h1, one_smul, hterm _ h]
    · have h1 : dosetInd ℂ K g c.out = 0 := by
        simp only [dosetInd]
        exact Set.indicator_of_notMem h _
      rw [Set.indicator_of_notMem (show c ∉ {c : G ⧸ K | c.out ∈ D} from h), h1, zero_smul, map_zero]
  have hc : Nat.card {c : G ⧸ K // c.out ∈ D} = hfin.toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact Nat.card_coe_set_eq {c : G ⧸ K | c.out ∈ D}
  rw [e1, e2, ← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hfin, hc]
  simp

theorem sphCompare : PositivityTheory.SphericalProduct.SphCompare := by
  intro L _ _ ϖ σ q n hU V _ _ ρ α v₀ hv l hl g
  have hK := Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU n
  have e := congrArg l (hv.2.2 _ (Formalism.UG.Final.DosetIndMem _ (KU σ n) ℂ g))
  rw [map_smul, smul_eq_mul, form_heckeVec_dosetInd hK ρ hv.2.1 l hl g] at e
  exact e

end GlobalTheory.CompanionTheory.SphComp

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabFiniteIndexOfSmooth
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.KAvg

open GlobalTheory.OrbitAvg

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem stab_finiteIndex_of_smooth [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G)
    (hc : IsCompact (K : Set G)) (ρ : Representation ℂ G V) (hs : IsSmooth ρ) (x : V) :
    (stab ρ K x).FiniteIndex := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hc
  have ho : IsOpen (stab ρ K x : Set K) :=
    (hs x).preimage continuous_subtype_val
  haveI : Finite (K ⧸ stab ρ K x) := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.finiteIndex_of_finite_quotient

private theorem normalCore_stab_le_stab_apply (ρ : Representation ℂ G V) (K : Subgroup G) (x : V) (k : K) :
    (stab ρ K x).normalCore ≤ stab ρ K (ρ (k : G) x) := by
  intro n hn
  have hc : k⁻¹ * n * k ∈ stab ρ K x := by
    have h1 := (Subgroup.normalCore_normal (stab ρ K x)).conj_mem n hn k⁻¹
    rw [inv_inv] at h1
    exact Subgroup.normalCore_le _ h1
  rw [mem_stab] at hc ⊢
  have he : (n : G) * (k : G) = (k : G) * ((k⁻¹ * n * k : K) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  calc ρ (n : G) (ρ (k : G) x) = ρ ((n : G) * (k : G)) x := by
        rw [map_mul, Module.End.mul_apply]
    _ = ρ (k : G) (ρ ((k⁻¹ * n * k : K) : G) x) := by
        rw [he, map_mul, Module.End.mul_apply]
    _ = ρ (k : G) x := by rw [hc]

theorem avg_translate (ρ : Representation ℂ G V) (K : Subgroup G) {x : V}
    (hx : (stab ρ K x).FiniteIndex) (k : K) : avg ρ K (ρ (k : G) x) = avg ρ K x := by
  haveI := hx
  have hN1 : (stab ρ K x).normalCore ≤ stab ρ K x := Subgroup.normalCore_le _
  have hN2 : (stab ρ K x).normalCore ≤ stab ρ K (ρ (k : G) x) := normalCore_stab_le_stab_apply ρ K x k
  rw [avg_eq ρ K hN2, avg_eq ρ K hN1]
  unfold avgH
  congr 1
  have key : ∀ q : K ⧸ (stab ρ K x).normalCore,
      cv ρ K (stab ρ K x).normalCore (ρ (k : G) x) q =
        cv ρ K (stab ρ K x).normalCore x (q * (QuotientGroup.mk k)) := by
    intro q
    have hq : q * (QuotientGroup.mk k : K ⧸ (stab ρ K x).normalCore) = QuotientGroup.mk (q.out * k) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [hq, cv_mk ρ K hN1]
    simp only [cv, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  simp_rw [key]
  exact finsum_comp_equiv (Equiv.mulRight (QuotientGroup.mk k : K ⧸ (stab ρ K x).normalCore))

end GlobalTheory.CompanionTheory.KAvg


open GlobalTheory.OrbitAvg GlobalTheory.CompanionTheory.KAvg in
theorem GlobalTheory.CompanionTheory.KAvg.kInvForm : PositivityTheory.SphericalProduct.KInvForm := by
  unfold PositivityTheory.SphericalProduct.KInvForm
  intro G _ _ _ K _ hc V _ _ ρ hs v₀ hv₀ hne
  have hfi : ∀ x : V, (stab ρ K x).FiniteIndex := fun x => stab_finiteIndex_of_smooth K hc ρ hs x
  let A : V →ₗ[ℂ] V :=
    { toFun := fun x => avg ρ K x
      map_add' := fun x y => avg_add ρ K (hfi x) (hfi y)
      map_smul' := fun c x => avg_smul ρ K (hfi x) c }
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ V, f v₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne ((Module.forall_dual_apply_eq_zero_iff ℂ v₀).mp h)
  have hfix : ∀ l ∈ K, ρ l v₀ = v₀ := by
    intro l hl
    have h' : ∀ h : K, ρ h v₀ = ((1 : K →* ℂˣ) h : ℂ) • v₀ := hv₀
    simpa using h' ⟨l, hl⟩
  refine ⟨((f v₀)⁻¹ • f) ∘ₗ A, ?_, ?_⟩
  · intro k hk
    ext v
    show ((f v₀)⁻¹ • f) (avg ρ K (ρ k v)) = ((f v₀)⁻¹ • f) (avg ρ K v)
    rw [avg_translate ρ K (hfi v) ⟨k, hk⟩]
  · show ((f v₀)⁻¹ • f) (avg ρ K v₀) = 1
    rw [avg_fixed ρ K (hfi v₀) hfix, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryJacquetNonzero
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.JacSph

theorem hecke_pow {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : CassData G) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (hπ : IsSmooth π) (t : D.T) (ht : D.IsDom t)
    (U : Module.End ℂ (fixed π D.J)) (hU : PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U) (r : ℕ) :
    D.IsDom (t ^ r) ∧ PositivityTheory.Lbc.IsHeckeOpG π D.J ((t ^ r : D.T) : G) (U ^ r) := by
  induction r with
  | zero =>
    refine ⟨by simpa using (GlobalTheory.CompanionTheory.Cass.isDom_monoid G D).1, ?_⟩
    intro w l _
    simp
  | succ r ih =>
    rw [pow_succ, pow_succ U]
    exact ⟨(GlobalTheory.CompanionTheory.Cass.isDom_monoid G D).2 _ _ ih.1 ht,
      GlobalTheory.T.casselman_first_property G D V π hπ (t ^ r) t ih.1 ht _ _ ih.2 hU⟩

theorem jacNeU : JacNeU := by
  intro L _ _ _ ϖ σ q n V _ _ ρ α hu hadm _ hsat
  obtain ⟨v₀, hv₀⟩ := hsat.exists_vec
  have hfixK : v₀ ∈ fixed ρ (KU σ n) := hv₀.2.1
  refine ⟨v₀, fun hjac => ?_, fun k hk _ => ?_⟩
  · obtain ⟨D, hJ, hN, hNm, hT⟩ := GlobalTheory.T.iwahori_unipotent_datum L ϖ σ q hu n
    obtain ⟨hKo, hKc, hIK, t₀, ht₀d, ht₀s⟩ := GlobalTheory.CompanionTheory.KUFactsU.kuFacts L ϖ σ q n hu
    have hstr : D.IsStrDom ⟨t₀, (hT _).2 ht₀d⟩ :=
      (GlobalTheory.T.dominant_unipotent_contraction L ϖ σ q hu n D hJ hN hNm hT ⟨t₀, (hT _).2 ht₀d⟩).2 ht₀s
    have hker : twKer ρ D.N 1 = jacU ρ := twKer_eq_jacSub D _ hN ρ
    have hproj0 : D.proj ρ v₀ = 0 := by
      refine (Submodule.Quotient.mk_eq_zero _).2 ?_
      rw [hker]
      exact hjac
    have hJK : ∀ x ∈ D.J, x ∈ KU σ n := fun x hx => hIK (hJ ▸ hx)
    have hfixJ : v₀ ∈ fixed ρ D.J :=
      GlobalTheory.LGrp.mem_fixed.2 fun x hx => GlobalTheory.LGrp.mem_fixed.1 hfixK x (hJK x hx)
    obtain ⟨U, hU, -⟩ := GlobalTheory.T.hecke_character_exists_unique (GU σ n) D.J D.isOpen_J D.isCompact_J V ρ hadm.1 t₀
    obtain ⟨j₀, hj₀⟩ := GlobalTheory.CompanionTheory.Cass.hecke_pow_kills_of_proj_eq_zero (GU σ n) D V ρ hadm.1 _ hstr U hU
      ⟨v₀, hfixJ⟩ hproj0
    obtain ⟨l, hlK, hl1⟩ := GlobalTheory.CompanionTheory.KAvg.kInvForm (GU σ n) (KU σ n) hKo hKc V ρ hadm.1 v₀ hfixK hv₀.1
    obtain ⟨j, hj, hS⟩ := GlobalTheory.T.satake_power_nonvanishing L ϖ σ q n hu α t₀ ht₀d ht₀s j₀
    have hUj : (U ^ j) ⟨v₀, hfixJ⟩ = 0 := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
      rw [add_comm, pow_add, Module.End.mul_apply, hj₀, map_zero]
    have hl0 : l (ρ (t₀ ^ j) v₀) = 0 := by
      have h := (hecke_pow D ρ hadm.1 _ hstr.1 U hU j).2 ⟨v₀, hfixJ⟩ l fun x hx => hlK x (hJK x hx)
      rw [hUj] at h
      simpa using h
    have hc := GlobalTheory.CompanionTheory.SphComp.sphCompare L ϖ σ q n hu V ρ α v₀ hv₀ l hlK (t₀ ^ j)
    rw [hl0, mul_zero, hl1, mul_one] at hc
    exact hS hc.symm
  · rw [GlobalTheory.LGrp.mem_fixed.1 hfixK k hk, sub_self]
    exact Submodule.zero_mem _

end GlobalTheory.CompanionTheory.JacSph
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryJacquetNonzeroStatement
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_jacquet_nonzero : PositivityTheory.SphericalProduct.JacNeU := by
  first | exact @GlobalTheory.CompanionTheory.JacSph.jacNeU | exact GlobalTheory.CompanionTheory.JacSph.jacNeU | (intros; apply GlobalTheory.CompanionTheory.JacSph.jacNeU <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryCharacterFacts
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryCharacterFacts
noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.TorusChar

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem exists_diag {n : ℕ} {g : GL (Fin n) L} (h : IsDiagM g) :
    (g : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => (g : Matrix (Fin n) (Fin n) L) i i) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · rw [Matrix.diagonal_apply_ne _ hij]; exact h i j hij

theorem diag_ne_zero {n : ℕ} {g : GL (Fin n) L} (h : IsDiagM g) (i : Fin n) :
    (g : Matrix (Fin n) (Fin n) L) i i ≠ 0 := by
  intro h0
  have h1 : ((g * g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1 := by simp
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_zero] at h1
  · exact zero_ne_one h1
  · intro j _
    by_cases hij : i = j
    · subst hij; rw [h0, zero_mul]
    · rw [h i j hij, zero_mul]

theorem inv_val {n : ℕ} {g : GL (Fin n) L} (h : IsDiagM g) :
    ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (fun i => ((g : Matrix (Fin n) (Fin n) L) i i)⁻¹) := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [exists_diag h, Matrix.diagonal_mul_diagonal]
  simp only [Matrix.diagonal_apply_eq]
  rw [← Matrix.diagonal_one]
  congr 1
  ext i
  exact mul_inv_cancel₀ (diag_ne_zero h i)

theorem isDiag_inv {n : ℕ} {g : GL (Fin n) L} (h : IsDiagM g) : IsDiagM g⁻¹ := by
  intro i j hij
  rw [inv_val h, Matrix.diagonal_apply_ne _ hij]

theorem isDiag_mul {n : ℕ} {g k : GL (Fin n) L} (h : IsDiagM g) (h' : IsDiagM k) : IsDiagM (g * k) := by
  intro i j hij
  rw [Units.val_mul, exists_diag h, exists_diag h', Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_apply_ne _ hij]

theorem isUni_conj {n : ℕ} {s u : GL (Fin n) L} (hs : IsDiagM s) (hu : IsUniM u) : IsUniM (s * u * s⁻¹) := by
  have key : ∀ i j : Fin n, ((s * u * s⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      (s : Matrix (Fin n) (Fin n) L) i i * (u : Matrix (Fin n) (Fin n) L) i j *
        ((s : Matrix (Fin n) (Fin n) L) j j)⁻¹ := by
    intro i j
    rw [Units.val_mul, Units.val_mul, inv_val hs, Matrix.mul_diagonal]
    congr 1
    conv_lhs => rw [exists_diag hs]
    rw [Matrix.diagonal_mul]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [key, hu.1 i j hij]; simp
  · rw [key, hu.2 i, mul_one]; exact mul_inv_cancel₀ (diag_ne_zero hs i)

variable {σ : L →+* L} {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem map_jac (ρ : Representation ℂ (GU σ n) V) {s : GU σ n} (hs : IsDiagM (s : GL (Fin n) L))
    {x : V} (hx : x ∈ jacU ρ) : ρ s x ∈ jacU ρ := by
  have hle : jacU ρ ≤ (jacU ρ).comap (ρ s) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, hu, v, rfl⟩
    refine Submodule.subset_span ⟨s * u * s⁻¹, ?_, ρ s v, ?_⟩
    · have := isUni_conj hs hu
      simpa using this
    · have e : ρ (s * u * s⁻¹) (ρ s v) = ρ s (ρ u v) := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply]
      rw [map_sub, e]
  exact hle hx

theorem xi_mul {ρ : Representation ℂ (GU σ n) V} {ξ : GU σ n → ℂ} {y : V} (hy : y ∉ jacU ρ)
    (he : ∀ t : GU σ n, IsDiagM (t : GL (Fin n) L) → ρ t y - ξ t • y ∈ jacU ρ)
    {s t : GU σ n} (hs : IsDiagM (s : GL (Fin n) L)) (ht : IsDiagM (t : GL (Fin n) L)) :
    ξ (s * t) = ξ s * ξ t := by
  have h1 := he (s * t) (by simpa using isDiag_mul hs ht)
  have h2 := map_jac ρ hs (he t ht)
  have h3 := (jacU ρ).smul_mem (ξ t) (he s hs)
  have h4 := (jacU ρ).sub_mem ((jacU ρ).sub_mem h1 h2) h3
  have h5 : (ρ (s * t) y - ξ (s * t) • y) - ρ s (ρ t y - ξ t • y) - ξ t • (ρ s y - ξ s • y) =
      (ξ s * ξ t - ξ (s * t)) • y := by
    simp only [map_sub, map_smul, map_mul, Module.End.mul_apply, smul_sub, sub_smul, mul_smul]
    rw [smul_comm (ξ t) (ξ s) y]
    abel
  rw [h5] at h4
  by_contra hne
  exact hy (((jacU ρ).smul_mem_iff (sub_ne_zero.2 (Ne.symm hne))).1 h4)

theorem cT_diag (σ : L →+* L) (d : Fin n → L) :
    Formalism.UG.cT σ (Matrix.diagonal d) = Matrix.diagonal (fun i => σ (d i)) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Formalism.UG.cT]
  · simp [Formalism.UG.cT, Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij)]

theorem diag_rel {t : GU σ n} (ht : IsDiagM (t : GL (Fin n) L)) {i j : Fin n}
    (hij : i.val + j.val + 1 = n) :
    σ (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) *
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j j = 1 := by
  have h : Formalism.UG.cT σ ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * antiJ L n *
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = antiJ L n := t.2
  have h' := congrFun (congrFun h i) j
  rw [exists_diag ht, cT_diag, Matrix.mul_diagonal, Matrix.diagonal_mul] at h'
  simpa [antiJ, hij] using h'

def mkDiag (σ : L →+* L) (n : ℕ) (d : Fin n → L) (hd : ∀ i, d i ≠ 0)
    (hJ : ∀ i j : Fin n, i.val + j.val + 1 = n → σ (d i) * d j = 1) : GU σ n :=
  ⟨⟨Matrix.diagonal d, Matrix.diagonal (fun i => (d i)⁻¹),
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i; exact mul_inv_cancel₀ (hd i),
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i; exact inv_mul_cancel₀ (hd i)⟩,
    by
      change Formalism.UG.cT σ (Matrix.diagonal d) * antiJ L n * Matrix.diagonal d = antiJ L n
      rw [cT_diag]
      ext i j
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      by_cases hij : i.val + j.val + 1 = n
      · simpa [antiJ, hij] using hJ i j hij
      · simp [antiJ, hij]⟩

def ext0 {m : ℕ} (a : Fin m → ℤ) (i : ℕ) : ℤ := if h : i < m then a ⟨i, h⟩ else 0

def eps (n : ℕ) (a : Fin (n / 2) → ℤ) (i : Fin n) : ℤ := ext0 a i.val - ext0 a (n - 1 - i.val)

theorem matrixExtendByZero_add {m : ℕ} (a b : Fin m → ℤ) (i : ℕ) : ext0 (a + b) i = ext0 a i + ext0 b i := by
  unfold ext0; split_ifs <;> simp

theorem eps_add (a b : Fin (n / 2) → ℤ) (i : Fin n) : eps n (a + b) i = eps n a i + eps n b i := by
  unfold eps; rw [matrixExtendByZero_add, matrixExtendByZero_add]; ring

theorem eps_zero (i : Fin n) : eps n 0 i = 0 := by
  simp [eps, ext0]

theorem eps_anti (a : Fin (n / 2) → ℤ) {i j : Fin n} (hij : i.val + j.val + 1 = n) :
    eps n a j = - eps n a i := by
  have h1 : n - 1 - i.val = j.val := by omega
  have h2 : n - 1 - j.val = i.val := by omega
  unfold eps; rw [h1, h2]; ring

def tU {ϖ : L} (h0 : ϖ ≠ 0) (hσ : σ ϖ = ϖ) (n : ℕ) (a : Fin (n / 2) → ℤ) : GU σ n :=
  mkDiag σ n (fun i => ϖ ^ eps n a i) (fun i => zpow_ne_zero _ h0) (by
    intro i j hij
    simp only [map_zpow₀, hσ]
    rw [eps_anti a hij, zpow_neg]
    exact mul_inv_cancel₀ (zpow_ne_zero _ h0))

theorem tU_val {ϖ : L} (h0 : ϖ ≠ 0) (hσ : σ ϖ = ϖ) (a : Fin (n / 2) → ℤ) :
    (((tU h0 hσ n a : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (fun i => ϖ ^ eps n a i) := rfl

theorem isDiag_tU {ϖ : L} (h0 : ϖ ≠ 0) (hσ : σ ϖ = ϖ) (a : Fin (n / 2) → ℤ) :
    IsDiagM ((tU h0 hσ n a : GU σ n) : GL (Fin n) L) := by
  intro i j hij
  rw [tU_val, Matrix.diagonal_apply_ne _ hij]

theorem tU_add {ϖ : L} (h0 : ϖ ≠ 0) (hσ : σ ϖ = ϖ) (a b : Fin (n / 2) → ℤ) :
    (tU h0 hσ n (a + b) : GU σ n) = tU h0 hσ n a * tU h0 hσ n b := by
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_mul, Units.val_mul, tU_val, tU_val, tU_val, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  rw [eps_add, zpow_add₀ h0]

theorem tU_zero {ϖ : L} (h0 : ϖ ≠ 0) (hσ : σ ϖ = ϖ) : (tU h0 hσ n 0 : GU σ n) = 1 := by
  refine Subtype.ext (Units.ext ?_)
  rw [tU_val]
  simp [eps_zero]

theorem mem_KU {k : GU σ n} (hk : IsDiagM (k : GL (Fin n) L))
    (hv : ∀ i, Valued.v (((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) = 1) : k ∈ KU σ n := by
  have hmem : ∀ x : L, Valued.v x = 1 → x ∈ intL L := fun x h => (Valuation.mem_integer_iff _ _).2 h.le
  have hinv : ∀ i, Valued.v ((((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)⁻¹) = 1 := by
    intro i; rw [map_inv₀, hv, inv_one]
  unfold KU
  rw [Subgroup.mem_subgroupOf]
  refine ⟨k.2, ⟨Matrix.diagonal (fun i => ⟨_, hmem _ (hv i)⟩), Matrix.diagonal (fun i => ⟨_, hmem _ (hinv i)⟩), ?_, ?_⟩, ?_⟩
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext i
    exact mul_inv_cancel₀ (diag_ne_zero hk i)
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext i
    exact inv_mul_cancel₀ (diag_ne_zero hk i)
  · apply Units.ext
    change (Matrix.diagonal _).map _ = _
    conv_rhs => rw [exists_diag hk]
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.diagonal_apply_ne _ hij]

theorem v_eq_zpow {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {x : L} (hx : x ≠ 0) : Valued.v x = (Valued.v ϖ) ^ (ordL x) := by
  have h : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  unfold ordL
  rw [dite_eq_right h, hϖ]
  conv_lhs => rw [← WithZero.coe_unzero h]
  rw [← WithZero.coe_zpow]
  congr 1
  apply Multiplicative.toAdd.injective
  simp

theorem sq_one {x : WithZero (Multiplicative ℤ)} (h : x * x = 1) : x = 1 := by
  have hne : x ≠ 0 := by rintro rfl; simp at h
  obtain ⟨w, rfl⟩ := WithZero.ne_zero_iff_exists.1 hne
  have h1 : w * w = 1 := by exact_mod_cast h
  have h2 := congrArg Multiplicative.toAdd h1
  have h3 : w = 1 := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_one] at h2 ⊢
    omega
  rw [h3]; rfl

def ordVec (t : GU σ n) : Fin (n / 2) → ℤ := fun i =>
  ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
    ⟨i.val, lt_of_lt_of_le i.2 (Nat.div_le_self n 2)⟩ ⟨i.val, lt_of_lt_of_le i.2 (Nat.div_le_self n 2)⟩)

theorem v_entry {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {t : GU σ n} (ht : IsDiagM (t : GL (Fin n) L)) (i : Fin n) :
    Valued.v (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) = (Valued.v ϖ) ^ eps n (ordVec t) i := by
  have hi := i.2
  let j : Fin n := ⟨n - 1 - i.val, by omega⟩
  have hj : j.val = n - 1 - i.val := rfl
  have hij : i.val + j.val + 1 = n := by omega
  have hv : Valued.v (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) *
      Valued.v (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j j) = 1 := by
    rw [← hσv (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i), ← map_mul, diag_rel ht hij, map_one]
  unfold eps
  by_cases h1 : i.val < n / 2
  · have e1 : ext0 (ordVec t) i.val = ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) := by
      unfold ext0; rw [dite_eq_left h1]; rfl
    have e2 : ext0 (ordVec t) (n - 1 - i.val) = 0 := by
      unfold ext0; rw [dite_eq_right (by omega)]
    rw [e1, e2, sub_zero]
    exact v_eq_zpow hϖ (diag_ne_zero ht i)
  · have e1 : ext0 (ordVec t) i.val = 0 := by
      unfold ext0; rw [dite_eq_right h1]
    by_cases h2 : j.val < n / 2
    · have e2 : ext0 (ordVec t) (n - 1 - i.val) =
          ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j j) := by
        unfold ext0; rw [dite_eq_left (by omega)]; rfl
      rw [e1, e2, zero_sub, zpow_neg, ← v_eq_zpow hϖ (diag_ne_zero ht j)]
      exact eq_inv_of_mul_eq_one_left hv
    · have hji : j = i := Fin.ext (by omega)
      have e2 : ext0 (ordVec t) (n - 1 - i.val) = 0 := by
        unfold ext0; rw [dite_eq_right (by omega)]
      rw [e1, e2, sub_zero, zpow_zero]
      rw [hji] at hv
      exact sq_one hv

theorem exists_decomp {ϖ : L} (h0 : ϖ ≠ 0) (hσ : σ ϖ = ϖ)
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {t : GU σ n} (ht : IsDiagM (t : GL (Fin n) L)) :
    ∃ k ∈ KU σ n, IsDiagM (k : GL (Fin n) L) ∧ t = tU h0 hσ n (ordVec t) * k := by
  have hT := isDiag_tU (σ := σ) h0 hσ (ordVec t)
  have hk : IsDiagM (((tU h0 hσ n (ordVec t))⁻¹ * t : GU σ n) : GL (Fin n) L) := by
    simpa using isDiag_mul (isDiag_inv hT) ht
  refine ⟨(tU h0 hσ n (ordVec t))⁻¹ * t, mem_KU hk ?_, hk, by simp⟩
  intro i
  have he : ((((tU h0 hσ n (ordVec t))⁻¹ * t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i =
      (ϖ ^ eps n (ordVec t) i)⁻¹ * ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, inv_val hT, tU_val, Matrix.diagonal_mul]
    simp
  rw [he, map_mul, map_inv₀, map_zpow₀, v_entry hϖ hσv ht i]
  exact inv_mul_cancel₀ (zpow_ne_zero _ (by
    rw [hϖ]; exact WithZero.coe_ne_zero))

theorem hom_prod {m : ℕ} (Φ : (Fin m → ℤ) → ℂˣ) (h : ∀ a b, Φ (a + b) = Φ a * Φ b) (a : Fin m → ℤ) :
    Φ a = ∏ i, Φ (Pi.single i 1) ^ a i := by
  let f : (Fin m → ℤ) →+ Additive ℂˣ := AddMonoidHom.mk' (fun a => Additive.ofMul (Φ a))
    (fun a b => by rw [h]; rfl)
  have ha : a = ∑ i, a i • (Pi.single i (1 : ℤ) : Fin m → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h2 : f a = ∑ i, a i • f (Pi.single i 1) := by
    conv_lhs => rw [ha]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_zsmul f _ _
  have h3 := congrArg Additive.toMul h2
  simpa [f, toMul_sum] using h3

theorem charU : PositivityTheory.SphericalProduct.CharU := by
  intro L _ _ _ ϖ σ q n V _ _ ρ hU ξ y hy he hk
  obtain ⟨-, hσv, hσϖ, hϖ, -, hq, -⟩ := hU
  have h0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ
    exact WithZero.coe_ne_zero hϖ.symm
  have hT : ∀ a, IsDiagM ((tU h0 hσϖ n a : GU σ n) : GL (Fin n) L) := isDiag_tU h0 hσϖ
  have hone : ξ 1 = 1 := hk 1 (one_mem _) (by
    intro i j hij
    simp [Matrix.one_apply_ne hij])
  have hmul : ∀ a b, ξ (tU h0 hσϖ n (a + b)) = ξ (tU h0 hσϖ n a) * ξ (tU h0 hσϖ n b) := by
    intro a b
    rw [tU_add]
    exact xi_mul hy he (hT a) (hT b)
  let Φ : (Fin (n / 2) → ℤ) → ℂˣ := fun a => ⟨ξ (tU h0 hσϖ n a), ξ (tU h0 hσϖ n (-a)),
    by rw [← hmul, add_neg_cancel, tU_zero, hone], by rw [← hmul, neg_add_cancel, tU_zero, hone]⟩
  have hΦ : ∀ a b, Φ (a + b) = Φ a * Φ b := fun a b => Units.ext (hmul a b)
  have hq0 : (q : ℂ) ≠ 0 := by
    have : q ≠ 0 := by omega
    exact_mod_cast this
  refine ⟨fun i => Φ (Pi.single i 1) * Units.mk0 (q : ℂ) hq0 ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ)), fun t ht => ?_⟩
  obtain ⟨k, hkK, hkd, hdec⟩ := exists_decomp h0 hσϖ hϖ hσv ht
  have h1 : ξ t = ((Φ (ordVec t) : ℂˣ) : ℂ) := by
    conv_lhs => rw [hdec]
    rw [xi_mul hy he (hT _) hkd, hk k hkK hkd, mul_one]
  rw [h1, hom_prod Φ hΦ, Units.coe_prod]
  unfold chiDeltaU
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi : i.val < n := lt_of_lt_of_le i.2 (Nat.div_le_self n 2)
  rw [dite_eq_left hi]
  change _ = _ ^ (ordVec t i) * _ ^ (-(ordVec t i) * _)
  simp only [Units.val_zpow_eq_zpow_val, Units.val_mul, Units.val_mk0]
  rw [mul_zpow, mul_assoc, ← zpow_mul, ← zpow_add₀ hq0]
  have : ((n : ℤ) - 1 - 2 * (i.val : ℤ)) * ordVec t i + -(ordVec t i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)) = 0 := by ring
  rw [this, zpow_zero, mul_one]

end GlobalTheory.CompanionTheory.TorusChar

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryCharacterFactsStatement
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_character_facts : PositivityTheory.SphericalProduct.CharU := by
  first | exact @GlobalTheory.CompanionTheory.TorusChar.charU | exact GlobalTheory.CompanionTheory.TorusChar.charU | (intros; apply GlobalTheory.CompanionTheory.TorusChar.charU <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryChamberDecomposition
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryChamberDecomposition
noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.ChamberInd

variable {m : ℕ}

def nrm (χ : Fin m → ℂˣ) : Fin m → ℝ := fun i => ‖(χ i : ℂ)‖

def wt (a : Fin m → ℝ) : ℝ := ∑ i : Fin m, ((m : ℝ) - (i.val : ℝ)) * Real.log (a i)

theorem nrm_pos (χ : Fin m → ℂˣ) (i : Fin m) : 0 < nrm χ i := by
  exact norm_pos_iff.mpr (Units.ne_zero _)

theorem wt_swap_gt (a : Fin m → ℝ) (ha : ∀ i, 0 < a i) (i j : Fin m) (hij : i.val + 1 = j.val)
    (hlt : a i < a j) : wt a < wt (a ∘ Equiv.swap i j) := by
  have hne : i ≠ j := by
    intro h
    rw [h] at hij
    omega
  have hsub : wt (a ∘ Equiv.swap i j) - wt a =
      ((m : ℝ) - (i.val : ℝ)) * (Real.log (a j) - Real.log (a i)) +
        ((m : ℝ) - (j.val : ℝ)) * (Real.log (a i) - Real.log (a j)) := by
    unfold wt
    rw [← Finset.sum_sub_distrib, Fintype.sum_eq_add i j hne (fun k hk => by
      simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hk.1 hk.2, sub_self])]
    simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
    ring
  have hj : (j.val : ℝ) = (i.val : ℝ) + 1 := by
    rw [← hij]
    push_cast
    ring
  have hlog : Real.log (a i) < Real.log (a j) := Real.log_lt_log (ha i) hlt
  have hd : wt (a ∘ Equiv.swap i j) - wt a = Real.log (a j) - Real.log (a i) := by
    rw [hsub, hj]
    ring
  linarith

theorem wt_update_gt (χ : Fin m → ℂˣ) (j : Fin m) (hj : j.val + 1 = m) (hlt : ‖(χ j : ℂ)‖ < 1) :
    wt (nrm χ) < wt (nrm (Function.update χ j (χ j)⁻¹)) := by
  have hpos : 0 < ‖(χ j : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
  have hn : nrm (Function.update χ j (χ j)⁻¹) = Function.update (nrm χ) j (‖(χ j : ℂ)‖⁻¹) := by
    funext k
    by_cases hk : k = j
    · subst hk
      simp [nrm]
    · simp [nrm, Function.update_of_ne hk]
  rw [hn]
  have hdiff : wt (Function.update (nrm χ) j ‖(χ j : ℂ)‖⁻¹) - wt (nrm χ) =
      ((m : ℝ) - (j.val : ℝ)) * (Real.log ‖(χ j : ℂ)‖⁻¹ - Real.log (nrm χ j)) := by
    unfold wt
    rw [← Finset.sum_sub_distrib, Fintype.sum_eq_single j (fun k hk => by
      simp only [Function.update_of_ne hk, sub_self])]
    simp only [Function.update_self]
    ring
  have hm : (m : ℝ) - (j.val : ℝ) = 1 := by
    have hj' : (j.val : ℝ) + 1 = (m : ℝ) := by exact_mod_cast hj
    linarith
  have hlog : Real.log ‖(χ j : ℂ)‖ < 0 := Real.log_neg hpos hlt
  have e : nrm χ j = ‖(χ j : ℂ)‖ := rfl
  rw [Real.log_inv, hm, e] at hdiff
  linarith

theorem weylConj_swap {α χ : Fin m → ℂˣ} (h : GlobalTheory.LGrp.WeylConjU α χ) (i j : Fin m) :
    GlobalTheory.LGrp.WeylConjU α (χ ∘ Equiv.swap i j) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨(Equiv.swap i j).trans w, fun k => hw _⟩

theorem weylConj_update {α χ : Fin m → ℂˣ} (h : GlobalTheory.LGrp.WeylConjU α χ) (j : Fin m) :
    GlobalTheory.LGrp.WeylConjU α (Function.update χ j (χ j)⁻¹) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨w, fun k => ?_⟩
  by_cases hk : k = j
  · subst hk
    rw [Function.update_self]
    rcases hw k with h | h
    · right
      rw [h]
    · left
      rw [h, inv_inv]
  · rw [Function.update_of_ne hk]
    exact hw k

theorem finite_nrm (α : Fin m → ℂˣ) (T : Set (Fin m → ℂˣ)) (hT : ∀ β ∈ T, GlobalTheory.LGrp.WeylConjU α β) :
    (nrm '' T).Finite := by
  classical
  let S : Set ℝ := (Set.range fun k => ‖(α k : ℂ)‖) ∪ Set.range fun k => ‖(((α k)⁻¹ : ℂˣ) : ℂ)‖
  have hS : S.Finite := (Set.finite_range _).union (Set.finite_range _)
  refine (Set.Finite.pi (t := fun _ : Fin m => S) (fun _ => hS)).subset ?_
  rintro _ ⟨β, hβ, rfl⟩
  rw [Set.mem_univ_pi]
  intro i
  obtain ⟨w, hw⟩ := hT β hβ
  rcases hw i with h | h
  · exact Or.inl ⟨w i, by simp only [nrm, h]⟩
  · exact Or.inr ⟨w i, by simp only [nrm, h]⟩

theorem exists_chamber (P : (Fin m → ℂˣ) → Prop)
    (hs : ∀ (χ : Fin m → ℂˣ) (i j : Fin m), i.val + 1 = j.val → ‖(χ i : ℂ)‖ < ‖(χ j : ℂ)‖ → P χ →
      P (χ ∘ Equiv.swap i j))
    (hv : ∀ (χ : Fin m → ℂˣ) (j : Fin m), j.val + 1 = m → ‖(χ j : ℂ)‖ < 1 → P χ →
      P (Function.update χ j (χ j)⁻¹))
    (α χ : Fin m → ℂˣ) (hα : GlobalTheory.LGrp.WeylConjU α χ) (hχ : P χ) :
    ∃ β : Fin m → ℂˣ, GlobalTheory.LGrp.WeylConjU α β ∧ (∀ i j : Fin m, i ≤ j → ‖(β j : ℂ)‖ ≤ ‖(β i : ℂ)‖) ∧
      (∀ i, 1 ≤ ‖(β i : ℂ)‖) ∧ P β := by
  classical
  obtain ⟨T, hTdef⟩ : ∃ T : Set (Fin m → ℂˣ), T = {β | GlobalTheory.LGrp.WeylConjU α β ∧ P β} := ⟨_, rfl⟩
  have hfin : (nrm '' T).Finite := finite_nrm α T (fun β hβ => by rw [hTdef] at hβ; exact hβ.1)
  have hne : (nrm '' T).Nonempty := ⟨nrm χ, χ, by rw [hTdef]; exact ⟨hα, hχ⟩, rfl⟩
  obtain ⟨_, ⟨β, hβT, rfl⟩, hmax⟩ := Set.exists_max_image (nrm '' T) wt hfin hne
  rw [hTdef] at hβT
  obtain ⟨hβα, hβP⟩ := hβT
  have hmax' : ∀ γ : Fin m → ℂˣ, GlobalTheory.LGrp.WeylConjU α γ → P γ → wt (nrm γ) ≤ wt (nrm β) :=
    fun γ h1 h2 => hmax _ ⟨γ, by rw [hTdef]; exact ⟨h1, h2⟩, rfl⟩
  have hadj : ∀ i j : Fin m, i.val + 1 = j.val → ‖(β j : ℂ)‖ ≤ ‖(β i : ℂ)‖ := by
    intro i j hij
    by_contra hcon
    rw [not_le] at hcon
    have h1 := hmax' _ (weylConj_swap hβα i j) (hs β i j hij hcon hβP)
    have h2 := wt_swap_gt (nrm β) (nrm_pos β) i j hij hcon
    exact absurd h1 (not_le.mpr h2)
  have key : ∀ d : ℕ, ∀ i j : Fin m, j.val = i.val + d → ‖(β j : ℂ)‖ ≤ ‖(β i : ℂ)‖ := by
    intro d
    induction d with
    | zero =>
      intro i j h
      rw [show j = i from Fin.ext (by omega)]
    | succ d ih =>
      intro i j h
      have hk : i.val + d < m := by
        have := j.isLt
        omega
      exact le_trans (hadj ⟨i.val + d, hk⟩ j (by show i.val + d + 1 = j.val; omega))
        (ih i ⟨i.val + d, hk⟩ rfl)
  have hmono : ∀ i j : Fin m, i ≤ j → ‖(β j : ℂ)‖ ≤ ‖(β i : ℂ)‖ := by
    intro i j hij
    have h' : i.val ≤ j.val := hij
    exact key (j.val - i.val) i j (by omega)
  have hone : ∀ i, 1 ≤ ‖(β i : ℂ)‖ := by
    intro i
    have hi := i.isLt
    have hlast : (⟨m - 1, by omega⟩ : Fin m).val + 1 = m := by
      show m - 1 + 1 = m
      omega
    have hl : 1 ≤ ‖(β ⟨m - 1, by omega⟩ : ℂ)‖ := by
      by_contra hcon
      rw [not_le] at hcon
      have h1 := hmax' _ (weylConj_update hβα _) (hv β _ hlast hcon hβP)
      have h2 := wt_update_gt β _ hlast hcon
      exact absurd h1 (not_le.mpr h2)
    exact le_trans hl (hmono i _ (by show i.val ≤ m - 1; omega))
  exact ⟨β, hβα, hmono, hone, hβP⟩

theorem chamberU : PositivityTheory.SphericalProduct.ChamberU := by
  unfold ChamberU
  intro hsw hinv
  unfold SwapStepU at hsw
  unfold InvStepU at hinv
  intro L _ _ _ ϖ σ q n hU V _ _ ρ hadm hirr hsph α χ hα f hf hfeq
  obtain ⟨β, h1, h2, h3, hP⟩ := exists_chamber (m := n / 2)
    (fun χ => ∃ f : V →ₗ[ℂ] ↥(GlobalTheory.LFun.psSpaceU σ q χ), Function.Injective f ∧
      ∀ (g : ↥(Formalism.UG.GU σ n)) (v : V), f (ρ g v) = (GlobalTheory.LFun.psFunU σ q χ g) (f v))
    (fun χ i j hij hlt hP => by
      obtain ⟨f, hf, hfeq⟩ := hP
      exact hsw L ϖ σ q n hU V ρ hadm hirr hsph χ i j hij
        (by rw [norm_div, div_lt_one (norm_pos_iff.mpr (Units.ne_zero _))]; exact hlt) f hf hfeq)
    (fun χ j hj hlt hP => by
      obtain ⟨f, hf, hfeq⟩ := hP
      exact hinv L ϖ σ q n hU V ρ hadm hirr hsph χ j hj hlt f hf hfeq)
    α χ hα ⟨f, hf, hfeq⟩
  exact ⟨β, h1, h2, h3, hP⟩

end GlobalTheory.CompanionTheory.ChamberInd

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryChamberDecompositionStatement
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_chamber_decomposition : PositivityTheory.SphericalProduct.ChamberU := by
  first | exact @GlobalTheory.CompanionTheory.ChamberInd.chamberU | exact GlobalTheory.CompanionTheory.ChamberInd.chamberU | (intros; apply GlobalTheory.CompanionTheory.ChamberInd.chamberU <;> assumption)
end
end

noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun

namespace PositivityTheory.SphericalProduct

theorem extremeU : ExtremeU := by
  intro L _ _ _ ϖ σ q n V _ _ ρ α hU hA hI hS
  obtain ⟨y, hy, hy1⟩ := GlobalTheory.T.unitary_jacquet_nonzero L ϖ σ q n V ρ α hU hA hI hS
  obtain ⟨y', ξ, hy', heig, h1⟩ := GlobalTheory.T.unitary_jacquet_eigenvector_exists L ϖ σ q n V ρ hU hA y hy hy1
  obtain ⟨lam, hlam0, hne, hlam⟩ := GlobalTheory.T.unitary_equivariant_form L ϖ σ q n V ρ hU hA ξ y' hy' heig h1
  obtain ⟨β, hβ⟩ := GlobalTheory.T.unitary_character_facts L ϖ σ q n V ρ hU ξ y' hy' heig h1
  obtain ⟨hW, f, hf, hfe⟩ := GlobalTheory.T.unitary_frobenius_reciprocity L ϖ σ q n V ρ α hU hA hI hS β lam hlam0 hne
    (fun t ht v => by rw [← hβ t ht]; exact hlam t ht v)
  exact GlobalTheory.T.unitary_chamber_decomposition GlobalTheory.T.unitary_swap_reduction GlobalTheory.T.unitary_inverse_reduction L ϖ σ q n hU V ρ hA hI hS.1 α β hW f hf hfe

end PositivityTheory.SphericalProduct

end
