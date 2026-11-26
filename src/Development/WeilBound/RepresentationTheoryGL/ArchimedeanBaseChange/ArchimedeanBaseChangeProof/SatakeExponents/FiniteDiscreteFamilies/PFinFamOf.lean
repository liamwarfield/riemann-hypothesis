module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.FinCut
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalFactorOfSphericalSubquotient

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.PFinFamOf
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShapeMemBounded
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.One PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.F.F5

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.FinFamAssembly

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def Cov (S : Set (Pre E n)) : Prop :=
  ∃ (k : ℕ) (D : Fin k → Pre E n), ∀ D' ∈ S, ∃ j, PreEquiv (D j) D'

theorem cov_of_rel {S : Set (Pre E n)} {ι : Type*} [Finite ι] (P : ι → Pre E n → Prop)
    (h1 : ∀ D ∈ S, ∃ a, P a D)
    (h2 : ∀ a, ∀ D₁ ∈ S, ∀ D₂ ∈ S, P a D₁ → P a D₂ → PreEquiv D₁ D₂) : Cov S := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨D₀, -⟩ := hS
    let e := Finite.equivFin ι
    refine ⟨Nat.card ι, fun j => if h : ∃ D ∈ S, P (e.symm j) D then h.choose else D₀, ?_⟩
    intro D' hD'
    obtain ⟨a, ha⟩ := h1 D' hD'
    have hex : ∃ D ∈ S, P (e.symm (e a)) D := ⟨D', hD', by rw [Equiv.symm_apply_apply]; exact ha⟩
    refine ⟨e a, ?_⟩
    show PreEquiv (if h : ∃ D ∈ S, P (e.symm (e a)) D then h.choose else D₀) D'
    rw [dite_eq_left hex]
    obtain ⟨hmem, hP⟩ := hex.choose_spec
    exact h2 _ _ hmem _ hD' hP (by rw [Equiv.symm_apply_apply]; exact ha)
  · exact ⟨0, Fin.elim0, fun D' hD' => (hS ⟨D', hD'⟩).elim⟩

theorem cov_of_cover {S : Set (Pre E n)} {ι : Type*} [Finite ι] (A : ι → Set (Pre E n))
    (hA : ∀ a, Cov (A a)) (hS : ∀ D ∈ S, ∃ a, D ∈ A a) : Cov S := by
  classical
  choose k D hD using fun a => (hA a : ∃ (k : ℕ) (D : Fin k → Pre E n), ∀ D' ∈ A a, ∃ j, PreEquiv (D j) D')
  let e := Finite.equivFin (Σ a, Fin (k a))
  refine ⟨Nat.card (Σ a, Fin (k a)), fun j => D (e.symm j).1 (e.symm j).2, ?_⟩
  intro D' hD'
  obtain ⟨a, ha⟩ := hS D' hD'
  obtain ⟨j, hj⟩ := hD a D' ha
  refine ⟨e ⟨a, j⟩, ?_⟩
  show PreEquiv (D (e.symm (e ⟨a, j⟩)).1 (e.symm (e ⟨a, j⟩)).2) D'
  rw [Equiv.symm_apply_apply]
  exact hj

abbrev Shape (E : Type) [Field E] : Type :=
  Σ c : ℕ, (Fin c → ℕ) × (Fin c → (E →+* ℂ) → Multiset ℂ)

def shape (D : Pre E n) : Shape E := ⟨D.c, D.N, D.m⟩

def bounded (E : Type) [Field E] (n : ℕ) (m : (E →+* ℂ) → Multiset ℂ) : Set (Shape E) :=
  {t | t.1 ≤ n ∧ (∀ i, t.2.1 i ≤ n) ∧ ∀ i τ, t.2.2 i τ ≤ m τ}

theorem finite_le (s : Multiset ℂ) : {x : Multiset ℂ | x ≤ s}.Finite := by
  exact (Multiset.finite_toSet s.powerset).subset fun x hx => Multiset.mem_powerset.mpr hx

theorem bounded_finite (n : ℕ) (m : (E →+* ℂ) → Multiset ℂ) : (bounded E n m).Finite := by
  refine ((Set.finite_Iic n).biUnion fun c _ =>
    (((Set.Finite.pi fun _ : Fin c => Set.finite_Iic n).prod
      (Set.Finite.pi fun _ : Fin c => Set.Finite.pi fun τ => finite_le (m τ))).image
        (fun p => (⟨c, p⟩ : Shape E)))).subset ?_
  rintro ⟨c, N, mm⟩ ⟨hc, hN, hm⟩
  exact Set.mem_iUnion₂.mpr ⟨c, hc, ⟨(N, mm), ⟨fun i _ => hN i, fun i _ τ _ => hm i τ⟩, rfl⟩⟩

theorem shape_mem_bounded (m : (E →+* ℂ) → Multiset ℂ) (D : Pre E n)
    (hm : ∀ τ, ∑ i, D.m i τ = m τ) : shape D ∈ bounded E n m := by
  refine ⟨?_, fun i => ?_, fun i τ => ?_⟩
  · show D.c ≤ n
    calc D.c = ∑ _i : Fin D.c, 1 := by simp
      _ ≤ ∑ i, D.N i := Finset.sum_le_sum fun i _ => D.pos i
      _ = n := D.h
  · show D.N i ≤ n
    exact (Finset.single_le_sum (f := D.N) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)).trans D.h.le
  · show D.m i τ ≤ m τ
    rw [← hm τ]
    exact Finset.single_le_sum (f := fun j => D.m j τ) (fun j _ => Multiset.zero_le _) (Finset.mem_univ i)

theorem cov_fibre (hL : LevelFactor) (hF : FinDiscN)
    (K : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin n) (w.adicCompletion E)))
    (W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)) (hK : IsLevel K) (hW : ∀ N, FiniteDimensional ℂ (W N))
    (t : Shape E) :
    Cov {D' : Pre E n | shape D' = t ∧
      (∀ w, GlobalTheory.LGrp.IsSpherical (locProd D'.h w (D'.σ · w)) (K w)) ∧
      ∀ i, HasKType (W (D'.N i)) (D'.V i)} := by
  classical
  obtain ⟨c, N, mm⟩ := t
  by_cases hsum : ∑ i, N i = n
  swap
  · refine ⟨0, Fin.elim0, ?_⟩
    rintro ⟨c', N', h', V', σ', m', pos', disc', loc', inf'⟩ ⟨hsh, -, -⟩
    obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp hsh
    obtain ⟨rfl, -⟩ := Prod.mk.inj (eq_of_heq hh)
    exact absurd h' hsum
  choose Ki hKiopen hKiKGL hKisph using fun w => hL E w c n N hsum (K w) (hK.1 w)
  have hlev : ∀ i : Fin c, IsLevel (fun w => Ki w i) := fun i =>
    ⟨fun w => hKiopen w i, hK.2.mono fun w hw => hKiKGL w hw i⟩
  choose k σs hσs using fun i : Fin c =>
    hF E (N i) (fun w => Ki w i) (W (N i)) (mm i) (hlev i) (hW (N i))
  refine cov_of_rel (ι := (i : Fin c) → Fin (k i))
    (fun a D => ∃ hc : D.c = c, ∀ (i : Fin D.c) w, ∃ hs hi,
      D.cls i w = GlobalTheory.LocGL.IrrGL.of (σs (Fin.cast hc i) (a (Fin.cast hc i)) w).ρ hs hi) ?_ ?_
  · rintro ⟨c', N', h', V', σ', m', pos', disc', loc', inf'⟩ ⟨hsh, hsph, hKt⟩
    obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp hsh
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq hh)
    choose a ha using fun i => hσs i (V' i) (fun w => σ' i w) (disc' i) (fun w => loc' i w)
      (fun τ => inf' i τ) (fun w => hKisph w (fun j => σ' j w) (hsph w) i) (hKt i)
    exact ⟨a, rfl, fun i w => ⟨_, _, (ha i w).symm⟩⟩
  · rintro a ⟨c₁, N₁, h₁, V₁, σ₁, m₁, pos₁, disc₁, loc₁, inf₁⟩ ⟨hsh₁, -, -⟩
      ⟨c₂, N₂, h₂, V₂, σ₂, m₂, pos₂, disc₂, loc₂, inf₂⟩ ⟨hsh₂, -, -⟩ ⟨hc₁, hP₁⟩ ⟨hc₂, hP₂⟩
    obtain ⟨rfl, hh₁⟩ := Sigma.mk.inj_iff.mp hsh₁
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq hh₁)
    obtain ⟨rfl, hh₂⟩ := Sigma.mk.inj_iff.mp hsh₂
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq hh₂)
    refine ⟨finCongr rfl, fun i w => ?_, fun i τ => rfl⟩
    obtain ⟨hs₁, hi₁, e₁⟩ := hP₁ i w
    obtain ⟨hs₂, hi₂, e₂⟩ := hP₂ i w
    exact e₁.trans e₂.symm

theorem finFamOf : FinFamOf := by
  intro hL hF E _ _ _ n K W m hK hW
  have hS : Cov {D' : Pre E n | (∀ τ, ∑ i, D'.m i τ = m τ) ∧
      (∀ w, GlobalTheory.LGrp.IsSpherical (locProd D'.h w (D'.σ · w)) (K w)) ∧
      ∀ i, HasKType (W (D'.N i)) (D'.V i)} := by
    have hfin := bounded_finite (E := E) n m
    haveI := hfin.to_subtype
    refine cov_of_cover (ι := bounded E n m) (fun t => {D' : Pre E n | shape D' = t.1 ∧
      (∀ w, GlobalTheory.LGrp.IsSpherical (locProd D'.h w (D'.σ · w)) (K w)) ∧
      ∀ i, HasKType (W (D'.N i)) (D'.V i)}) (fun t => cov_fibre hL hF K W hK hW t.1) ?_
    rintro D' ⟨hm, hsph, hKt⟩
    exact ⟨⟨shape D', shape_mem_bounded m D' hm⟩, rfl, hsph, hKt⟩
  obtain ⟨k, D, hD⟩ := hS
  exact ⟨k, D, fun D' hm hsph hKt => hD D' ⟨hm, hsph, hKt⟩⟩

end GlobalTheory.CompanionTheory.FinFamAssembly

end
end

namespace PositivityTheory.Rg.BcB.F.F5

theorem finFamOf_holds : FinFamOf := GlobalTheory.CompanionTheory.FinFamAssembly.finFamOf

end PositivityTheory.Rg.BcB.F.F5
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.PLevelFactorB
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SmGL.DepthZero GlobalTheory.LocLanglands.SphFac

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.F5

namespace LevelFixedParabolic

section Gen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
  {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]

theorem fixed_ne_bot_mono {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {H K : Subgroup G} (hle : H ≤ K) (h : fixed ρ K ≠ ⊥) : fixed ρ H ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  exact (Submodule.ne_bot_iff _).2 ⟨v, fun g => hv ⟨g.1, hle g.2⟩, hv0⟩


variable (k n) in
def coreH (K : Subgroup (GL n k)) : Subgroup (GL n k) :=
  ((K.subgroupOf (KO k n)).normalCore).map (KO k n).subtype

theorem coreH_le (K : Subgroup (GL n k)) : coreH k n K ≤ K := by
  rintro _ ⟨y, hy, rfl⟩
  exact Subgroup.mem_subgroupOf.1 (Subgroup.normalCore_le _ hy)

theorem conj_mem_coreH (K : Subgroup (GL n k)) {c : GL n k} (hc : c ∈ KO k n) {x : GL n k}
    (hx : x ∈ coreH k n K) : c⁻¹ * x * c ∈ coreH k n K := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨(⟨c, hc⟩ : KO k n)⁻¹ * y * (⟨c, hc⟩ : KO k n)⁻¹⁻¹,
    (Subgroup.normalCore_normal _).conj_mem y hy _, ?_⟩
  simp

theorem KO_le_coreH {K : Subgroup (GL n k)} (hK : KO k n ≤ K) : KO k n ≤ coreH k n K := by
  intro x hx
  have htop : K.subgroupOf (KO k n) = ⊤ := Subgroup.subgroupOf_eq_top.2 hK
  have hc : (⊤ : Subgroup (KO k n)) ≤ (K.subgroupOf (KO k n)).normalCore :=
    Subgroup.normal_le_normalCore.2 (by rw [htop])
  exact Subgroup.mem_map.2 ⟨⟨x, hx⟩, hc (Subgroup.mem_top _), rfl⟩

theorem isOpen_coreH {K : Subgroup (GL n k)} (hK : IsOpen (K : Set (GL n k))) :
    IsOpen (coreH k n K : Set (GL n k)) := by
  haveI : CompactSpace (KO k n) := isCompact_iff_compactSpace.1 GlobalTheory.SplitFlip.isCompact_KO
  have hU : IsOpen ((K.subgroupOf (KO k n) : Subgroup (KO k n)) : Set (KO k n)) :=
    hK.preimage continuous_subtype_val
  haveI : Finite (KO k n ⧸ K.subgroupOf (KO k n)) := Subgroup.quotient_finite_of_isOpen _ hU
  haveI : (K.subgroupOf (KO k n)).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hC : IsClosed (((K.subgroupOf (KO k n)).normalCore : Subgroup (KO k n)) : Set (KO k n)) :=
    Subgroup.normalCore_isClosed _ (Subgroup.isClosed_of_isOpen _ hU)
  have hO := Subgroup.isOpen_of_isClosed_of_finiteIndex _ hC
  obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.1 hO
  convert ht.inter GlobalTheory.SplitFlip.isOpen_KO using 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyt : y ∈ Subtype.val ⁻¹' t := by rw [hts]; exact hy
    exact ⟨hyt, y.2⟩
  · rintro ⟨hxt, hxK⟩
    refine ⟨⟨x, hxK⟩, ?_, rfl⟩
    have : (⟨x, hxK⟩ : KO k n) ∈ Subtype.val ⁻¹' t := hxt
    rw [hts] at this
    exact this


variable (k) in
def Ki (e : (Σ a, m a) ≃ n) (H : Subgroup (GL n k)) (a : α) : Subgroup (GL (m a) k) :=
  H.comap ((leviEmb k e).comp (MonoidHom.mulSingle (fun b => GL (m b) k) a)) ⊓ KO k (m a)

theorem isOpen_Ki (e : (Σ a, m a) ≃ n) {H : Subgroup (GL n k)} (hH : IsOpen (H : Set (GL n k))) (a : α) :
    IsOpen (Ki k e H a : Set (GL (m a) k)) := by
  have hc : Continuous ((leviEmb k e).comp (MonoidHom.mulSingle (fun b => GL (m b) k) a)) :=
    (continuous_leviEmb k e).comp (continuous_mulSingle (A := fun b => GL (m b) k) a)
  exact (hH.preimage hc).inter GlobalTheory.SplitFlip.isOpen_KO

theorem KO_le_Ki (e : (Σ a, m a) ≃ n) {H : Subgroup (GL n k)} (hH : KO k n ≤ H) (a : α) :
    KO k (m a) ≤ Ki k e H a := by
  intro x hx
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_comap.2 (hH (leviEmb_mem_KO' (g := Pi.mulSingle a x) e fun b => ?_)), hx⟩
  by_cases hb : b = a
  · subst hb; simpa using hx
  · rw [Pi.mulSingle_eq_of_ne hb]; exact one_mem _

theorem exists_fixed_of_parInd_H (e : (Σ a, m a) ≃ n) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k m) W) (H : Subgroup (GL n k))
    (hH : ∀ c ∈ KO k n, ∀ x ∈ H, c⁻¹ * x * c ∈ H)
    {f : IndSp e ρ} (hf : f ∈ fixed (parInd e ρ) H) (h0 : f ≠ 0) :
    ∃ w : W, w ≠ 0 ∧ ∀ g : Levi k m, (∀ a, g a ∈ KO k (m a)) → leviEmb k e g ∈ H → ρ g w = w := by
  obtain ⟨x, hx⟩ : ∃ x, f.1.1 x ≠ 0 := by
    by_contra! h
    exact h0 (Subtype.ext (Subtype.ext (funext h)))
  obtain ⟨p, c, hc, rfl⟩ := MultiIrr.exists_parab_mul e x
  refine ⟨f.1.1 c, fun h => hx (by rw [parInd_law, h]; simp), fun g hg hgH => ?_⟩
  have hmem : leviEmb k e g ∈ parab k e := by
    refine mem_parab_iff.2 fun a b i j hab => ?_
    simp [leviEmb, Matrix.blockDiagonal'_apply, hab.ne']
  have hproj : leviProj k e ⟨leviEmb k e g, hmem⟩ = g := by
    funext a
    ext i j
    simp [leviEmb]
  have h1 := parInd_law e ρ f ⟨_, hmem⟩ c
  rw [hproj, deltaHalf_eq_one_of_KO hg, Units.val_one, one_smul] at h1
  have h2 := hf ⟨c⁻¹ * leviEmb k e g * c, hH c hc _ hgH⟩
  have h3 := congrArg (fun F : IndSp e ρ => F.1.1 c) h2
  simp only [parInd_apply, MonoidHom.one_apply, Units.val_one, one_smul] at h3
  rw [← h1, ← h3]
  group

theorem exists_fixed_factor (e : (Σ a, m a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) (H : Subgroup (GL n k))
    (hH : ∀ c ∈ KO k n, ∀ x ∈ H, c⁻¹ * x * c ∈ H)
    (hv : fixed (multiProd e σ) H ≠ ⊥) (a : α) : fixed (σ a) (Ki k e H a) ≠ ⊥ := by
  obtain ⟨f, hf, hf0⟩ := (Submodule.ne_bot_iff _).1 hv
  obtain ⟨w, hw0, hw⟩ := exists_fixed_of_parInd_H e (piTensor σ) H hH hf hf0
  obtain ⟨φ, hφ⟩ := exists_contract_ne_zero hw0 a
  refine (Submodule.ne_bot_iff _).2 ⟨_, fun g => ?_, hφ⟩
  have hg := Subgroup.mem_inf.1 g.2
  rw [← contract_piTensor, hw (Pi.mulSingle a g) (fun b => ?_) (Subgroup.mem_comap.1 hg.1)]
  · simp
  · by_cases hb : b = a
    · subst hb; simpa using hg.2
    · rw [Pi.mulSingle_eq_of_ne hb]; exact one_mem _

end Gen

end LevelFixedParabolic

open LevelFixedParabolic in
theorem levelFactor : LevelFactor := by
  intro E _ _ _ w c n N h K hK
  have hKO : ∀ m, GlobalTheory.LFun.KGL w (n := m) = KO (w.adicCompletion E) (Fin m) := fun m =>
    (GlobalTheory.SmGL.SphCompletion.KO_completion w m).symm
  refine ⟨Ki (m := fun i => Fin (N i)) (w.adicCompletion E) (stdBlocks N h) (coreH (w.adicCompletion E) (Fin n) K),
    fun i => isOpen_Ki (stdBlocks N h) (isOpen_coreH hK) i, fun hle i => ?_, fun σ hσ i => ?_⟩
  · rw [hKO n] at hle
    rw [hKO (N i)]
    exact KO_le_Ki (stdBlocks N h) (KO_le_coreH hle) i
  · exact exists_fixed_factor (stdBlocks N h) (fun i => (σ i).ρ) _ (fun c hc x hx => conj_mem_coreH K hc hx)
      (fixed_ne_bot_mono (coreH_le K) hσ) i

end PositivityTheory.Rg.BcB.F.F5

end
end
