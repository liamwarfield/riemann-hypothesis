module

public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EquivOfStalkwiseBaseChange
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsTateTwistSectionsEquivLocallyConstant
public import Development.AutomorphicArithmetic.CommutativeAlgebra.AcyclicSpecIntegralAlgebraStrictHenselian

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.RedShDefs
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.RedSh

def Conn {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') (F : Shv R) (m : ℤ) : Prop :=
  (∀ n, n < m → Function.Bijective (pull R f F n)) ∧ Function.Injective (pull R f F m)

end UpperTheory.RedSh
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.CechAugmentationEquivOfSection
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem UpperTheory.cechAugmentation_equiv_of_section :
    ∀ (R : Type) [CommRing R] {Y X : Scheme.{0}} (f : Y ⟶ X) (s : X ⟶ Y), s ≫ f = 𝟙 X → ∀ F : Shv R, Eqv R (cechAug f) F := by
  intro R _ Y X f s hs F
  apply (GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F).2.2.1
  apply GlobalTheory.T.quasiIso_chains_cechNerve_of_surjective R (yoneda.map f)
  intro U g
  refine ⟨g ≫ s, ?_⟩
  change (g ≫ s) ≫ f = g
  rw [Category.assoc, hs, Category.comp_id]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.SheafConnectedOfLevelwiseConnected
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.CochainPullbackBijectiveOfTermwiseBijectiveInjec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.TruncCx

open GlobalTheory.ColFilt

section Abstract

variable {A B : ℤ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)]

private def ConeAt (dA : ∀ n m, A n →+ A m) (dB : ∀ n m, B n →+ B m) (Φ : ∀ n, A n →+ B n)
    (n₂ : ℤ) : Prop :=
  ∀ n₀ n₁ n₃ : ℤ, n₀ + 1 = n₁ → n₁ + 1 = n₂ → n₂ + 1 = n₃ → ∀ (x : A n₂) (y : B n₁),
    dA n₂ n₃ x = 0 → Φ n₂ x = dB n₁ n₂ y →
      ∃ (v : A n₁) (w : B n₀), x = dA n₁ n₂ v ∧ y = Φ n₁ v + dB n₀ n₁ w

variable {GA GB : ℤ → ℤ → Type*} [∀ p n, AddCommGroup (GA p n)] [∀ p n, AddCommGroup (GB p n)]
  {dA : ∀ n m, A n →+ A m} {gA : ∀ p n m, GA p n →+ GA p m} {FA : ℤ → ∀ n, AddSubgroup (A n)}
  {rA : ∀ p n m, n + p = m → (A n →+ GA p m)}
  {dB : ∀ n m, B n →+ B m} {gB : ∀ p n m, GB p n →+ GB p m} {FB : ℤ → ∀ n, AddSubgroup (B n)}
  {rB : ∀ p n m, n + p = m → (B n →+ GB p m)}

private theorem coneAt_of_graded (hA : IsFilt dA gA FA rA) (hB : IsFilt dB gB FB rB)
    (Φ : ∀ n, A n →+ B n)
    (hd : ∀ n m, n + 1 = m → ∀ x, Φ m (dA n m x) = dB n m (Φ n x))
    (hF : ∀ p n, ∀ x ∈ FA p n, Φ n x ∈ FB p n) (Ψ : ∀ p m, GA p m →+ GB p m)
    (hΨ : ∀ p n m (h : n + p = m), ∀ x ∈ FA p n, Ψ p m (rA p n m h x) = rB p n m h (Φ n x))
    (M : ℤ) (hc : ∀ p ≤ 0, ∀ k ≤ M + p, ConeAt (gA p) (gB p) (Ψ p) k)
    (n₂ : ℤ) (hn : n₂ ≤ M) : ConeAt dA dB Φ n₂ := by
  intro n₀ n₁ n₃ h01 h12 h23
  obtain ⟨N1, hN1⟩ := hA.bot n₂
  obtain ⟨N2, hN2⟩ := hB.bot n₁
  have leInd (a : ℤ) (P : ℤ → Prop) (base : P a)
      (step : ∀ n, a ≤ n → P n → P (n + 1)) : ∀ n, a ≤ n → P n := by
    intro n
    induction n using Int.inductionOn' (b := a) with
    | zero => exact fun _ => base
    | succ n hn ih => exact fun _ => step n hn (ih hn)
    | pred n hn ih => intro h; omega
  have key : ∀ p, min (min N1 N2) 0 ≤ p → p ≤ 0 → ∀ (x : A n₂) (y : B n₁), x ∈ FA p n₂ →
      y ∈ FB p n₁ → dA n₂ n₃ x = 0 → Φ n₂ x = dB n₁ n₂ y →
      ∃ (v : A n₁) (w : B n₀), x = dA n₁ n₂ v ∧ y = Φ n₁ v + dB n₀ n₁ w := by
    intro p hNp
    refine leInd (min (min N1 N2) 0) (fun p => p ≤ 0 → ∀ (x : A n₂) (y : B n₁),
      x ∈ FA p n₂ → y ∈ FB p n₁ → dA n₂ n₃ x = 0 → Φ n₂ x = dB n₁ n₂ y →
      ∃ (v : A n₁) (w : B n₀), x = dA n₁ n₂ v ∧ y = Φ n₁ v + dB n₀ n₁ w) ?_ ?_ p hNp
    ·
      intro _ x y hxF hyF _ _
      have hx0 : x = 0 := hN1 x (hA.mono _ N1 n₂ (by omega) hxF)
      have hy0 : y = 0 := hN2 y (hB.mono _ N2 n₁ (by omega) hyF)
      exact ⟨0, 0, by simp [hx0], by simp [hy0]⟩
    · intro q hNq ih
      intro hq x y hxF hyF hx hxy
      have ih' := ih (by omega)
      have hpq : q + 1 - 1 = q := by ring
      obtain ⟨v₀, w₀, hv₀, hw₀⟩ := hc (q + 1) hq (n₂ + (q + 1)) (by omega)
        (n₀ + (q + 1)) (n₁ + (q + 1)) (n₃ + (q + 1)) (by omega) (by omega) (by omega)
        (rA (q + 1) n₂ _ rfl x) (rB (q + 1) n₁ _ rfl y)
        (by rw [← hA.rd (q + 1) n₂ n₃ _ _ rfl rfl h23 x hxF, hx, map_zero])
        (by rw [hΨ (q + 1) n₂ _ rfl x hxF, hxy, hB.rd (q + 1) n₁ n₂ _ _ rfl rfl h12 y hyF])
      obtain ⟨v, hvF, hv⟩ := hA.surj (q + 1) n₁ _ rfl v₀
      obtain ⟨w, hwF, hw⟩ := hB.surj (q + 1) n₀ _ rfl w₀
      have hx'F : x - dA n₁ n₂ v ∈ FA q n₂ := by
        have h := (hA.ker (q + 1) n₂ _ rfl (x - dA n₁ n₂ v)
          (sub_mem hxF (hA.dF (q + 1) n₁ n₂ h12 v hvF))).1
          (by rw [map_sub, hA.rd (q + 1) n₁ n₂ _ _ rfl rfl h12 v hvF, hv, hv₀, sub_self])
        rwa [hpq] at h
      have hy'F : y - Φ n₁ v - dB n₀ n₁ w ∈ FB q n₁ := by
        have h := (hB.ker (q + 1) n₁ _ rfl (y - Φ n₁ v - dB n₀ n₁ w)
          (sub_mem (sub_mem hyF (hF (q + 1) n₁ v hvF)) (hB.dF (q + 1) n₀ n₁ h01 w hwF))).1
          (by
            rw [map_sub, map_sub, ← hΨ (q + 1) n₁ _ rfl v hvF,
              hB.rd (q + 1) n₀ n₁ _ _ rfl rfl h01 w hwF, hv, hw, hw₀]
            abel)
        rwa [hpq] at h
      have hx'c : dA n₂ n₃ (x - dA n₁ n₂ v) = 0 := by
        rw [map_sub, hx, hA.dd, sub_self]
      have hx'r : Φ n₂ (x - dA n₁ n₂ v) = dB n₁ n₂ (y - Φ n₁ v - dB n₀ n₁ w) := by
        rw [map_sub, map_sub, map_sub, hd n₁ n₂ h12 v, hxy, hB.dd, sub_zero]
      obtain ⟨v', w', hv', hw'⟩ := ih' _ _ hx'F hy'F hx'c hx'r
      refine ⟨v + v', w + w', ?_, ?_⟩
      · rw [map_add (f := _), ← hv']
        abel
      · rw [map_add (f := _), map_add (f := _)]
        rw [sub_sub, sub_eq_iff_eq_add] at hw'
        rw [hw']
        abel
  intro x y hx hxy
  exact key 0 (by omega) le_rfl x y (hA.top n₂ x) (hB.top n₁ y) hx hxy

end Abstract

section Classes

variable {R : Type} [CommRing R]

private def pre {K L : Cx R} (g : K ⟶ L) (I : Cx R) (n : ℤ) : Cochain L I n →+ Cochain K I n :=
  AddMonoidHom.mk' (fun α => (Cochain.ofHom g).comp α (zero_add n))
    (fun _ _ => Cochain.comp_add _ _ _ _)

private theorem pre_v {K L : Cx R} (g : K ⟶ L) (I : Cx R) (n : ℤ) (α : Cochain L I n) (t q : ℤ)
    (hq : t + n = q) : (pre g I n α).v t q hq = g.f t ≫ α.v t q hq := by
  simp [pre, Cochain.comp_zero_cochain_v]

private theorem pre_δ {K L : Cx R} (g : K ⟶ L) (I : Cx R) (n m : ℤ) (h : n + 1 = m)
    (α : Cochain L I n) : pre g I m (δ n m α) = δ n m (pre g I n α) := by
  simp only [pre, AddMonoidHom.mk'_apply]
  rw [δ_ofHom_comp]

private theorem cpull_mk_eq_mk_of_pre {K L I : Cx R} (g : K ⟶ L) (n : ℤ) (x : Cocycle L I n)
    (z : Cocycle K I n) (hz : (z : Cochain K I n) = pre g I n x) :
    cpull g I n (CohomologyClass.mk x) = CohomologyClass.mk z := by
  simp only [cpull, cpre, CohomologyClass.descAddMonoidHom_cohomologyClass, AddMonoidHom.mk'_apply]
  congr 1
  exact Subtype.ext (by rw [hz]; rfl)

private theorem coneAt_of_conn {K L I : Cx R} (g : K ⟶ L) (M : ℤ)
    (hb : ∀ n, n < M → Function.Bijective (cpull g I n)) (hi : Function.Injective (cpull g I M))
    (k : ℤ) (hk : k ≤ M) : ConeAt (dC L I) (dC K I) (pre g I) k := by
  intro n₀ n₁ n₃ h01 h12 h23 x y hx hxy
  simp only [dC, AddMonoidHom.mk'_apply] at hx hxy ⊢
  have hk1 : n₁ < M := by omega
  have injk : Function.Injective (cpull g I k) := by
    rcases lt_or_eq_of_le hk with h | h
    · exact (hb k h).1
    · subst h
      exact hi
  have hpx : δ k n₃ (pre g I k x) = 0 := by rw [← pre_δ g I k n₃ h23, hx, map_zero]
  have e1 : cpull g I k (CohomologyClass.mk (Cocycle.mk x n₃ h23 hx)) = 0 := by
    rw [cpull_mk_eq_mk_of_pre g k _ (Cocycle.mk (pre g I k x) n₃ h23 hpx) rfl, ← CohomologyClass.mk_zero,
      mk_eq_mk_iff _ _ n₁ h12]
    exact ⟨y, by simp [hxy]⟩
  have e2 := injk (e1.trans (map_zero _).symm)
  rw [← CohomologyClass.mk_zero, mk_eq_mk_iff _ _ n₁ h12] at e2
  obtain ⟨v', hv'⟩ := e2
  simp only [Cocycle.mk_coe, Cocycle.coe_zero, sub_zero] at hv'
  have hyc : δ n₁ k (y - pre g I n₁ v') = 0 := by
    rw [δ_sub, ← pre_δ g I n₁ k h12, hv', hxy, sub_self]
  obtain ⟨c, hc⟩ := (hb n₁ hk1).2 (CohomologyClass.mk (Cocycle.mk _ k h12 hyc))
  obtain ⟨u, rfl⟩ := CohomologyClass.mk_surjective c
  have hpu : δ n₁ k (pre g I n₁ u) = 0 := by
    rw [← pre_δ g I n₁ k h12, Cocycle.δ_eq_zero, map_zero]
  rw [cpull_mk_eq_mk_of_pre g n₁ u (Cocycle.mk (pre g I n₁ u) k h12 hpu) rfl, mk_eq_mk_iff _ _ n₀ h01] at hc
  obtain ⟨w, hw⟩ := hc
  simp only [Cocycle.mk_coe] at hw
  refine ⟨v' + u, -w, ?_, ?_⟩
  · rw [δ_add, hv', Cocycle.δ_eq_zero, add_zero]
  · rw [map_add (f := _), δ_neg, hw]
    abel

private theorem conn_of_coneAt {K L I : Cx R} (g : K ⟶ L) (M : ℤ)
    (h : ∀ k ≤ M, ConeAt (dC L I) (dC K I) (pre g I) k) :
    (∀ n, n < M → Function.Bijective (cpull g I n)) ∧ Function.Injective (cpull g I M) := by
  have inj : ∀ n, n ≤ M → Function.Injective (cpull g I n) := by
    intro n hn
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective c
    have hpx : δ n (n + 1) (pre g I n x) = 0 := by
      rw [← pre_δ g I n (n + 1) rfl, Cocycle.δ_eq_zero, map_zero]
    rw [cpull_mk_eq_mk_of_pre g n x (Cocycle.mk _ (n + 1) rfl hpx) rfl, ← CohomologyClass.mk_zero,
      mk_eq_mk_iff _ _ (n - 1) (by ring)] at hc
    obtain ⟨y, hy⟩ := hc
    simp only [Cocycle.mk_coe, Cocycle.coe_zero, sub_zero] at hy
    obtain ⟨v, w, hv, -⟩ := h n hn (n - 1 - 1) (n - 1) (n + 1) (by ring) (by ring) rfl
      (x : Cochain L I n) y (Cocycle.δ_eq_zero x _) (by simp only [dC, AddMonoidHom.mk'_apply, hy])
    rw [← CohomologyClass.mk_zero, mk_eq_mk_iff _ _ (n - 1) (by ring)]
    simp only [dC, AddMonoidHom.mk'_apply] at hv
    exact ⟨v, by rw [← hv]; simp⟩
  refine ⟨fun n hn => ⟨inj n hn.le, ?_⟩, inj M le_rfl⟩
  intro c
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective c
  obtain ⟨v, w, hv, hw⟩ := h (n + 1) (by omega) (n - 1) n (n + 1 + 1) (by ring) rfl rfl 0
    (z : Cochain K I n) (map_zero _) (by simp [dC, Cocycle.δ_eq_zero])
  simp only [dC, AddMonoidHom.mk'_apply] at hv hw
  have hvδ : δ n (n + 1) v = 0 := hv.symm
  have hpv : δ n (n + 1) (pre g I n v) = 0 := by
    rw [← pre_δ g I n (n + 1) rfl, hvδ, map_zero]
  refine ⟨CohomologyClass.mk (Cocycle.mk v (n + 1) rfl hvδ), ?_⟩
  rw [cpull_mk_eq_mk_of_pre g n _ (Cocycle.mk (pre g I n v) (n + 1) rfl hpv) rfl,
    mk_eq_mk_iff _ _ (n - 1) (by ring)]
  refine ⟨-w, ?_⟩
  simp only [Cocycle.mk_coe, δ_neg, hw]
  abel

end Classes

end UpperTheory.TruncCx

private theorem ιTerm_comp_f_naturality {R : Type} [CommRing R] {K L : Cx R} (g : K ⟶ L) (c k t : ℤ)
    (h : c + k = t) :
    GlobalTheory.ColFilt.ιTerm K c k t h ≫ g.f t =
      ((CochainComplex.singleFunctor (Shv R) 0).map (g.f c)).f k ≫ GlobalTheory.ColFilt.ιTerm L c k t h := by
  by_cases hk : k = 0
  · subst hk
    have hct : t = c := by omega
    subst hct
    rw [GlobalTheory.ColFilt.ιTerm_zero, GlobalTheory.ColFilt.ιTerm_zero]
    simp [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      HomologicalComplex.single_map_f_self]
  · rw [GlobalTheory.ColFilt.ιTerm_ne K c k t h hk, GlobalTheory.ColFilt.ιTerm_ne L c k t h hk]
    simp

open GlobalTheory.ColFilt UpperTheory.TruncCx in
theorem UpperTheory.cochainPullback_bijective_of_termwise_bijective_injective :
    ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0], (∀ n, Injective (I.X n)) → ∀ {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L) (m : ℤ), (∀ p : ℤ, (∀ n, n < m + p → Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p)) I n)) ∧ Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p)) I (m + p))) → (∀ n, n < m → Function.Bijective (cpull g I n)) ∧ Function.Injective (cpull g I m) := by
  intro R _ I _ _ K L _ _ g m hyp
  apply UpperTheory.TruncCx.conn_of_coneAt g m
  intro k hk
  refine UpperTheory.TruncCx.coneAt_of_graded ((isColumns_terms L).isFilt I) ((isColumns_terms K).isFilt I)
    (UpperTheory.TruncCx.pre g I) (fun n m' h x => UpperTheory.TruncCx.pre_δ g I n m' h x) ?_
    (fun p => UpperTheory.TruncCx.pre ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p)) I) ?_ m
    (fun p _ k' hk' => UpperTheory.TruncCx.coneAt_of_conn _ (m + p) (hyp p).1 (hyp p).2 k' hk') k hk
  · intro p n x hx c k' t h q hq hpc
    have hx' : ∀ (c k t : ℤ) (h : c + k = t) (q : ℤ) (hq : t + n = q), p < c →
        ιTerm L c k t h ≫ x.v t q hq = 0 := hx
    rw [UpperTheory.TruncCx.pre_v, ← Category.assoc, ιTerm_comp_f_naturality, Category.assoc,
      hx' c k' t h q hq hpc, comp_zero]
  · intro p n m' h x _
    refine Cochain.ext _ _ (fun k' q hq => ?_)
    rw [UpperTheory.TruncCx.pre_v, restr_v _ _ p n m' h _ k' (p + k') q rfl hq (by omega),
      restr_v _ _ p n m' h _ k' (p + k') q rfl hq (by omega), UpperTheory.TruncCx.pre_v,
      ← Category.assoc, ← Category.assoc, ιTerm_comp_f_naturality]
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

section SlopeTestRemainingChoices
variable {R : Type} [CommRing R]

private theorem cpull_comp' {A B C : Cx R} (f : A ⟶ B) (g : B ⟶ C) (I : Cx R) (n : ℤ)
    (x : CohomologyClass C I n) : cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

private theorem cpull_id' {A : Cx R} (I : Cx R) (n : ℤ) (x : CohomologyClass A I n) :
    cpull (𝟙 A) I n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

private theorem cpull_homotopy {A B : Cx R} {f g : A ⟶ B} (h : Homotopy f g) (I : Cx R) (n : ℤ)
    (x : CohomologyClass B I n) : cpull f I n x = cpull g I n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨z, hz⟩ := Cochain.equivHomotopy f g h
  rw [cpre_mk, cpre_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨n.negOnePow • z.comp x.1 (by omega), ?_⟩
  rw [δ_units_smul, δ_comp z x.1 _ 0 (n + 1) n (by omega) (by omega) rfl]
  simp [zcomp, smul_smul, hz, Cochain.add_comp]

private theorem cpull_bij {A B : Cx R} (e : HomotopyEquiv A B) (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull e.hom I n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨cpull e.inv I n, fun x => ?_, fun x => ?_⟩
  · rw [← cpull_comp', cpull_homotopy e.homotopyInvHomId, cpull_id']
  · rw [← cpull_comp', cpull_homotopy e.homotopyHomInvId, cpull_id']

private theorem transfer {A B A' B' : Cx R} (g : A ⟶ B) (g' : A' ⟶ B') (a : HomotopyEquiv A A')
    (b : HomotopyEquiv B B') (w : g ≫ b.hom = a.hom ≫ g') (I : Cx R) (n : ℤ) :
    (Function.Bijective (cpull g' I n) → Function.Bijective (cpull g I n)) ∧
      (Function.Injective (cpull g' I n) → Function.Injective (cpull g I n)) := by
  have ha := cpull_bij a I n
  have hb := cpull_bij b I n
  have key : ⇑(cpull g I n) = cpull a.hom I n ∘ cpull g' I n ∘ (Equiv.ofBijective _ hb).symm := by
    funext x
    obtain ⟨y, rfl⟩ := hb.2 x
    have : (Equiv.ofBijective _ hb).symm (cpull b.hom I n y) = y :=
      (Equiv.ofBijective _ hb).symm_apply_apply y
    simp only [Function.comp_apply, this]
    rw [← cpull_comp', ← cpull_comp', w]
  rw [key]
  exact ⟨fun h => ha.comp (h.comp (Equiv.bijective _)),
    fun h => ha.1.comp (h.comp (Equiv.injective _))⟩

private theorem subsingleton_of_isZero {A : Cx R} (h : IsZero A) (I : Cx R) (n : ℤ) :
    Subsingleton (CohomologyClass A I n) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨y, rfl⟩ := y.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext (Cochain.ext _ _ fun p q hpq => ?_))
  exact ((HomologicalComplex.eval _ _ p).map_isZero h).eq_of_src _ _

private theorem bij_of_isZero {A B : Cx R} (hA : IsZero A) (hB : IsZero B) (g : A ⟶ B) (I : Cx R)
    (n : ℤ) : Function.Bijective (cpull g I n) := by
  have := subsingleton_of_isZero hA I n
  have := subsingleton_of_isZero hB I n
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

private theorem core (R : Type) [CommRing R] (F : Shv R) {E' E : Spc} (p : E' ⟶ E) (m : ℤ)
    (e : ∀ P : PSh, HomotopyEquiv (sgl ((free R).obj P)) ((chains R).obj (disc.obj P)))
    (he : ∀ {P Q : PSh} (f : P ⟶ Q), (e P).hom ≫ (chains R).map (disc.map f) =
      (CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f) ≫ (e Q).hom)
    (h : ∀ k : ℕ, UpperTheory.RedSh.Conn (disc.map (p.app (op (SimplexCategory.mk k)))) F (m - k)) :
    UpperTheory.RedSh.Conn p F m := by
  obtain ⟨-, hinj, hge, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F
  obtain ⟨hle, hnat, -⟩ := GlobalTheory.T.chains_map_and_d_eq_sum_neg_one_pow_smul_delta R
  have := hle E
  have := hle E'
  refine UpperTheory.cochainPullback_bijective_of_termwise_bijective_injective R (res R F) hinj ((chains R).map p) m fun q => ?_
  rcases lt_or_ge 0 q with hq | hq
  · have hz : ∀ K : Cx R, K.IsStrictlyLE 0 →
        IsZero ((CochainComplex.singleFunctor (Shv R) 0).obj (K.X q)) := fun K _ =>
      (CochainComplex.singleFunctor (Shv R) 0).map_isZero (K.isZero_of_isStrictlyLE 0 q hq)
    exact ⟨fun n _ => bij_of_isZero (hz _ (hle E')) (hz _ (hle E)) _ _ _,
      (bij_of_isZero (hz _ (hle E')) (hz _ (hle E)) _ _ _).1⟩
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, q = -(k : ℤ) := ⟨(-q).toNat, by omega⟩
    let S := CochainComplex.singleFunctor (Shv R) 0
    let φ := p.app (op (SimplexCategory.mk k))
    let a : HomotopyEquiv (S.obj (((chains R).obj E').X (-(k : ℤ)))) _ :=
      (HomotopyEquiv.ofIso (S.mapIso (chainsXIso R E' k))).trans (e _)
    let b : HomotopyEquiv (S.obj (((chains R).obj E).X (-(k : ℤ)))) _ :=
      (HomotopyEquiv.ofIso (S.mapIso (chainsXIso R E k))).trans (e _)
    have w : S.map (((chains R).map p).f (-(k : ℤ))) ≫ b.hom =
        a.hom ≫ (chains R).map (disc.map φ) := by
      change S.map _ ≫ S.map (chainsXIso R E k).hom ≫ (e _).hom =
        (S.map (chainsXIso R E' k).hom ≫ (e _).hom) ≫ _
      rw [Category.assoc, he, ← Category.assoc, ← S.map_comp, hnat, S.map_comp, Category.assoc]
    have hm : m + -(k : ℤ) = m - k := by ring
    rw [hm]
    refine ⟨fun n hn => (transfer _ _ a b w _ n).1 ((h k).1 n hn),
      (transfer _ _ a b w _ _).2 (h k).2⟩

end SlopeTestRemainingChoices

theorem UpperTheory.sheafConnected_of_levelwise_connected :
    ∀ (R : Type) [CommRing R] (F : Shv R) {E' E : Spc} (p : E' ⟶ E) (m : ℤ), (∀ k : ℕ, UpperTheory.RedSh.Conn (disc.map (p.app (op (SimplexCategory.mk k)))) F (m - k)) → UpperTheory.RedSh.Conn p F m := by
  intro R _ F E' E p m h
  obtain ⟨e, -, he⟩ := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf R
  exact core R F p m e he h
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsUniqueIdempotentLiftTensorFieldStrictHense
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

private lemma algebraMap_eq_zero_of_mem (O K : Type) [CommRing O] [IsLocalRing O] [Field K]
    [Algebra O K] [Algebra.IsIntegral O K] {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) :
    algebraMap O K a = 0 := by
  have hm : Ideal.comap (algebraMap O K) ⊥ = IsLocalRing.maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := O) (⊥ : Ideal K))
  have h : a ∈ Ideal.comap (algebraMap O K) ⊥ := hm ▸ ha
  simpa using h

private noncomputable def resMap (O K : Type) [CommRing O] [IsLocalRing O] [Field K]
    [Algebra O K] [Algebra.IsIntegral O K] : IsLocalRing.ResidueField O →+* K :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) (algebraMap O K)
    (fun _ ha ↦ algebraMap_eq_zero_of_mem O K ha)

private theorem mem_maximal_of_includeLeft_eq_zero (O R K : Type) [CommRing O] [IsLocalRing O] [CommRing R] [Field K]
    [Algebra O R] [Algebra O K] [Algebra.IsIntegral O R] [Algebra.IsIntegral O K]
    (M : Ideal R) [M.IsMaximal] (x : R)
    (hx : (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] K) x = 0) : x ∈ M := by
  letI : Field (R ⧸ M) := Ideal.Quotient.field M
  haveI : Algebra.IsIntegral O (R ⧸ M) := inferInstance
  letI : Algebra (IsLocalRing.ResidueField O) K := (resMap O K).toAlgebra
  letI : Algebra (IsLocalRing.ResidueField O) (AlgebraicClosure (R ⧸ M)) :=
    ((algebraMap (R ⧸ M) (AlgebraicClosure (R ⧸ M))).comp (resMap O (R ⧸ M))).toAlgebra
  haveI : IsScalarTower O (IsLocalRing.ResidueField O) K :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField O) K :=
    Algebra.IsIntegral.tower_top O
  haveI : Algebra.IsAlgebraic (IsLocalRing.ResidueField O) K := inferInstance
  let g : K →ₐ[IsLocalRing.ResidueField O] AlgebraicClosure (R ⧸ M) := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let fR : R →+* AlgebraicClosure (R ⧸ M) :=
    (algebraMap (R ⧸ M) (AlgebraicClosure (R ⧸ M))).comp (Ideal.Quotient.mk M)
  have hc : ∀ o : O, g (algebraMap O K o) = fR (algebraMap O R o) := by
    intro o
    have h1 : algebraMap O K o =
        algebraMap (IsLocalRing.ResidueField O) K (IsLocalRing.residue O o) := rfl
    rw [h1, g.commutes]
    rfl
  letI : Algebra O (AlgebraicClosure (R ⧸ M)) := (fR.comp (algebraMap O R)).toAlgebra
  let FR : R →ₐ[O] AlgebraicClosure (R ⧸ M) := { fR with commutes' := fun _ ↦ rfl }
  let G : K →ₐ[O] AlgebraicClosure (R ⧸ M) :=
    { g.toRingHom with commutes' := fun o ↦ hc o }
  have h2 := congrArg (Algebra.TensorProduct.productMap FR G) hx
  have h3 : fR x = 0 := by
    simpa [FR, G] using h2
  have h4 : Ideal.Quotient.mk M x = 0 :=
    (algebraMap (R ⧸ M) (AlgebraicClosure (R ⧸ M))).injective (by simpa [fR] using h3)
  exact Ideal.Quotient.eq_zero_iff_mem.mp h4

private theorem exists_includeLeft_eq_pow_expChar_pow (O R K : Type) [CommRing O] [IsLocalRing O] [CommRing R] [Field K]
    [Algebra O R] [Algebra O K] [Algebra.IsIntegral O K]
    [IsSepClosed (IsLocalRing.ResidueField O)] (q : ℕ) [ExpChar (IsLocalRing.ResidueField O) q]
    (t : R ⊗[O] K) :
    ∃ n : ℕ, ∃ r : R, (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] K) r = t ^ q ^ n := by
  letI : Algebra (IsLocalRing.ResidueField O) K := (resMap O K).toAlgebra
  haveI : IsScalarTower O (IsLocalRing.ResidueField O) K :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField O) K :=
    Algebra.IsIntegral.tower_top O
  haveI : Algebra.IsAlgebraic (IsLocalRing.ResidueField O) K := inferInstance
  haveI : IsPurelyInseparable (IsLocalRing.ResidueField O) K := inferInstance
  haveI : ExpChar K q :=
    expChar_of_injective_algebraMap (algebraMap (IsLocalRing.ResidueField O) K).injective q
  rcases subsingleton_or_nontrivial (R ⊗[O] K) with hs | hs
  · exact ⟨0, 0, Subsingleton.elim _ _⟩
  haveI : ExpChar (R ⊗[O] K) q :=
    expChar_of_injective_ringHom
      (f := (Algebra.TensorProduct.includeRight : K →ₐ[O] R ⊗[O] K).toRingHom)
      (RingHom.injective _) q
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul r y =>
    obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem (IsLocalRing.ResidueField O) q y
    obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective c
    refine ⟨n, algebraMap O R o * r ^ q ^ n, ?_⟩
    rw [Algebra.TensorProduct.tmul_pow, ← hc, Algebra.TensorProduct.includeLeftRingHom_apply]
    show (algebraMap O R o * r ^ q ^ n) ⊗ₜ[O] (1 : K) = (r ^ q ^ n) ⊗ₜ[O] (algebraMap O K o)
    rw [← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  | add a b ha hb =>
    obtain ⟨n1, r1, h1⟩ := ha
    obtain ⟨n2, r2, h2⟩ := hb
    refine ⟨n1 + n2, r1 ^ q ^ n2 + r2 ^ q ^ n1, ?_⟩
    rw [map_add (f := _), map_pow, map_pow, h1, h2, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add,
      add_comm n2 n1, add_pow_expChar_pow]

theorem UpperTheory.existsUnique_idempotent_lift_tensor_field_strictHenselian :
    ∀ (O R K : Type) [CommRing O] [CommRing R] [Field K] [Algebra O R] [Algebra O K] [Algebra.IsIntegral O R] [Algebra.IsIntegral O K], SH O → ∀ e' : R ⊗[O] K, IsIdempotentElem e' → ∃! e : R, IsIdempotentElem e ∧ (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] K) e = e' := by
  intro O R K _ _ _ _ _ _ _ hO e' he'
  obtain ⟨hH, hsep⟩ := hO
  obtain ⟨q, hq⟩ := ExpChar.exists (IsLocalRing.ResidueField O)
  have hjac : ∀ y : R, (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] K) y = 0 →
      ∀ Q : Ideal R, Q.IsMaximal → y ∈ Q := fun y hy Q hQ ↦ by
    haveI := hQ
    exact mem_maximal_of_includeLeft_eq_zero O R K Q y hy
  obtain ⟨n, x, hx⟩ := exists_includeLeft_eq_pow_expChar_pow O R K q e'
  have hx' : (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] K) x = e' := by
    have hpos : 0 < q ^ n := pow_pos (expChar_pos (IsLocalRing.ResidueField O) q) n
    obtain ⟨m, hm⟩ : ∃ m, q ^ n = m + 1 := ⟨q ^ n - 1, by omega⟩
    rw [hx, hm, he'.pow_succ_eq]
  refine existsUnique_of_exists_of_unique ?_ ?_
  · let S := Algebra.adjoin O {x}
    haveI : Module.Finite O S :=
      Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral x)
    let ψ : S →+* R ⊗[O] K :=
      (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] K).comp S.val.toRingHom
    have hxS : x ∈ S := Algebra.subset_adjoin (Set.mem_singleton x)
    let c : ψ.range := ⟨e', ⟨⟨x, hxS⟩, hx'⟩⟩
    have hc : IsIdempotentElem c := Subtype.ext he'
    have hker : RingHom.ker ψ.rangeRestrict ≤ Ideal.jacobson ⊥ := by
      rw [RingHom.ker_rangeRestrict]
      intro s hs
      rw [RingHom.mem_ker] at hs
      refine Ideal.mem_sInf.mpr ?_
      rintro P ⟨-, hP⟩
      haveI := hP
      haveI : Algebra.IsIntegral S R := Algebra.IsIntegral.tower_top O
      obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := R) P (by
        intro z hz
        rw [RingHom.mem_ker] at hz
        have : z = 0 := Subtype.ext hz
        simp [this])
      rw [← hQP, Ideal.mem_comap]
      exact hjac _ hs Q hQ
    obtain ⟨e, ⟨he, hec⟩, -⟩ := GlobalTheory.existsUnique_idempotent_lift_of_henselian O ψ.rangeRestrict
      ψ.rangeRestrict_surjective hker hc
    refine ⟨(e : R), he.map S.val, ?_⟩
    exact congrArg Subtype.val hec
  · rintro y z ⟨hy, hyc⟩ ⟨hz, hzc⟩
    have hy2 : y * y = y := hy
    have hz2 : z * z = z := hz
    have he2 : e' * e' = e' := he'
    have hf0 : (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] K) (y + z - 2 * y * z) = 0 := by
      rw [map_sub, map_add (f := _), map_mul, map_mul, hyc, hzc, map_ofNat]
      linear_combination (-2 : R ⊗[O] K) * he2
    have hfj : ∀ Q : Ideal R, Q.IsMaximal → y + z - 2 * y * z ∈ Q := hjac _ hf0
    have hmem : y + z - 2 * y * z ∈ Ideal.jacobson (⊥ : Ideal R) :=
      Ideal.mem_sInf.mpr (fun Q hQ ↦ hfj Q hQ.2)
    have hu := Ideal.mem_jacobson_bot.mp hmem (-1)
    have hfid : (y + z - 2 * y * z) * (y + z - 2 * y * z) = y + z - 2 * y * z := by
      linear_combination (1 + 4 * z * z - 4 * z) * hy2 + hz2
    have hff : (y + z - 2 * y * z) * ((y + z - 2 * y * z) * -1 + 1) = 0 := by
      linear_combination (-1 : R) * hfid
    have hf : y + z - 2 * y * z = 0 := (hu.mul_left_eq_zero).mp hff
    linear_combination (-1 + 2 * z) * hy2 + (1 - 2 * y) * hz2 + (y - z) * hf
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsSectionOfIntegralSurjectiveAlgClosed
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem UpperTheory.exists_section_of_integral_surjective_algClosed :
    ∀ (K : Type) [Field K] [IsAlgClosed K] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of K)) [IsIntegralHom g] [Surjective g], ∃ s : Spec (CommRingCat.of K) ⟶ Y, s ≫ g = 𝟙 _ := by
  intro K _ _ Y g _ _
  haveI : IsAffine Y := isAffine_of_isAffineHom g
  obtain ⟨y, -⟩ := g.surjective (IsLocalRing.closedPoint K)
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := Y)).exists_closed_singleton ⟨y, trivial⟩
  haveI : IsIntegralHom (Y.fromSpecResidueField x ≫ g) := by
    rw [isClosed_singleton_iff_isClosedImmersion] at hx
    infer_instance
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = Y.fromSpecResidueField x ≫ g :=
    ⟨_, Spec.map_preimage _⟩
  haveI : IsIso φ := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine IsAlgClosed.ringHom_bijective_of_isIntegral _ ?_
    rw [← IsIntegralHom.SpecMap_iff, hφ]
    infer_instance
  refine ⟨Spec.map (inv φ) ≫ Y.fromSpecResidueField x, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp]
  simp
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.CechNervePullbackRepresentableOfIsPullback
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem UpperTheory.cechNerve_pullback_representable_of_isPullback :
    ∀ {Y X Y' X' Z Z' : Scheme.{0}} (f : Y ⟶ X) (f' : Y' ⟶ X') (b : X' ⟶ X) (m : cech f' ⟶ cech f), IsPullback m (cechAug f') (cechAug f) (sch.map b) → ∀ (k : SimplexCategoryᵒᵖ) (e : yoneda.obj Z ≅ (cech f).obj k) (g : Z ⟶ X) (c : Z' ⟶ Z) (g' : Z' ⟶ X'), e.hom ≫ (cechAug f).app k = yoneda.map g → IsPullback c g' g b → ∃ e' : yoneda.obj Z' ≅ (cech f').obj k, e'.hom ≫ m.app k = yoneda.map c ≫ e.hom := by
  intro Y X Y' X' Z Z' f f' b m hm k e g c g' he hc
  have h1 : IsPullback (m.app k) ((cechAug f').app k) ((cechAug f).app k) (yoneda.map b) :=
    hm.map ((evaluation _ _).obj k)
  have h2 : IsPullback (m.app k ≫ e.inv) ((cechAug f').app k) (yoneda.map g) (yoneda.map b) := by
    refine h1.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp [← he]
      exact Category.comp_id _
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
  have h3 : IsPullback (yoneda.map c) (yoneda.map g') (yoneda.map g) (yoneda.map b) :=
    hc.map yoneda
  refine ⟨IsPullback.isoIsPullback _ _ h3 h2, ?_⟩
  have h4 := IsPullback.isoIsPullback_hom_fst _ _ h3 h2
  calc (IsPullback.isoIsPullback _ _ h3 h2).hom ≫ m.app k
      = ((IsPullback.isoIsPullback _ _ h3 h2).hom ≫ (m.app k ≫ e.inv)) ≫ e.hom := by simp
    _ = yoneda.map c ≫ e.hom := by rw [h4]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsCyclotomicRootOfStrictHenselian
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem UpperTheory.exists_cyclotomic_root_of_strictHenselian :
    ∀ (q : ℕ) [NeZero q] (O : Type) [CommRing O], SH O → IsUnit (q : O) → ∃ ζ : O, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
  intro q _ O _ hO hq
  obtain ⟨hH, hsep⟩ := hO
  have key : ∀ (p : Polynomial O) (x : O), IsLocalRing.residue O (p.eval x) =
      (p.map (IsLocalRing.residue O)).eval (IsLocalRing.residue O x) := by
    intro p x
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  have hqk : ((q : ℕ) : IsLocalRing.ResidueField O) ≠ 0 := by
    have := (IsLocalRing.residue_ne_zero_iff_isUnit (q : O)).2 hq
    simpa using this
  haveI : NeZero ((q : ℕ) : IsLocalRing.ResidueField O) := ⟨hqk⟩
  have hdeg : (Polynomial.cyclotomic q (IsLocalRing.ResidueField O)).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  obtain ⟨r, hr⟩ := IsSepClosed.exists_root _ hdeg
    (Polynomial.separable_cyclotomic q (IsLocalRing.ResidueField O))
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective r
  have h1 : (Polynomial.cyclotomic q O).eval a₀ ∈ IsLocalRing.maximalIdeal O := by
    rw [← IsLocalRing.residue_eq_zero_iff, key, Polynomial.map_cyclotomic]
    exact hr
  have h2 : IsUnit ((Polynomial.derivative (Polynomial.cyclotomic q O)).eval a₀) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, key, ← Polynomial.derivative_map,
      Polynomial.map_cyclotomic]
    have h0 := (Polynomial.separable_cyclotomic q (IsLocalRing.ResidueField O)).aeval_derivative_ne_zero
      (x := IsLocalRing.residue O a₀) (by simpa [Polynomial.coe_aeval_eq_eval] using hr)
    simpa [Polynomial.coe_aeval_eq_eval] using h0
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (Polynomial.cyclotomic q O)
    (Polynomial.cyclotomic.monic q O) a₀ h1 h2
  refine ⟨a, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact ha
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.LocallyConstantComapBijective
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

private theorem clopen_pre_inj {B B' : Type} [CommRing B] [CommRing B'] (φ : B →+* B')
    (h : ∀ e' : B', IsIdempotentElem e' → ∃! e : B, IsIdempotentElem e ∧ φ e = e')
    {C D : Set (PrimeSpectrum B)} (hC : IsClopen C) (hD : IsClopen D)
    (hCD : PrimeSpectrum.comap φ ⁻¹' C = PrimeSpectrum.comap φ ⁻¹' D) : C = D := by
  obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.1 hC
  obtain ⟨d, hd, rfl⟩ := PrimeSpectrum.isClopen_iff.1 hD
  have h1 : φ e = φ d := by
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem (he.map φ) (hd.map φ)
    apply SetLike.coe_injective
    rw [← PrimeSpectrum.comap_basicOpen, ← PrimeSpectrum.comap_basicOpen]
    exact hCD
  rw [(h (φ e) (he.map φ)).unique ⟨he, rfl⟩ ⟨hd, h1.symm⟩]

private theorem clopen_pre_surj {B B' : Type} [CommRing B] [CommRing B'] (φ : B →+* B')
    (h : ∀ e' : B', IsIdempotentElem e' → ∃! e : B, IsIdempotentElem e ∧ φ e = e')
    {C' : Set (PrimeSpectrum B')} (hC' : IsClopen C') :
    ∃ C : Set (PrimeSpectrum B), IsClopen C ∧ PrimeSpectrum.comap φ ⁻¹' C = C' := by
  obtain ⟨e', he', rfl⟩ := PrimeSpectrum.isClopen_iff.1 hC'
  obtain ⟨e, ⟨he, rfl⟩, -⟩ := h e' he'
  exact ⟨_, PrimeSpectrum.isClopen_iff.2 ⟨e, he, rfl⟩, rfl⟩

theorem UpperTheory.locallyConstant_comap_bijective :
    ∀ (B B' : Type) [CommRing B] [CommRing B'] (φ : B →+* B') (Y : Type), (∀ e' : B', IsIdempotentElem e' → ∃! e : B, IsIdempotentElem e ∧ φ e = e') → Function.Bijective (fun a : LocallyConstant (PrimeSpectrum B) Y => a.comap ⟨PrimeSpectrum.comap φ, PrimeSpectrum.continuous_comap φ⟩) := by
  intro B B' _ _ φ Y h
  constructor
  · intro a b hab
    have hfib : ∀ y, (a : PrimeSpectrum B → Y) ⁻¹' {y} = (b : PrimeSpectrum B → Y) ⁻¹' {y} := by
      intro y
      apply clopen_pre_inj φ h (a.isLocallyConstant.isClopen_fiber y)
        (b.isLocallyConstant.isClopen_fiber y)
      ext q
      have hq : a (PrimeSpectrum.comap φ q) = b (PrimeSpectrum.comap φ q) :=
        DFunLike.congr_fun hab q
      change a (PrimeSpectrum.comap φ q) = y ↔ b (PrimeSpectrum.comap φ q) = y
      rw [hq]
    ext p
    have hp : p ∈ (b : PrimeSpectrum B → Y) ⁻¹' {a p} := by
      rw [← hfib]
      rfl
    exact hp.symm
  · intro a'
    choose C hCc hC using fun y =>
      clopen_pre_surj φ h (a'.isLocallyConstant.isClopen_fiber y)
    have hdisj : ∀ y z, y ≠ z → C y ∩ C z = ∅ := by
      intro y z hyz
      apply clopen_pre_inj φ h ((hCc y).inter (hCc z)) isClopen_empty
      rw [Set.preimage_inter, hC, hC, Set.preimage_empty]
      ext q
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      exact fun h1 h2 => hyz (h1.symm.trans h2)
    have hcov : (⋃ y ∈ Set.range a', C y) = Set.univ := by
      apply clopen_pre_inj φ h
        (a'.range_finite.isClopen_biUnion fun y _ => hCc y) isClopen_univ
      rw [Set.preimage_iUnion₂, Set.preimage_univ]
      ext q
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      exact ⟨a' q, ⟨q, rfl⟩, by rw [hC]; rfl⟩
    have hex : ∀ p, ∃ y, p ∈ C y := by
      intro p
      have hp : p ∈ ⋃ y ∈ Set.range a', C y := hcov ▸ Set.mem_univ p
      obtain ⟨y, -, hy⟩ := Set.mem_iUnion₂.1 hp
      exact ⟨y, hy⟩
    choose a ha using hex
    have hiff : ∀ p y, a p = y ↔ p ∈ C y := by
      intro p y
      constructor
      · rintro rfl
        exact ha p
      · intro hy
        by_contra hne
        have : p ∈ C (a p) ∩ C y := ⟨ha p, hy⟩
        rw [hdisj _ _ hne] at this
        exact this
    have hlc : IsLocallyConstant a := by
      refine (IsLocallyConstant.iff_isOpen_fiber).2 fun y => ?_
      have : a ⁻¹' {y} = C y := by
        ext p
        exact hiff p y
      rw [this]
      exact (hCc y).isOpen
    refine ⟨⟨a, hlc⟩, ?_⟩
    ext q
    have hq : q ∈ PrimeSpectrum.comap φ ⁻¹' C (a' q) := by
      rw [hC]
      rfl
    exact (hiff _ _).2 hq
end

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

private theorem bijective_pull_spMap_tw_zero : ∀ (q : ℕ) [NeZero q] (i : ℤ) (B B' : Type) [CommRing B] [CommRing B'] (φ : B →+* B'), IsUnit (q : B) →
    (∃ ζ : B, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) →
    (∀ e' : B', IsIdempotentElem e' → ∃! e : B, IsIdempotentElem e ∧ φ e = e') →
    Function.Bijective (pull _ (spMap φ) (tw q i) 0) := by
  intro q _ i B B' _ _ φ hq ⟨ζ, hζ⟩ hid
  obtain ⟨E, hE⟩ := UpperTheory.exists_tateTwist_sections_equiv_locallyConstant q i
  obtain ⟨-, e, he, -⟩ := GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q i)
  let g : Spec (CommRingCat.of B') ⟶ Spec (CommRingCat.of B) := Spec.map (CommRingCat.ofHom φ)
  let ζ₀ : Prim q Γ(Spec (CommRingCat.of B), ⊤) :=
    Prim.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom ⟨ζ, hq, hζ⟩
  have hres : Function.Bijective (Sec.res (F := tw q i) g) := by
    have h1 := UpperTheory.locallyConstant_comap_bijective B B' φ (ZMod q) hid
    have hc : ∀ s, E _ (ζ₀.map g.appTop.hom) (Sec.res g s) = (E _ ζ₀ s).comap ⟨g, g.continuous⟩ := hE _ _ g ζ₀
    have hcomp : (E _ (ζ₀.map g.appTop.hom)) ∘ (Sec.res (F := tw q i) g) = (fun a : LocallyConstant (PrimeSpectrum B) (ZMod q) => a.comap ⟨PrimeSpectrum.comap φ, PrimeSpectrum.continuous_comap φ⟩) ∘ (E _ ζ₀) := by
      funext s
      exact hc s
    refine (Function.Bijective.of_comp_iff' (E _ (ζ₀.map g.appTop.hom)).bijective _).1 ?_
    rw [hcomp]
    exact h1.comp (E _ ζ₀).bijective
  have hp : (pull _ (sch.map g) (tw q i) 0) ∘ (e _) = (e _) ∘ (Sec.res (F := tw q i) g) := by
    funext s
    exact he g s
  refine (Function.Bijective.of_comp_iff _ (e _).bijective).1 ?_
  rw [hp]
  exact (e _).bijective.comp hres

private theorem eqv_ring : ∀ (q : ℕ) (O R K : Type) [CommRing O] [CommRing R] [Field K] [Algebra O R] [Algebra O K]
    [Algebra.IsIntegral O R] [Algebra.IsIntegral O K], SH O → IsUnit (q : O) → ∀ i : ℤ,
    Eqv _ (spMap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] K)) (tw q i) := by
  intro q O R K _ _ _ _ _ _ _ hSH hq i n
  obtain ⟨hH, -⟩ := id hSH
  haveI : NeZero q := ⟨by
    rintro rfl
    simp at hq⟩
  have hqR : IsUnit (q : R) := by simpa using hq.map (algebraMap O R)
  haveI : Algebra.IsIntegral O (R ⊗[O] K) := by
    have : Algebra.IsIntegral R (R ⊗[O] K) := inferInstance
    exact Algebra.IsIntegral.trans R
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have hs := (GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q i)).1
    haveI := hs (sp R) n hn
    haveI := hs (sp (R ⊗[O] K)) n hn
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  · obtain ⟨ζ, hζ⟩ := UpperTheory.exists_cyclotomic_root_of_strictHenselian q O hSH hq
    refine bijective_pull_spMap_tw_zero q i R _ _ hqR ⟨algebraMap O R ζ, ?_⟩ (UpperTheory.existsUnique_idempotent_lift_tensor_field_strictHenselian O R K hSH)
    rw [Polynomial.aeval_algebraMap_apply, hζ, map_zero]
  · haveI := UpperTheory.acyclic_spec_integral_algebra_strictHenselian q O R hSH hq n i hn
    haveI := UpperTheory.acyclic_spec_integral_algebra_strictHenselian q O (R ⊗[O] K) hSH hq n i hn
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

private theorem T_key : ∀ (q : ℕ) (O K : Type) [CommRing O] [Field K] [Algebra O K] [Algebra.IsIntegral O K], SH O → IsUnit (q : O) →
    ∀ (i : ℤ) {Z Z' W : Scheme.{0}} (r : Z ⟶ W) [IsIntegralHom r] (e : W ≅ Spec (CommRingCat.of O)) (c : Z' ⟶ Z)
      (g' : Z' ⟶ Spec (CommRingCat.of K)),
      IsPullback c g' r (Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ e.inv) → Eqv _ (sch.map c) (tw q i) := by
  intro q O K _ _ _ _ hSH hq i Z Z' W r _ e c g' hpb
  obtain ⟨hiso, hcomp, -, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  have hg : IsIntegralHom (r ≫ e.hom) := inferInstance
  haveI : IsAffine Z := isAffine_of_isAffineHom (r ≫ e.hom)
  let φ : CommRingCat.of O ⟶ Γ(Z, ⊤) := Spec.preimage (Z.isoSpec.inv ≫ r ≫ e.hom)
  have hφ : Spec.map φ = Z.isoSpec.inv ≫ r ≫ e.hom := Spec.map_preimage _
  letI alg : Algebra O Γ(Z, ⊤) := φ.hom.toAlgebra
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap O Γ(Z, ⊤))) = Z.isoSpec.inv ≫ r ≫ e.hom := hφ
  haveI hint : Algebra.IsIntegral O Γ(Z, ⊤) := by
    have h2 : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap O Γ(Z, ⊤)))) := by
      rw [hmap]; infer_instance
    rw [IsIntegralHom.SpecMap_iff] at h2
    exact (algebraMap_isIntegral_iff (R := O) (A := Γ(Z, ⊤))).1 h2
  have sq1 := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct O Γ(Z, ⊤) K)
  have sq2 : IsPullback (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : Γ(Z, ⊤) →+* Γ(Z, ⊤) ⊗[O] K)) ≫ Z.isoSpec.inv) (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := O) (A := Γ(Z, ⊤)) (B := K)).toRingHom)) (r ≫ e.hom) (Spec.map (CommRingCat.ofHom (algebraMap O K))) := by
    refine IsPullback.of_iso sq1 (Iso.refl _) Z.isoSpec.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp [hmap]
    · simp
  have sq3 : IsPullback c g' (r ≫ e.hom) (Spec.map (CommRingCat.ofHom (algebraMap O K))) := by
    refine IsPullback.of_iso hpb (Iso.refl _) (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp
  obtain ⟨u, hu⟩ : ∃ u : Z' ≅ Spec (CommRingCat.of (Γ(Z, ⊤) ⊗[O] K)), u.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : Γ(Z, ⊤) →+* Γ(Z, ⊤) ⊗[O] K)) ≫ Z.isoSpec.inv = c :=
    ⟨_, sq3.isoIsPullback_hom_fst _ _ sq2⟩
  have hE := eqv_ring q O Γ(Z, ⊤) K hSH hq i
  have h1 : sch.map c ≫ sch.map Z.isoSpec.hom = sch.map u.hom ≫ spMap (Algebra.TensorProduct.includeLeftRingHom : Γ(Z, ⊤) →+* Γ(Z, ⊤) ⊗[O] K) := by
    rw [← sch.map_comp, ← sch.map_comp, ← hu]
    simp
  have h2 : Eqv _ (sch.map c ≫ sch.map Z.isoSpec.hom) (tw q i) := by
    rw [h1]
    exact (hcomp _ _ _ _ _).1 (hiso _ _ _ inferInstance) hE
  exact (hcomp _ _ _ _ _).2.2 (hiso _ _ _ inferInstance) h2

private theorem eqv_of_forall_conn {R : Type} [CommRing R] {E E' : Spc} {f : E ⟶ E'} {F : Shv R}
    (h : ∀ m, UpperTheory.RedSh.Conn f F m) : Eqv R f F := fun n => (h (n + 1)).1 n (by omega)

private theorem conn_of_eqv {R : Type} [CommRing R] {E E' : Spc} {f : E ⟶ E'} {F : Shv R}
    (h : Eqv R f F) (m : ℤ) : UpperTheory.RedSh.Conn f F m := ⟨fun n _ => h n, (h m).1⟩

private theorem L_loc : ∀ (q : ℕ) (O : Type) [CommRing O], SH O → IsUnit (q : O) → ∀ (i : ℤ) {Y W : Scheme.{0}} (g : Y ⟶ W)
    [IsIntegralHom g] [Surjective g] (e : W ≅ Spec (CommRingCat.of O)), Eqv _ (cechAug g) (tw q i) := by
  intro q O _ hSH hq i Y W g _ _ e
  obtain ⟨hH, hS⟩ := id hSH
  obtain ⟨hiso, hcomp, -, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  let K := AlgebraicClosure (IsLocalRing.ResidueField O)
  haveI : Algebra.IsIntegral O (IsLocalRing.ResidueField O) :=
    Algebra.IsIntegral.of_surjective (Algebra.ofId O (IsLocalRing.ResidueField O)) IsLocalRing.residue_surjective
  haveI : Algebra.IsIntegral O K := Algebra.IsIntegral.trans (IsLocalRing.ResidueField O)
  let b : Spec (CommRingCat.of K) ⟶ W := Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ e.inv
  have hpb := IsPullback.of_hasPullback g b
  haveI : IsIntegralHom (pullback.snd g b) := MorphismProperty.of_isPullback hpb inferInstance
  haveI : Surjective (pullback.snd g b) := MorphismProperty.of_isPullback hpb inferInstance
  obtain ⟨s, hs⟩ := UpperTheory.exists_section_of_integral_surjective_algClosed K (pullback.snd g b)
  have hsplit : Eqv _ (cechAug (pullback.snd g b)) (tw q i) := UpperTheory.cechAugmentation_equiv_of_section _ _ s hs _
  obtain ⟨m, hm, -⟩ := GlobalTheory.T.etaleCechNerve_baseChange_isPullback _ _ _ _ _ _ _ _ hpb
  have hb : Eqv _ (sch.map b) (tw q i) := by
    have : IsPullback b (𝟙 _) (𝟙 W) b := IsPullback.of_vert_isIso ⟨by simp⟩
    exact T_key q O K hSH hq i (𝟙 W) e b (𝟙 _) this
  have hlev : Eqv _ m (tw q i) := by
    refine eqv_of_forall_conn fun n => UpperTheory.sheafConnected_of_levelwise_connected _ _ m n fun k => conn_of_eqv ?_ _
    obtain ⟨Z, π, ez, hπ, hz⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable @IsIntegralHom _ _ g inferInstance (op (SimplexCategory.mk k))
    have hpz := IsPullback.of_hasPullback (π ≫ g) b
    obtain ⟨ez', hez'⟩ := UpperTheory.cechNerve_pullback_representable_of_isPullback g (pullback.snd g b) b m hm (op (SimplexCategory.mk k)) ez (π ≫ g)
      (pullback.fst (π ≫ g) b) (pullback.snd (π ≫ g) b) hz hpz
    have h1 : Eqv _ (sch.map (pullback.fst (π ≫ g) b)) (tw q i) :=
      T_key q O K hSH hq i (π ≫ g) e _ _ hpz
    have h3 : Eqv _ (disc.map ez'.hom ≫ disc.map (m.app (op (SimplexCategory.mk k)))) (tw q i) := by
      rw [← Functor.map_comp, hez', Functor.map_comp]
      exact (hcomp _ _ _ _ _).1 h1 (hiso _ _ _ inferInstance)
    exact (hcomp _ _ _ _ _).2.1 (hiso _ _ _ inferInstance) h3
  have hc : m ≫ cechAug g = cechAug (pullback.snd g b) ≫ sch.map b := hm.w
  have h2 : Eqv _ (m ≫ cechAug g) (tw q i) := by
    rw [hc]; exact (hcomp _ _ _ _ _).1 hsplit hb
  exact (hcomp _ _ _ _ _).2.1 hlev h2

theorem UpperTheory.etaleCohomology_excisionAxiom_holds : GlobalTheory.EtC.B4 := by
  intro q Y X f _ _ hq i
  obtain ⟨hiso, hcomp, -, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  have hqc₁ : QcqsOver (cechAug f ≫ sch.map (𝟙 X)) := by
    intro k
    obtain ⟨Z, π, e, hπ, he⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable @IsIntegralHom _ _ f inferInstance k
    refine ⟨Z, π ≫ f, e, inferInstance, inferInstance, ?_⟩
    rw [sch.map_id, Category.comp_id]
    exact he
  have hqc₂ : QcqsOver (sch.map (𝟙 X)) := by
    intro k
    refine ⟨X, 𝟙 X, Iso.refl _, inferInstance, inferInstance, ?_⟩
    rw [sch.map_id]
    simp
    rfl
  refine UpperTheory.Cb.equiv_of_stalkwise_base_change _ (tw q i) X (cech f) (sch.obj X) (cechAug f) (sch.map (𝟙 X)) (UpperTheory.Cb.tateTwist_finitary q i)
    hqc₁ hqc₂ ?_
  intro O _ s hs
  obtain ⟨e₁, e₂, h⟩ := GlobalTheory.T.baseChange_cechNerveAugmentation_iso X X Y (𝟙 X) f (Over.mk s)
  have hO : IsUnit (q : O) := by
    simpa using (hq.map s.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom
  let w : pullback (𝟙 X) (Over.mk s).hom ≅ Spec (CommRingCat.of O) := asIso (pullback.snd _ _)
  have hfst : IsPullback (pullback.fst f (pullback.fst (𝟙 X) (Over.mk s).hom)) (pullback.snd f (pullback.fst (𝟙 X) (Over.mk s).hom)) f (pullback.fst (𝟙 X) (Over.mk s).hom) := IsPullback.of_hasPullback _ _
  haveI : IsIntegralHom (pullback.snd f (pullback.fst (𝟙 X) (Over.mk s).hom)) := MorphismProperty.of_isPullback hfst inferInstance
  haveI : Surjective (pullback.snd f (pullback.fst (𝟙 X) (Over.mk s).hom)) := MorphismProperty.of_isPullback hfst inferInstance
  have h2 : Eqv _ (cechAug (pullback.snd f (pullback.fst (𝟙 X) (Over.mk s).hom))) (tw q i) :=
    L_loc q O hs.1 hO i _ w
  have h3 : Eqv _ (e₁.hom ≫ (bcMap (cechAug f) (sch.map (𝟙 X))).app (Over.mk s)) (tw q i) := by
    rw [h]
    exact (hcomp _ _ _ _ _).1 h2 (hiso _ _ _ inferInstance)
  exact (hcomp _ _ _ _ _).2.1 (hiso _ _ _ inferInstance) h3
