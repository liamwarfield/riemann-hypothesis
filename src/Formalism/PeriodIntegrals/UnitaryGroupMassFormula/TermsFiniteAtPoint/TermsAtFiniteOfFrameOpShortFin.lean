module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.ZhatIntegralHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdentityCellTrace.TraceOneHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.PositiveWeightHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.ResFinAlt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.CellMain

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.FixedZ
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.FixedRel
noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

section Int

variable {E : Type} [Field E] [NumberField E]

def IntE (x : E) : Prop := ∃ o : 𝓞 E, (o : E) = x

theorem IntE.add {x y : E} (hx : IntE x) (hy : IntE y) : IntE (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, map_add (algebraMap (𝓞 E) E) a b⟩
theorem IntE.mul {x y : E} (hx : IntE x) (hy : IntE y) : IntE (x * y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a * b, map_mul (algebraMap (𝓞 E) E) a b⟩
theorem IntE.neg {x : E} (hx : IntE x) : IntE (-x) := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨-a, map_neg (algebraMap (𝓞 E) E) a⟩
theorem IntE.sub {x y : E} (hx : IntE x) (hy : IntE y) : IntE (x - y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a - b, map_sub (algebraMap (𝓞 E) E) a b⟩
theorem IntE.nat (n : ℕ) : IntE (n : E) := ⟨n, map_natCast (algebraMap (𝓞 E) E) n⟩
theorem IntE.zero : IntE (0 : E) := ⟨0, map_zero (algebraMap (𝓞 E) E)⟩
theorem IntE.sum {ι : Type*} (s : Finset ι) (g : ι → E) (h : ∀ i ∈ s, IntE (g i)) : IntE (∑ i ∈ s, g i) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact IntE.zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact IntE.add (h a (Finset.mem_insert_self a s)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

end Int

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def piL (e f : Fin r → S.V) : S.V →ₗ[E] S.V := LinearMap.id - ∑ c, (S.hT (f c)).smulRight (e c)

theorem piL_apply (e f : Fin r → S.V) (x : S.V) : piL e f x = x - ∑ c, S.hT (f c) x • e c := by
  simp [piL, LinearMap.smulRight_apply]

theorem herm_star (x y : S.V) : star (S.hT x y) = S.hT y x := by
  exact S.herm.eq x y

theorem related_gen (hH : HeisOp) (hSk : SkewSolve) {T T' : E} (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T)
    (f : Fin r → S.V)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ o : 𝓞 E, (o : E) = S.hT x y)
    (he : ∀ c, F.fl.e c ∈ Λ)
    (hef : ∀ a b, S.hT (F.fl.e a) (f b) = if a = b then 1 else 0)
    (θ : 𝓞 E) (hθ : (θ : E) + star (θ : E) = 1)
    (nd nQ : ℕ) (hfint : ∀ x ∈ Λ, ∀ c, IntE ((nd : E) * S.hT (f c) x))
    (β : Matrix (Fin r) (Fin (r + 1)) E) (Q : Matrix (Fin (r + 1)) (Fin r) E) (v l : Fin (r + 1) → E)
    (hind : ∀ u : Fin r → E, (∀ b, ∑ c, u c * β c b = 0) → u = 0)
    (hβQ : β * Q = 1) (hv : ∀ c, ∑ b, β c b * v b = 0)
    (hQβ : ∀ i j, (Q * β) i j = (if i = j then 1 else 0) - v i * l j)
    (hQint : ∀ b c, IntE ((nQ : E) * Q b c))
    (y1 y2 : LFlag S r T')
    (hzt1 : y1.zt = frame y1 (Fin.last r)) (hzt2 : y2.zt = frame y2 (Fin.last r))
    (hy1 : ∀ b, frame y1 b ∈ Λ)
    (hβ1 : ∀ c b, S.hT (F.fl.e c) (frame y1 b) = β c b) (hβ2 : ∀ c b, S.hT (F.fl.e c) (frame y2 b) = β c b)
    (hgram : ∀ a b, S.hT (frame y2 a) (frame y2 b) = S.hT (frame y1 a) (frame y1 b))
    (hδ : ∀ b, ∃ lam ∈ Λ, frame y2 b - frame y1 b = (((nd * nQ) ^ 2 : ℕ) : E) • lam)
    (hι : piL F.fl.e f (∑ b, v b • frame y1 b) = piL F.fl.e f (∑ b, v b • frame y2 b)) :
    DCRel Λ F y1 y2 := by
  set e := F.fl.e with he_def
  have hee : ∀ a b, S.hT (e a) (e b) = 0 := F.fl.e_iso
  have hfe : ∀ a b, S.hT (f a) (e b) = if a = b then 1 else 0 := fun a b => by
    rw [← herm_star, hef b a]
    by_cases h : b = a
    · subst h; simp
    · simp [h, Ne.symm h]
  have hpi_e : ∀ a x, S.hT (e a) (piL e f x) = S.hT (e a) x := fun a x => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [piL_apply, map_sub, map_sum, hee]
  have hpi_f : ∀ a x, S.hT (f a) (piL e f x) = 0 := fun a x => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [piL_apply, map_sub, map_sum, hfe]
  have hmemE : ∀ (x : E) (w : S.V), IntE x → w ∈ Λ → x • w ∈ Λ := by
    rintro x w ⟨o, rfl⟩ hw
    show (algebraMap (𝓞 E) E o) • w ∈ Λ
    rw [algebraMap_smul]
    exact Λ.smul_mem o hw
  have hnat : ∀ (k : ℕ) (w : S.V), w ∈ Λ → (k : E) • w ∈ Λ := fun k w hw => hmemE _ w (IntE.nat k) hw
  choose lam hlam hδeq using hδ

  let P : Fin (r + 1) → S.V := fun b => (nd : E) • piL e f (lam b)
  have hP : ∀ b, P b ∈ Λ := by
    intro b
    have : P b = (nd : E) • lam b - ∑ c, ((nd : E) * S.hT (f c) (lam b)) • e c := by
      simp only [P, piL_apply, smul_sub, Finset.smul_sum, smul_smul]
    rw [this]
    refine Λ.sub_mem (hnat nd _ (hlam b)) (Λ.sum_mem fun c _ => hmemE _ _ (hfint _ (hlam b) c) (he c))
  let δ : Fin (r + 1) → S.V := fun b => frame y2 b - frame y1 b
  let ρ : Fin (r + 1) → S.V := fun b => piL e f (δ b)
  have hδe : ∀ c b, S.hT (e c) (δ b) = 0 := fun c b => by simp [δ, map_sub, hβ1, hβ2]
  have hρe : ∀ c b, S.hT (e c) (ρ b) = 0 := fun c b => by simp only [ρ, hpi_e, hδe]
  have hρsum : ∑ b, v b • ρ b = 0 := by
    have : ∑ b, v b • ρ b = piL e f (∑ b, v b • frame y2 b) - piL e f (∑ b, v b • frame y1 b) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [ρ, δ, map_sum, map_smul, map_sub, smul_sub, Finset.sum_sub_distrib]
    rw [this, ← hι, sub_self]
  obtain ⟨qo, hqo⟩ : ∃ qo : Fin (r + 1) → Fin r → 𝓞 E, ∀ b c, (qo b c : E) = (nQ : E) * Q b c :=
    ⟨fun b c => (hQint b c).choose, fun b c => (hQint b c).choose_spec⟩
  let a' : Fin r → S.V := fun c => ∑ b, (qo b c : E) • P b
  let a : Fin r → S.V := fun c => ∑ b, Q b c • ρ b
  have ha' : ∀ c, a' c ∈ Λ := fun c => Λ.sum_mem fun b _ => hmemE _ _ ⟨qo b c, rfl⟩ (hP b)
  have haa' : ∀ c, a c = ((nd * nQ : ℕ) : E) • a' c := by
    intro c
    simp only [a, a', ρ, P, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show δ b = (((nd * nQ) ^ 2 : ℕ) : E) • lam b from hδeq b, map_smul, smul_smul, hqo]
    congr 1
    push_cast
    ring
  have ha : ∀ c, a c ∈ Λ := fun c => by rw [haa']; exact hnat _ _ (ha' c)
  have hea : ∀ c d, S.hT (e c) (a d) = 0 := fun c d => by simp [a, map_sum, hρe]

  let s : Matrix (Fin r) (Fin r) E := fun c d =>
    if c < d then -S.hT (a c) (a d) else if c = d then -((θ : E) * S.hT (a c) (a c)) else 0
  have hs : ∀ c d, s c d + star (s d c) = -S.hT (a c) (a d) := by
    intro c d
    rcases lt_trichotomy c d with h | h | h
    · simp [s, h, not_lt.2 h.le, h.ne']
    · subst h
      have hh : star (S.hT (a c) (a c)) = S.hT (a c) (a c) := herm_star _ _
      simp only [s, lt_irrefl, if_false, if_true, star_neg, star_mul', hh]
      linear_combination (-(S.hT (a c) (a c))) * hθ
    · simp [s, h, not_lt.2 h.le, h.ne, h.ne', herm_star]
  have haa : ∀ c d, S.hT (a c) (a d) = (((nd * nQ) ^ 2 : ℕ) : E) * S.hT (a' c) (a' d) := by
    intro c d
    rw [haa', haa', map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply]
    simp only [starRingEnd_apply, star_natCast, smul_eq_mul]
    push_cast
    ring
  let s' : Matrix (Fin r) (Fin r) E := fun c d =>
    if c < d then -S.hT (a' c) (a' d) else if c = d then -((θ : E) * S.hT (a' c) (a' c)) else 0
  have hss' : ∀ c d, s c d = (((nd * nQ) ^ 2 : ℕ) : E) * s' c d := by
    intro c d
    simp only [s, s', haa]
    split_ifs <;> ring
  have hs'int : ∀ c d, IntE (s' c d) := by
    intro c d
    simp only [s']
    split_ifs
    · exact (IntE.neg (hint _ (ha' c) _ (ha' d)))
    · exact IntE.neg (IntE.mul (show IntE (θ : E) from ⟨θ, rfl⟩) (hint _ (ha' c) _ (ha' c)))
    · exact IntE.zero
  have hsint : ∀ c d, ∃ o : 𝓞 E, (o : E) = s c d := fun c d => by
    rw [hss']; exact (IntE.nat _).mul (hs'int c d)
  obtain ⟨n1, hn1, hn1act⟩ := hH E S r T Λ F a s hint he ha hea hsint hs
  simp only [← he_def] at hn1act
  have hiso1 : ∀ x y, S.hT (n1 x) (n1 y) = S.hT x y := hn1.1.1
  have hn1e : ∀ c, n1 (e c) = e c := by
    intro c
    rw [hn1act, heisFun]
    have : ∀ c', S.hT (a c') (e c) = 0 := fun c' => by rw [← herm_star, hea]; simp
    simp [hee, this]
  have hrow : ∀ c b, S.hT (e c) (n1 (frame y1 b)) = β c b := fun c b => by
    rw [← hn1e c, hiso1, hβ1]

  have hsum_a : ∀ b, ∑ c, S.hT (e c) (frame y1 b) • a c = ρ b := by
    intro b
    simp only [a, hβ1, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have : ∀ d, ∑ c, (β c b * Q d c) • ρ d = ((Q * β) d b) • ρ d := fun d => by
      rw [← Finset.sum_smul, Matrix.mul_apply]
      congr 1
      exact Finset.sum_congr rfl fun c _ => mul_comm _ _
    simp only [this, hQβ, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have h2 : ∑ d, (v d * l b) • ρ d = l b • ∑ d, v d • ρ d := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun d _ => by rw [smul_smul, mul_comm]
    rw [h2, hρsum, smul_zero, sub_zero]
  let x' : Matrix (Fin r) (Fin (r + 1)) E := fun c b =>
    S.hT (f c) (δ b) + S.hT (a c) (frame y1 b) - ∑ d, s c d * β d b
  have hk : ∀ b, frame y2 b = n1 (frame y1 b) + ∑ c, x' c b • e c := by
    intro b
    have hy2 : frame y2 b = frame y1 b + ρ b + ∑ c, S.hT (f c) (δ b) • e c := by
      simp only [ρ, piL_apply, δ]
      abel
    rw [hn1act, heisFun, hsum_a, hy2]
    simp only [x', add_smul, sub_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_smul, hβ1]
    abel

  have hcol : ∀ d a0, S.hT (n1 (frame y1 a0)) (e d) = star (β d a0) := fun d a0 => by
    rw [← herm_star, hrow]
  have hid : ∀ a0 b, ∑ c, (star (β c a0) * x' c b + star (x' c a0) * β c b) = 0 := by
    intro a0 b
    have h := hgram a0 b
    rw [hk a0, hk b, ← hiso1 (frame y1 a0) (frame y1 b)] at h
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), LinearMap.add_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
      LinearMap.smul_apply, smul_eq_mul, hee, mul_zero, Finset.sum_const_zero, add_zero, hrow, hcol,
      starRingEnd_apply] at h
    rw [Finset.sum_add_distrib]
    have e1 : ∑ c, star (β c a0) * x' c b = ∑ c, x' c b * star (β c a0) :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [e1]
    linear_combination h
  obtain ⟨hskew, hfact⟩ := hSk E r β x' Q v l hind hβQ hv hQβ hid

  have hfd : ∀ c b, S.hT (f c) (δ b) = (((nd * nQ) ^ 2 : ℕ) : E) * S.hT (f c) (lam b) := fun c b => by
    show S.hT (f c) (frame y2 b - frame y1 b) = _
    rw [hδeq b, map_smul, smul_eq_mul]
  have hac : ∀ c b, S.hT (a c) (frame y1 b) = ((nd * nQ : ℕ) : E) * S.hT (a' c) (frame y1 b) := fun c b => by
    rw [haa', LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_natCast, smul_eq_mul]
  let w : Matrix (Fin r) (Fin (r + 1)) E := fun c b =>
    ((nd * nQ : ℕ) : E) * ((nd : E) * S.hT (f c) (lam b)) + (nd : E) * S.hT (a' c) (frame y1 b) -
      ∑ d, ((nd ^ 2 * nQ : ℕ) : E) * s' c d * β d b
  have hw : ∀ c b, IntE (w c b) := by
    intro c b
    refine ((IntE.nat _).mul (hfint _ (hlam b) c)).add ((IntE.nat _).mul (hint _ (ha' c) _ (hy1 b))) |>.sub
      (IntE.sum _ _ fun d _ => ((IntE.nat _).mul (hs'int c d)).mul ?_)
    rw [← hβ1]
    exact hint _ (he d) _ (hy1 b)
  have hxw : ∀ c b, x' c b = (nQ : E) * w c b := by
    intro c b
    simp only [x', w, hfd, hac, hss']
    have hsum : ∑ x, (((nd * nQ) ^ 2 : ℕ) : E) * s' c x * β x b =
        (nQ : E) * ∑ d, ((nd ^ 2 * nQ : ℕ) : E) * s' c d * β d b := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      push_cast
      ring
    rw [hsum]
    push_cast
    ring
  have hSint : ∀ c d, ∃ o : 𝓞 E, (o : E) = (x' * Q) c d := by
    intro c d
    have : (x' * Q) c d = ∑ b, w c b * ((nQ : E) * Q b d) := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun b _ => by rw [hxw]; ring
    rw [this]
    exact IntE.sum _ _ fun b _ => (hw c b).mul (hQint b d)
  obtain ⟨n2, hn2, hn2act⟩ := hH E S r T Λ F 0 (x' * Q) hint he (fun _ => Λ.zero_mem) (by simp) hSint
    (by intro c d; simp [hskew c d])
  simp only [← he_def] at hn2act
  have hfin2 : ∀ b, n2 (n1 (frame y1 b)) = frame y2 b := by
    intro b
    rw [hn2act, heisFun, hk b]
    simp only [Pi.zero_apply, smul_zero, Finset.sum_const_zero, map_zero, LinearMap.zero_apply, zero_smul,
      add_zero, sub_zero, hrow]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    conv_rhs => rw [hfact]
    rw [Matrix.mul_apply]
  refine ⟨n2 * n1, PI.DCRelEquiv.UnitaryGroupMassFormula.nlam_mul hn2 hn1, 1, one_mem_NLam Λ y1, fun b => ?_, ?_⟩
  · simp [hfin2]
  · rw [hzt2, hzt1]
    simp [hfin2]

end Gen

end PI.TermsAtPtFiniteW
end
end

noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.Saturated

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem common_den (s : Finset E) : ∃ n : ℕ, 0 < n ∧ ∀ x ∈ s, IntE ((n : E) * x) := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := E) s
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, fun x hx => ?_⟩
  have hi : IsIntegral ℤ ((y : E) * x) := by simpa [zsmul_eq_mul] using h x hx
  have hn : ((y.natAbs : ℕ) : E) = (((y.natAbs : ℕ) : ℤ) : E) := (Int.cast_natCast _).symm
  rcases Int.natAbs_eq y with h' | h'
  · refine ⟨⟨_, hi⟩, ?_⟩
    show (y : E) * x = _
    rw [hn, ← h']
  · refine ⟨-⟨_, hi⟩, ?_⟩
    show -((y : E) * x) = _
    have h2 : ((y.natAbs : ℕ) : ℤ) = -y := by omega
    rw [hn, h2]
    push_cast
    ring

theorem gram_frame {T' : E} (F : LFlag S r T') (a b : Fin (r + 1)) :
    S.hT (frame F a) (frame F b) = if a = Fin.last r ∧ b = Fin.last r then -T' else 0 := by
  refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
  · simpa [frame, FlagG.fvec] using F.fl.z_norm
  · have h := F.fl.z_orth j
    have : S.hT F.fl.z (F.fl.e j) = 0 := by rw [← herm_star, h]; simp
    simpa [frame, FlagG.fvec, Fin.castSucc_ne_last] using this
  · simpa [frame, FlagG.fvec, Fin.castSucc_ne_last] using F.fl.z_orth i
  · simpa [frame, FlagG.fvec, Fin.castSucc_ne_last] using F.fl.e_iso i j

theorem mem_orth_Xplus {T : E} (F : LFlag S r T) (x : S.V) (he : ∀ a, S.hT (F.fl.e a) x = 0)
    (hz : S.hT F.fl.z x = 0) : x ∈ orth S (Xplus F) := by
  have hle : Xplus F ≤ LinearMap.ker (S.hT.flip x) := by
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨a, rfl⟩
      simp [he a]
    · intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      simp [hz]
  simp only [orth, Submodule.mem_iInf]
  intro w hw
  have := hle hw
  simpa using this

end Gen

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem zhat_cs (D : D7) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (c : Fin D.R.rS) (b : Fin (D.R.rS + 1)) :
    ZhatL (lf D F0) F' (Fin.castSucc c) b = (VS D).hT (F0.e c) (frame F' b) := by
  simp [ZhatL, Zhat, brS, frame, FlagG.fvec, lf]

theorem zhat_last (D : D7) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (b : Fin (D.R.rS + 1)) :
    ZhatL (lf D F0) F' (Fin.last D.R.rS) b = (VS D).hT F0.z (frame F' b) := by
  simp [ZhatL, Zhat, brS, frame, FlagG.fvec, lf]

theorem fixedZhat_of (hH : HeisOp) (hSk : SkewSolve) (hS : ShortFin) (hRD : RowsDep) (hRI : RightInv)
    (hFI : FInt) (hRF : ResFin) : FixedZhatFinite := by
  intro D u u' _hsig F0 Λ hΛ Z
  set Y := {y : Carrier (PD D Λ (lf D F0) u') | Gval (lf D F0) y.1 ≠ 0 ∧ ZhatL (lf D F0) y.1 = Z} with hY
  rcases Set.eq_empty_or_nonempty Y with hE | ⟨y0, hy0⟩
  · rw [hE, Set.image_empty]
    exact Set.finite_empty
  obtain ⟨f, L, hff, hef, hLp, hzL, hΛeq⟩ := split_row_iso D u F0 Λ hΛ
  obtain ⟨hnd, hfint⟩ := hFI D F0 Λ f L hff hef hLp hΛeq
  obtain ⟨θ, hθ⟩ := PI.UnitaryGroupMassFormula.IdCellInSW.traceOne_holds D
  obtain ⟨_, ⟨hlat, hU, hlift0, _⟩, hX0⟩ := hΛ
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ o : 𝓞 D.host.E, (o : D.host.E) = (VS D).hT x y :=
    fun x hx y hy => hT_int D Λ hU hx hy
  have he : ∀ c, F0.e c ∈ Λ := e_mem_of_XS D Λ (lf D F0) hX0
  have hz0 : F0.z ∈ Λ := hlift0.1
  let β : Matrix (Fin D.R.rS) (Fin (D.R.rS + 1)) D.host.E := fun c b => Z (Fin.castSucc c) b
  have hind : ∀ w : Fin D.R.rS → D.host.E, (∀ b, ∑ c, w c * β c b = 0) → w = 0 := by
    intro w hw
    by_contra hne
    obtain ⟨h1, h2⟩ := hRD D.host.E D.R.rS Z w hne hw
    apply hy0.1
    have hZ : Zhat F0 y0.1.fl = Z := hy0.2
    simp only [Gval, Gflag, Dl, lf, hZ, h1, h2]
    simp
  obtain ⟨Q, v, l, hβQ, hv, hQβ⟩ := hRI D.host.E D.R.rS β hind
  obtain ⟨nQ, hnQ, hQint⟩ := common_den (Finset.univ.image (fun p : Fin (D.R.rS + 1) × Fin D.R.rS => Q p.1 p.2))
  obtain ⟨nv, hnv, hvint⟩ := common_den (Finset.univ.image v)
  have hQint' : ∀ b c, IntE ((nQ : D.host.E) * Q b c) := fun b c =>
    hQint _ (Finset.mem_image.2 ⟨(b, c), Finset.mem_univ _, rfl⟩)
  have hvint' : ∀ b, IntE ((nv : D.host.E) * v b) := fun b => hvint _ (Finset.mem_image.2 ⟨b, Finset.mem_univ _, rfl⟩)
  obtain ⟨R, hRfin, ρ, hρ⟩ := hRF D.host.E (VS D).V Λ hlat.fg ((ndS D * nQ) ^ 2) (by positivity)
  set nd := ndS D with hnd_def
  have hfe : ∀ a b, (VS D).hT (f a) (F0.e b) = if a = b then 1 else 0 := fun a b => by
    rw [← herm_star, hef b a]
    by_cases h : b = a
    · subst h; simp
    · simp [h, Ne.symm h]
  have hze : ∀ c, (VS D).hT F0.z (F0.e c) = 0 := fun c => by rw [← herm_star, F0.z_orth c]; simp
  have hfz : ∀ c, (VS D).hT (f c) F0.z = 0 := fun c => (hLp F0.z hzL c).2
  have hmemE : ∀ (x : D.host.E) (w : (VS D).V), IntE x → w ∈ Λ → x • w ∈ Λ := by
    rintro x w ⟨o, rfl⟩ hw
    show (algebraMap (𝓞 D.host.E) D.host.E o) • w ∈ Λ
    rw [algebraMap_smul]
    exact Λ.smul_mem o hw
  have hnat : ∀ (k : ℕ) (w : (VS D).V), w ∈ Λ → (k : D.host.E) • w ∈ Λ :=
    fun k w hw => hmemE _ w (IntE.nat k) hw
  have hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0 := by
    have := (D.mem u).A.T_prime.pos
    exact_mod_cast this.ne'

  let yv : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E) → (VS D).V := fun y => ∑ b, v b • frame y b
  let ι2 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E) → (VS D).V :=
    fun y => ((nd * nv : ℕ) : D.host.E) • piL F0.e f (yv y)
  let hz : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E) → D.host.E := fun y => (VS D).hT F0.z (ι2 y)
  let xf : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E) → (VS D).V :=
    fun y => ((Tu D u : ℕ) : D.host.E) • ι2 y + hz y • F0.z

  have hβy : ∀ y ∈ Y, ∀ c b, (VS D).hT (F0.e c) (frame y.1 b) = β c b := by
    intro y hy c b
    rw [← zhat_cs D F0 y.1 c b, hy.2]
  have hzy : ∀ y ∈ Y, ∀ b, (VS D).hT F0.z (frame y.1 b) = Z (Fin.last D.R.rS) b := by
    intro y hy b
    rw [← zhat_last D F0 y.1 b, hy.2]
  have hyΛ : ∀ y : Carrier (PD D Λ (lf D F0) u'), ∀ b, frame y.1 b ∈ Λ := by
    intro y b
    obtain ⟨hlift, _, _, hX⟩ := y.2
    exact frame_mem D Λ y.1 hX hlift.1 b
  have hyve : ∀ y ∈ Y, ∀ c, (VS D).hT (F0.e c) (yv y.1) = 0 := by
    intro y hy c
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [yv, map_sum, map_smul, smul_eq_mul, hβy y hy]
    rw [← hv c]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  have hpie : ∀ c x, (VS D).hT (F0.e c) (piL F0.e f x) = (VS D).hT (F0.e c) x := fun c x => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [piL_apply, map_sub, map_sum, F0.e_iso]
  have hpif : ∀ c x, (VS D).hT (f c) (piL F0.e f x) = 0 := fun c x => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [piL_apply, map_sub, map_sum, hfe]
  have hpiz : ∀ x, (VS D).hT F0.z (piL F0.e f x) = (VS D).hT F0.z x := fun x => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [piL_apply, map_sub, map_sum, hze]
  have hι2 : ∀ y : Carrier (PD D Λ (lf D F0) u'), ι2 y.1 ∈ Λ := by
    intro y
    let lam : (VS D).V := ∑ b, ((nv : D.host.E) * v b) • frame y.1 b
    have hlam : lam ∈ Λ := Λ.sum_mem fun b _ => hmemE _ _ (hvint' b) (hyΛ y b)
    have : ι2 y.1 = (nd : D.host.E) • lam - ∑ c, ((nd : D.host.E) * (VS D).hT (f c) lam) • F0.e c := by
      have h1 : (nv : D.host.E) • yv y.1 = lam := by
        simp only [yv, lam, Finset.smul_sum, smul_smul]
      have h2 : ι2 y.1 = (nd : D.host.E) • piL F0.e f lam := by
        simp only [ι2]
        rw [← h1, map_smul, smul_smul]
        push_cast
        ring_nf
      rw [h2, piL_apply, smul_sub]
      congr 1
      rw [Finset.smul_sum]
      simp only [smul_smul]
    rw [this]
    exact Λ.sub_mem (hnat nd _ hlam) (Λ.sum_mem fun c _ => hmemE _ _ (hfint _ hlam c) (he c))
  have hhz : ∀ y ∈ Y, hz y.1 = ((nd * nv : ℕ) : D.host.E) * ∑ b, v b * Z (Fin.last D.R.rS) b := by
    intro y hy
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hz, ι2, map_smul, smul_eq_mul, hpiz, yv, map_sum, hzy y hy]

  have hyvn : ∀ y : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E),
      (VS D).hT (yv y) (yv y) = (VS D).hT (yv y0.1) (yv y0.1) := by
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [yv, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, gram_frame]
  have hpin : ∀ y ∈ Y, (VS D).hT (piL F0.e f (yv y.1)) (piL F0.e f (yv y.1)) = (VS D).hT (yv y.1) (yv y.1) := by
    intro y hy
    have h1 : ∀ c, (VS D).hT (yv y.1) (F0.e c) = 0 := fun c => by rw [← herm_star, hyve y hy c]; simp
    set_option synthInstance.maxHeartbeats 100000 in
      simp [piL_apply, map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
      hyve y hy, h1, F0.e_iso]
  set hzc : D.host.E := ((nd * nv : ℕ) : D.host.E) * ∑ b, v b * Z (Fin.last D.R.rS) b with hzc_def
  set K : D.host.E := ((Tu D u : ℕ) : D.host.E) ^ 2 * ((((nd * nv : ℕ) : D.host.E)) ^ 2 *
      (VS D).hT (yv y0.1) (yv y0.1)) + ((Tu D u : ℕ) : D.host.E) * hzc * star hzc with hK_def
  have hxK : ∀ y ∈ Y, (VS D).hT (xf y.1) (xf y.1) = K := by
    intro y hy
    have hιz : (VS D).hT (ι2 y.1) F0.z = star (hz y.1) := by rw [← herm_star]
    have hιι : (VS D).hT (ι2 y.1) (ι2 y.1) = (((nd * nv : ℕ) : D.host.E)) ^ 2 * (VS D).hT (yv y0.1) (yv y0.1) := by
      simp only [ι2, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply,
        star_natCast, hpin y hy, hyvn]
      ring
    have hzz : (VS D).hT F0.z F0.z = -((Tu D u : ℕ) : D.host.E) := F0.z_norm
    simp only [xf, map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, starRingEnd_apply, star_natCast, hιz, hιι, hzz]
    have hh : hz y.1 = hzc := hhz y hy
    rw [show (VS D).hT F0.z (ι2 y.1) = hz y.1 from rfl, hh]
    simp only [hK_def]
    ring

  let P : Submodule D.host.E (VS D).V :=
    orth (VS D) (Xplus (lf D F0)) ⊓ ⨅ c, LinearMap.ker ((VS D).hT (f c))
  have hpos : ∀ x ∈ P, x ≠ 0 → ∀ τ : D.host.E →+* ℂ, 0 < (τ ((VS D).hT x x)).re := by
    intro x hx hne τ
    obtain ⟨hxo, hxf⟩ := Submodule.mem_inf.1 hx
    refine PI.UnitaryGroupMassFormula.BetaModX.positive_weight_holds D (Tu D u) (lf D F0) τ x (D.mem u).A.T_prime.pos hxo ?_
    intro hxX
    obtain ⟨t, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hxX
    apply hne
    have ht : ∀ c, t c = 0 := by
      intro c
      have := LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hxf c)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, hfe] using this
    simp [ht]
  have hxP : ∀ y ∈ Y, xf y.1 ∈ P := by
    intro y hy
    refine Submodule.mem_inf.2 ⟨mem_orth_Xplus (lf D F0) _ (fun a => ?_) ?_, (Submodule.mem_iInf _).2 fun c => ?_⟩
    · show (VS D).hT (F0.e a) (xf y.1) = 0
      simp [xf, ι2, map_add (f := _), map_smul, hpie, hyve y hy, F0.z_orth]
    · show (VS D).hT F0.z (xf y.1) = 0
      simp only [xf, map_add (f := _), map_smul, smul_eq_mul, F0.z_norm]
      change ((Tu D u : ℕ) : D.host.E) * hz y.1 + hz y.1 * -((Tu D u : ℕ) : D.host.E) = 0
      ring
    · rw [LinearMap.mem_ker]
      simp [xf, ι2, map_add (f := _), map_smul, hpif, hfz]
  have hxΛ : ∀ y : Carrier (PD D Λ (lf D F0) u'), xf y.1 ∈ Λ := fun y =>
    Λ.add_mem (hnat _ _ (hι2 y)) (hmemE _ _ (hint _ hz0 _ (hι2 y)) hz0)

  haveI := hRfin
  let κ : Carrier (PD D Λ (lf D F0) u') → (VS D).V × (Fin (D.R.rS + 1) → R) :=
    fun y => (xf y.1, fun b => ρ (frame y.1 b))
  have hfinX := hS D.host.E (VS D) Λ hlat P hpos K
  have hκ : κ '' Y ⊆ {x | x ∈ Λ ∧ x ∈ P ∧ (VS D).hT x x = K} ×ˢ Set.univ := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨hxΛ y, hxP y hy, hxK y hy⟩, trivial⟩
  have hκfin : (κ '' Y).Finite := (hfinX.prod Set.finite_univ).subset hκ
  have hzt : ∀ y : Carrier (PD D Λ (lf D F0) u'), y.1.zt = frame y.1 (Fin.last D.R.rS) := by
    intro y
    rw [y.2.1.2]
    simp [frame, FlagG.fvec]
  have hrel : ∀ y1 ∈ Y, ∀ y2 ∈ Y, κ y1 = κ y2 →
      mk Λ (lf D F0) (PD D Λ (lf D F0) u') y1 = mk Λ (lf D F0) (PD D Λ (lf D F0) u') y2 := by
    intro y1 hy1 y2 hy2 hκ12
    have hx : xf y1.1 = xf y2.1 := congrArg Prod.fst hκ12
    have hr : ∀ b, ρ (frame y1.1 b) = ρ (frame y2.1 b) := fun b => congrFun (congrArg Prod.snd hκ12) b
    have hδ : ∀ b, ∃ lam ∈ Λ, frame y2.1 b - frame y1.1 b = (((nd * nQ) ^ 2 : ℕ) : D.host.E) • lam :=
      fun b => hρ _ (hyΛ y1 b) _ (hyΛ y2 b) (hr b)
    have hι : piL F0.e f (∑ b, v b • frame y1.1 b) = piL F0.e f (∑ b, v b • frame y2.1 b) := by
      have h1 : ((Tu D u : ℕ) : D.host.E) • ι2 y1.1 = ((Tu D u : ℕ) : D.host.E) • ι2 y2.1 := by
        have := hx
        simp only [xf] at this
        rw [show hz y1.1 = hzc from hhz y1 hy1, show hz y2.1 = hzc from hhz y2 hy2] at this
        exact add_right_cancel this
      have h2 := smul_right_injective (VS D).V hT0 h1
      have hne : ((nd * nv : ℕ) : D.host.E) ≠ 0 := by
        have : 0 < nd * nv := Nat.mul_pos hnd hnv
        exact_mod_cast this.ne'
      exact smul_right_injective (VS D).V hne h2
    exact Quot.sound (related_gen hH hSk Λ (lf D F0) f hint he hef θ hθ nd nQ hfint β Q v l hind hβQ hv hQβ
      hQint' y1.1 y2.1 (hzt y1) (hzt y2) (hyΛ y1) (hβy y1 hy1) (hβy y2 hy2)
      (fun a b => by rw [gram_frame, gram_frame]) hδ hι)
  let g : (VS D).V × (Fin (D.R.rS + 1) → R) → TermQ Λ (lf D F0) (PD D Λ (lf D F0) u') := fun t =>
    if h : ∃ y ∈ Y, κ y = t then mk Λ (lf D F0) (PD D Λ (lf D F0) u') (Classical.choose h)
    else mk Λ (lf D F0) (PD D Λ (lf D F0) u') y0
  refine (hκfin.image g).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨κ y, ⟨y, hy, rfl⟩, ?_⟩
  have h : ∃ y' ∈ Y, κ y' = κ y := ⟨y, hy, rfl⟩
  simp only [g, dif_pos h]
  obtain ⟨hy', hκ'⟩ := Classical.choose_spec h
  exact hrel _ hy' _ hy hκ'

end D7

end PI.TermsAtPtFiniteW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.DdSPowLeOne
noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.Saturated

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ndS_mul_int (D : D7) (a : Fin D.R.rS) (t : D.host.E) (ht : t ∈ aaS D a) :
    ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * t := by
  have ha := a.isLt
  obtain ⟨m, hm⟩ : ∃ m : ℕ, D.R.rS = (a : ℕ) + m := ⟨D.R.rS - (a : ℕ), by omega⟩
  have haa : aaS D a = (((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ^ m : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ := by
    unfold aaS ddS
    rw [FractionalIdeal.coeIdeal_pow, ← zpow_natCast, ← zpow_neg]
    congr 1
    omega
  rw [haa] at ht
  by_cases hJ : (((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ^ m : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = 0
  · rw [hJ] at ht
    have ht0 : t = 0 := by
      first
        | (rw [FractionalIdeal.inv_zero', FractionalIdeal.mem_zero_iff] at ht; exact ht)
        | (rw [inv_zero, FractionalIdeal.mem_zero_iff] at ht; exact ht)
        | simpa using ht
    exact ⟨0, by rw [ht0, map_zero, mul_zero]⟩
  · rw [FractionalIdeal.inv_eq] at ht
    first
      | rw [FractionalIdeal.mem_div_iff_of_ne_zero hJ] at ht
      | rw [FractionalIdeal.mem_div_iff_of_nonzero hJ] at ht
    have hN : ((Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : (𝓞 D.host.E)) ^ m) ∈ ((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ^ m : Ideal (𝓞 D.host.E)) :=
      Ideal.pow_mem_pow (Ideal.absNorm_mem _) m
    have hy : algebraMap (𝓞 D.host.E) D.host.E ((Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : (𝓞 D.host.E)) ^ m) ∈
        (((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ^ m : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :=
      by
        first
          | exact FractionalIdeal.mem_coeIdeal_of_mem _ hN
          | exact FractionalIdeal.mem_coeIdeal_of_mem hN
          | exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨_, hN, rfl⟩
    have h1 := ht _ hy
    rw [FractionalIdeal.mem_one_iff] at h1
    obtain ⟨o', ho'⟩ := h1
    refine ⟨(Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : (𝓞 D.host.E)) ^ (a : ℕ) * o', ?_⟩
    have hsplit : (Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : D.host.E) ^ D.R.rS =
        (Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : D.host.E) ^ (a : ℕ) * (Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : D.host.E) ^ m := by
      rw [← pow_add, ← hm]
    rw [map_mul, ho']
    simp only [ndS, map_pow, map_natCast, Nat.cast_pow, hsplit]
    ring

theorem fInt_holds : FInt := by
  intro D T F0 Λ f L hff hef hL hΛ
  refine ⟨?_, ?_⟩
  ·
    have hd : differentIdeal ℤ (𝓞 D.host.F) ≠ ⊥ := by
      first
        | exact differentIdeal_ne_bot
        | exact differentIdeal_ne_bot (K := ℚ) (L := D.host.F)
        | exact differentIdeal_ne_bot ℤ ℚ D.host.F (𝓞 D.host.F)
    have hinj : Function.Injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
      first
        | exact FaithfulSMul.algebraMap_injective _ _
        | exact NoZeroSMulDivisors.algebraMap_injective _ _
        | (have h1 : Function.Injective (algebraMap (𝓞 D.host.F) D.host.E) := by
             rw [IsScalarTower.algebraMap_eq (𝓞 D.host.F) D.host.F D.host.E, RingHom.coe_comp]
             exact (algebraMap D.host.F D.host.E).injective.comp (IsFractionRing.injective _ _)
           rw [IsScalarTower.algebraMap_eq (𝓞 D.host.F) (𝓞 D.host.E) D.host.E, RingHom.coe_comp] at h1
           exact h1.of_comp)
    have hmap : (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ≠ ⊥ := by
      rwa [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
    have hN : Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ≠ 0 := by
      rwa [Ne, Ideal.absNorm_eq_zero_iff]
    unfold ndS
    exact pow_pos (Nat.pos_of_ne_zero hN) _
  · intro x hx c

    have hec : ∀ a, (VS D).hT (f c) (F0.e a) = if a = c then 1 else 0 := by
      intro a
      have hs : starRingEnd D.host.E ((VS D).hT (F0.e a) (f c)) = (VS D).hT (f c) (F0.e a) := by
        first
          | exact (VS D).herm.eq _ _
          | exact (VS D).herm _ _
      rw [← hs, hef]
      split_ifs <;> simp
    let P : Submodule (𝓞 D.host.E) (VS D).V :=
      { carrier := {y | ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (y)}
        add_mem' := by
          rintro y z ⟨o1, h1⟩ ⟨o2, h2⟩
          exact (show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (y + z) from ⟨o1 + o2, by rw [map_add (f := _), map_add (f := _), mul_add, h1, h2]⟩)
        zero_mem' := by
          exact (show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (0) from ⟨0, by rw [map_zero, map_zero, mul_zero]⟩)
        smul_mem' := by
          rintro r y ⟨o, h⟩
          refine (show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (r • y) from ⟨r * o, ?_⟩)
          rw [← algebraMap_smul D.host.E r y, map_smul, smul_eq_mul, map_mul, h]
          ring }
    have hP : Λ ≤ P := by
      rw [hΛ]
      refine sup_le (sup_le ?_ ?_) ?_
      · unfold latSpan
        rw [Submodule.span_le]
        rintro y ⟨a, t, ht, rfl⟩
        show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (t • F0.e a)
        rw [map_smul, smul_eq_mul, hec a]
        by_cases hac : a = c
        · subst hac
          obtain ⟨o, ho⟩ := ndS_mul_int D a t ht
          exact ⟨o, by rw [ho, if_pos rfl, mul_one]⟩
        · exact ⟨0, by rw [if_neg hac, mul_zero, mul_zero, map_zero]⟩
      · intro y hy
        show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (y)
        exact ⟨0, by rw [(hL y hy c).2, mul_zero, map_zero]⟩
      · unfold latSpan
        rw [Submodule.span_le]
        rintro y ⟨a, t, ht, rfl⟩
        show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (t • f a)
        exact ⟨0, by rw [map_smul, smul_eq_mul, hff c a, mul_zero, mul_zero, map_zero]⟩
    obtain ⟨o, ho⟩ := hP hx
    exact ⟨o, ho⟩

end PI.TermsAtPtFiniteW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.RightInvHolds
noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open Formalism.MainNotions.S Matrix

theorem rowsDep_holds : RowsDep := by
  intro E _ r Z u hu hdep
  have hcast : ∀ (h : r ≤ r + 1) (c : Fin r), Fin.castLE h c = Fin.castSucc c := fun h c => Fin.ext rfl
  have hcast1 : ∀ (h : r + 1 ≤ r + 1) (c : Fin (r + 1)), Fin.castLE h c = c := fun h c => Fin.ext rfl
  constructor
  · unfold leadMinorE
    rw [dite_eq_left le_rfl, ← Matrix.exists_vecMul_eq_zero_iff]
    refine ⟨Fin.snoc (α := fun _ => E) u 0, ?_, ?_⟩
    · intro h0
      apply hu
      funext c
      have h1 := congrFun h0 (Fin.castSucc c)
      simpa using h1
    · funext b
      simp only [Matrix.vecMul, dotProduct, Matrix.submatrix_apply, hcast1, Pi.zero_apply]
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, zero_mul, add_zero]
      exact hdep b
  · unfold leadMinorE
    rw [dite_eq_left (Nat.le_succ r), ← Matrix.exists_vecMul_eq_zero_iff]
    refine ⟨u, hu, ?_⟩
    funext b
    simp only [Matrix.vecMul, dotProduct, Matrix.submatrix_apply, hcast, Pi.zero_apply]
    exact hdep (Fin.castSucc b)

theorem rightInv_holds : RightInv := by
  intro E _ r β hind
  have hinjT : Function.Injective (Matrix.mulVecLin βᵀ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    apply hind u
    intro b
    have h1 := congrFun hu b
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_transpose] at h1
    exact h1
  have hrank : β.rank = r := by
    rw [← Matrix.rank_transpose, Matrix.rank, LinearMap.finrank_range_of_inj hinjT]
    simp
  have hsurj : Function.Surjective (Matrix.mulVecLin β) := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    show β.rank = _
    rw [hrank]
    simp
  have hker : Module.finrank E (LinearMap.ker (Matrix.mulVecLin β)) = 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin β)
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at h1
    simp at h1
    omega
  obtain ⟨v0, hv0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 (by omega : 0 < Module.finrank E (LinearMap.ker (Matrix.mulVecLin β)))
  have hspan := (finrank_eq_one_iff_of_nonzero' v0 hv0).1 hker
  set vv : Fin (r + 1) → E := (v0 : Fin (r + 1) → E) with hvv
  have hvv0 : vv ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hfv : β *ᵥ vv = 0 := v0.2
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hvv0
  have hj' : vv j ≠ 0 := hj
  choose x hx using fun c : Fin r => hsurj (Pi.single c 1)
  set x' : Fin r → Fin (r + 1) → E := fun c => x c - ((vv j)⁻¹ * x c j) • vv with hx'
  have hx'f : ∀ c, β *ᵥ x' c = Pi.single c 1 := by
    intro c
    have h1 : β *ᵥ x c = Pi.single c 1 := hx c
    simp only [hx', Matrix.mulVec_sub, Matrix.mulVec_smul, hfv, smul_zero, sub_zero, h1]
  have hx'j : ∀ c, x' c j = 0 := by
    intro c
    simp only [hx', Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have h2 : (vv j)⁻¹ * x c j * vv j = x c j := by
      rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hj', one_mul]
    rw [h2, sub_self]
  refine ⟨Matrix.of (fun b c => x' c b), vv, fun k => if k = j then (vv j)⁻¹ else 0, ?_, ?_, ?_⟩
  · ext a c
    have h1 := congrFun (hx'f c) a
    have h2 : ∑ b, β a b * x' c b = (Pi.single c (1 : E) : Fin r → E) a := by
      rw [← h1]
      rfl
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply]
    rw [h2, Pi.single_apply]
  · intro c
    have h1 := congrFun hfv c
    simpa [Matrix.mulVec, dotProduct] using h1
  · intro i k
    set y : Fin (r + 1) → E := ∑ c, β c k • x' c with hy
    have hQ : (Matrix.of (fun b c => x' c b) * β) i k = y i := by
      simp [Matrix.mul_apply, hy, Finset.sum_apply, mul_comm]
    have hyf : β *ᵥ y = β *ᵥ Pi.single k 1 := by
      funext a
      simp only [hy, Matrix.mulVec_sum, Matrix.mulVec_smul, hx'f]
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]
    have hyj : y j = 0 := by
      simp [hy, Finset.sum_apply, hx'j]
    have hmem : Pi.single k 1 - y ∈ LinearMap.ker (Matrix.mulVecLin β) := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, hyf, sub_self]
    obtain ⟨t, ht⟩ := hspan ⟨_, hmem⟩
    have ht' : t • vv = Pi.single k 1 - y := congrArg Subtype.val ht
    have htj := congrFun ht' j
    have hti := congrFun ht' i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, hyj, sub_zero, Pi.single_apply] at htj hti
    show (Matrix.of (fun b c => x' c b) * β) i k = _
    rw [hQ]
    by_cases hkj : k = j
    · subst hkj
      simp only [if_true] at htj
      have htv : t = (vv k)⁻¹ := by
        field_simp
        linear_combination htj
      simp only [if_true]
      rw [htv] at hti
      linear_combination hti
    · have hjk : j ≠ k := fun h => hkj h.symm
      simp only [if_neg hjk] at htj
      have ht0 : t = 0 := by
        rcases mul_eq_zero.1 htj with h | h
        · exact h
        · exact absurd h hj
      simp only [if_neg hkj, mul_zero, sub_zero]
      rw [ht0, zero_mul] at hti
      linear_combination hti

end PI.TermsAtPtFiniteW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.SkewSolveAlt
noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open Formalism.MainNotions.S Matrix

theorem skewSolve_holds : SkewSolve := by
  intro E _ _ r β x Q v l hind hβQ hβv hQβ hskew
  have hS : βᴴ * x + xᴴ * β = 0 := by
    ext a b
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.zero_apply,
      ← Finset.sum_add_distrib]
    exact hskew a b
  have h1 : x * Q + (x * Q)ᴴ = 0 := by
    have h0 := congrArg (fun M => Qᴴ * M * Q) hS
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_zero, Matrix.zero_mul] at h0
    have e1 : Qᴴ * (βᴴ * x) * Q = x * Q := by
      rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hβQ, Matrix.conjTranspose_one, Matrix.one_mul]
    have e2 : Qᴴ * (xᴴ * β) * Q = (x * Q)ᴴ := by
      rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_assoc, hβQ, Matrix.mul_one]
    rw [e1, e2] at h0
    exact h0
  have hβv' : β *ᵥ v = 0 := by
    funext c
    exact hβv c
  have hw : βᴴ *ᵥ (x *ᵥ v) = 0 := by
    have h0 := congrArg (fun M => M *ᵥ v) hS
    simp only [Matrix.add_mulVec, Matrix.zero_mulVec, ← Matrix.mulVec_mulVec, hβv', Matrix.mulVec_zero,
      add_zero] at h0
    exact h0
  have hxv : x *ᵥ v = 0 := by
    have hu := hind (fun c => star ((x *ᵥ v) c)) (fun b => by
      have hb := congrFun hw b
      have h2 : ∑ c, star ((x *ᵥ v) c) * β c b = star ((βᴴ *ᵥ (x *ᵥ v)) b) := by
        show _ = star (∑ c, βᴴ b c * (x *ᵥ v) c)
        simp only [Matrix.conjTranspose_apply, star_sum, star_mul', star_star]
        exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
      rw [h2, hb]
      simp)
    funext c
    have hc := congrFun hu c
    simpa using hc
  refine ⟨fun c d => ?_, ?_⟩
  · have hcd := congrFun (congrFun h1 c) d
    simpa only [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.zero_apply] using hcd
  · rw [Matrix.mul_assoc]
    ext i j
    rw [Matrix.mul_apply]
    simp only [hQβ, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    have hi := congrFun hxv i
    have h' : ∑ k, x i k * (v k * l j) = (x *ᵥ v) i * l j := by
      show _ = (∑ k, x i k * v k) * l j
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [h', hi]
    simp

end PI.TermsAtPtFiniteW
end
end

noncomputable section

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem termsAtFinite_of_frameOp_shortFin (hF : FrameOp) (hS : ShortFin) (D : D7) (u u' : D.what₂.Word) :
    TermsAtFinite D u u' :=
  termsAtFinite_of (zhatReduce_of cellReduce_holds hF carrierRow_holds zhatIntegral_holds)
    (fixedZhat_of heisOp_holds skewSolve_holds hS rowsDep_holds rightInv_holds fInt_holds resFin_holds) D u u'

end PI.TermsAtPtFiniteW
