module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsDegLocExact
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

def DegLocExact.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (N : ℕ) (M' M M'' : Type v)
    [AddCommGroup M'] [Module (Poly S N) M'] [Module S M'] [IsScalarTower S (Poly S N) M']
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    [AddCommGroup M''] [Module (Poly S N) M''] [Module S M''] [IsScalarTower S (Poly S N) M'']
    (𝓜' : GradedPMod S N M') (𝓜 : GradedPMod S N M) (𝓜'' : GradedPMod S N M'')
    (f : GradedHom 𝓜' 𝓜) (g : GradedHom 𝓜 𝓜''),
    Function.Injective f.toLin → Function.Surjective g.toLin → Function.Exact f.toLin g.toLin →
    ∀ (c : ℤ) (I : StdCell N),
      (∀ z ∈ degLoc 𝓜 c I, locMap g.toLin I.1 z = 0 →
        ∃ z' ∈ degLoc 𝓜' c I, locMap f.toLin I.1 z' = z) ∧
      (∀ z'' ∈ degLoc 𝓜'' c I, ∃ z ∈ degLoc 𝓜 c I, locMap g.toLin I.1 z = z'')

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGeneratedAmple
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

theorem GeneratedAmple.proof (hCover : AmpleCover.Statement.{u, w})
    (hLocal : AmpleTwistLocal.Statement.{u, w}) : GeneratedAmple.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x H A Q
  choose n₀ hn₀ using fun (b : Fin A.m) (j : Fin (A.r + 1)) => hLocal S Ω N x H A Q b j
  let M : ℕ := Finset.univ.sup fun p : Fin A.m × Fin (A.r + 1) => n₀ p.1 p.2
  refine ⟨A.m * M, fun c hc => hCover S Ω N x H A _ fun j I y hy => ?_⟩
  have hm := A.m_pos
  have hc' : c % A.m + A.m * (c / A.m) = c := Nat.mod_add_div c A.m
  have hM : M ≤ c / A.m := (Nat.le_div_iff_mul_le hm).mpr (by rw [mul_comm]; exact hc)
  have hn : n₀ ⟨c % A.m, Nat.mod_lt c hm⟩ j ≤ c / A.m :=
    le_trans (Finset.le_sup (f := fun p : Fin A.m × Fin (A.r + 1) => n₀ p.1 p.2)
      (Finset.mem_univ (⟨c % A.m, Nat.mod_lt c hm⟩, j))) hM
  have key := hn₀ ⟨c % A.m, Nat.mod_lt c hm⟩ j (c / A.m) hn I y
  simp only [hc'] at key
  exact key hy

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem AmpleCover.sub_twist (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = F.sub I * Q.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  change Submodule.span _ _ = _
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_mul, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨q, hq, y, hy, rfl⟩; exact ⟨y, hy, q, hq, mul_comm _ _⟩
  · rintro ⟨y, hy, q, hq, rfl⟩; exact ⟨q, hq, y, hy, mul_comm _ _⟩

theorem AmpleCover.sub_pow (Q : SubSystem S x Ω) (n : ℕ) (I : Chart x) :
    (Q.pow n).sub I = Q.sub I ^ n := by
  induction n with
  | zero =>
    obtain ⟨i, hi⟩ := I.2.1
    rw [pow_zero]
    change twistMod S x 0 I = 1
    rw [twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]
  | succ n ih =>
    change ((Q.pow n).twist Q).sub I = _
    rw [AmpleCover.sub_twist, ih, pow_succ]

theorem AmpleCover.proof : AmpleCover.Statement.{u, w} := by
  intro S _ Ω _ _ N x H A F hF I
  set R := chartRing S x I
  set G : Submodule R Ω := Submodule.span R (F.secs : Set Ω)
  set P : Submodule R Ω := H.sub I
  refine le_antisymm (Submodule.span_le.mpr fun z hz => ?_) fun y hy => ?_
  · exact (Submodule.mem_iInf _).mp hz I
  obtain ⟨Q', hQ'⟩ := H.invertible I
  have hpow : ∀ n, (H.pow n).sub I = P ^ n := fun n => AmpleCover.sub_pow H.toSubSystem n I
  have hone : ∀ n, P ^ n * Q' ^ n = 1 := fun n => by rw [← mul_pow, hQ', one_pow]

  set c : Ideal R := G.comap (LinearMap.toSpanSingleton R Ω y)
  set V : Submodule R Ω := Submodule.map (Algebra.linearMap R Ω) c.radical
  have hkey : P ^ A.m * Q' ^ A.m ≤ V := by
    rw [← hpow, ← A.generates I, Submodule.mul_le]
    intro u hu w hw
    have hmem : ∀ j, A.h j * w ∈ V := by
      intro j
      have h1 : A.h j * w ∈ (1 : Submodule R Ω) := by
        rw [← hone A.m, ← hpow]
        exact Submodule.mul_mem_mul (by rw [← A.generates I]; exact Submodule.subset_span ⟨j, rfl⟩) hw
      obtain ⟨a, ha⟩ := Submodule.mem_one.mp h1
      obtain ⟨e, he⟩ := hF j I y hy
      refine ⟨a, ⟨e, ?_⟩, ha⟩
      change a ^ e • y ∈ G
      have hw' : w ^ e ∈ Q' ^ (A.m * e) := by
        rw [pow_mul]; exact Submodule.pow_mem_pow _ hw e
      have h2 : (y * A.h j ^ e) * w ^ e ∈ G * P ^ (A.m * e) * Q' ^ (A.m * e) :=
        Submodule.mul_mem_mul (by rw [← hpow]; exact he) hw'
      rw [mul_assoc, hone, mul_one] at h2
      rw [Algebra.smul_def, map_pow]
      change ((a : Ω)) ^ e * y ∈ G
      have : (a : Ω) = A.h j * w := ha
      rw [this]
      convert h2 using 1
      ring
    refine Submodule.span_induction (p := fun u _ => u * w ∈ V) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨j, rfl⟩; exact hmem j
    · rw [zero_mul]; exact V.zero_mem
    · intro a b _ _ ha hb; rw [add_mul]; exact V.add_mem ha hb
    · intro r a _ ha; rw [smul_mul_assoc]; exact V.smul_mem r ha
  obtain ⟨b, ⟨n, hn⟩, hb⟩ := hkey (by rw [hone]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩)
  have hb1 : (b : Ω) = 1 := hb
  have hbn : b ^ n • y ∈ G := hn
  rwa [Algebra.smul_def, map_pow, show algebraMap R Ω b = 1 from hb1, one_pow, one_mul] at hbn

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGenerated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem Generated.proof (hE : Extension.Statement.{u, w, w}) : Generated.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x Q
  obtain ⟨M, hMgam, hMtilde⟩ := hE S Ω N x Ω Q.toSubFamily Q.fg
  obtain ⟨n, deg, gen, hgen, hM⟩ := M.fg
  refine ⟨∑ j, |deg j|, fun c hc I => le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    intro z hz
    exact (Submodule.mem_iInf _).mp hz I
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  set T := Submodule.span (chartRing S x I) ((Q.twist (twistSys S x c)).secs : Set Ω) with hT

  have hgenT : ∀ (j : Fin n) (f s : Poly S N) (e e' : ℕ), s ∈ monos I.1 → f.IsHomogeneous e' →
      s.IsHomogeneous e → (e' : ℤ) + deg j = e →
      x i ^ c * ((aeval x s)⁻¹ * (aeval x f * gen j)) ∈ T := by
    intro j f s e e' hs hf hse hee
    have hd : deg j ≤ c := (le_abs_self (deg j)).trans
      ((Finset.single_le_sum (fun j _ => abs_nonneg (deg j)) (Finset.mem_univ j)).trans hc)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = c - deg j := ⟨(c - deg j).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hsec : x i ^ k * gen j ∈ (Q.twist (twistSys S x c)).secs := by
      have h1 := M.smul_mem k (deg j) (X i ^ k) (gen j) (isHomogeneous_X_pow i k) (hgen j)
      have h2 : deg j + (k : ℤ) = c := by omega
      rw [h2] at h1
      have h3 := hMgam c h1
      rwa [map_pow, aeval_X, smul_eq_mul] at h3
    have hα : aeval x f / aeval x s ∈ twistMod S x (-deg j) I :=
      Submodule.subset_span ⟨f, s, e, e', hs, hf, hse, by omega, rfl⟩
    rw [twistMod_eq_span (-deg j) I hi, Submodule.mem_span_singleton] at hα
    obtain ⟨b, hb⟩ := hα
    rw [chartRing_smul_def] at hb
    have e1 : x i ^ c * x i ^ (-deg j) = x i ^ k := by
      rw [← zpow_add₀ hxi, ← zpow_natCast, hk]
      congr 1
    have e2 : x i ^ c * ((aeval x s)⁻¹ * (aeval x f * gen j)) = b • (x i ^ k * gen j) := by
      rw [chartRing_smul_def, ← e1]
      calc x i ^ c * ((aeval x s)⁻¹ * (aeval x f * gen j))
          = x i ^ c * (aeval x f / aeval x s) * gen j := by ring
        _ = x i ^ c * ((b : Ω) * x i ^ (-deg j)) * gen j := by rw [hb]
        _ = (b : Ω) * (x i ^ c * x i ^ (-deg j) * gen j) := by ring
    rw [e2]
    exact T.smul_mem b (Submodule.subset_span hsec)

  have key : ∀ y ∈ M.tilde 0 I, x i ^ c * y ∈ T := by
    intro y hy
    refine Submodule.span_induction (p := fun y _ => x i ^ c * y ∈ T) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
      refine Submodule.span_induction
        (p := fun m _ => x i ^ c * ((aeval x s)⁻¹ • m) ∈ T) ?_ ?_ ?_ ?_ (hM a hm)
      · rintro _ ⟨j, f, e', hf, hee, rfl⟩
        rw [smul_eq_mul, smul_eq_mul]
        exact hgenT j f s e e' hs hf hse (by omega)
      · rw [smul_zero, mul_zero]; exact T.zero_mem
      · intro m m' _ _ h h'
        rw [smul_add, mul_add]; exact T.add_mem h h'
      · intro r m _ h
        have : x i ^ c * ((aeval x s)⁻¹ • (r • m)) =
            (algebraMap S (chartRing S x I) r) • (x i ^ c * ((aeval x s)⁻¹ • m)) := by
          rw [chartRing_smul_def]
          simp only [smul_eq_mul, Algebra.smul_def]
          change _ = algebraMap S Ω r * _
          ring
        rw [this]; exact T.smul_mem _ h
    · rw [mul_zero]; exact T.zero_mem
    · intro y y' _ _ h h'
      rw [mul_add]; exact T.add_mem h h'
    · intro b y _ h
      have : x i ^ c * (b • y) = b • (x i ^ c * y) := by
        rw [chartRing_smul_def, chartRing_smul_def]; ring
      rw [this]; exact T.smul_mem b h
  change Submodule.span _ _ ≤ T
  rw [Submodule.span_le]
  rintro _ ⟨q, hq, y, hy, rfl⟩
  change q ∈ twistMod S x c I at hq
  rw [twistMod_eq_span c I hi, Submodule.mem_span_singleton] at hq
  obtain ⟨a, rfl⟩ := hq
  have hy' : y ∈ M.tilde 0 I := by rw [hMtilde I]; exact hy
  have : (a • x i ^ c) • y = a • (x i ^ c * y) := by
    rw [smul_eq_mul, chartRing_smul_def, chartRing_smul_def, mul_assoc]
  rw [SetLike.mem_coe, this]
  exact T.smul_mem a (key y hy')

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistSections
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Loc

variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type*} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]

theorem locRes_locRes {I J K : Finset (Fin (N + 1))} (h1 : I ⊆ J) (h2 : J ⊆ K) (x : LocMod S N M I) :
    locRes h2 (locRes h1 x) = locRes (h1.trans h2) x := by
  revert x
  refine LocalizedModule.induction_on ?_
  intro m s
  rw [locRes_mk, locRes_mk, locRes_mk]

theorem locRes_self {I : Finset (Fin (N + 1))} (h : I ⊆ I) (x : LocMod S N M I) : locRes h x = x := by
  revert x
  refine LocalizedModule.induction_on ?_
  intro m s
  rw [locRes_mk]

theorem locRes_mem_degLoc (𝓜 : GradedPMod S N M) (c : ℤ) (I J : StdCell N) (h : I.1 ⊆ J.1)
    {x : LocMod S N M I.1} (hx : x ∈ degLoc 𝓜 c I) : locRes h x ∈ degLoc 𝓜 c J := by
  have key : degLoc 𝓜 c I ≤ (degLoc 𝓜 c J).comap (locResS I J h) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, s, a, e, hm, hs, hae, rfl⟩
    show locRes h (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I.1) M) ∈ degLoc 𝓜 c J
    rw [locRes_mk]
    exact Submodule.subset_span ⟨m, ⟨s, monos_mono h s.2⟩, a, e, hm, hs, hae, rfl⟩
  exact key hx

end Loc

section Proof

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (y : Fin (N + 1) → Ω)

def primeQuotGraded : GradedPMod S N (Poly S N ⧸ primeOf (S := S) y) :=
  quotGraded (primeOf (S := S) y) fun _ hf d => homogeneousComponent_mem_primeOf y hf d

theorem coordGraded_piece_le_secs (n : ℕ) :
    (coordGraded S y).piece (n : ℤ) ≤ (twistSys S y (n : ℤ)).secs := by
  change Submodule.span S _ ≤ _
  rw [Submodule.span_le]
  rintro _ ⟨f, e, hf, he, rfl⟩
  simp only [SetLike.mem_coe, SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem]
  intro I
  exact Submodule.subset_span ⟨f, 1, 0, e, one_mem _, hf, isHomogeneous_one _ _, by simp [he],
    by simp⟩

theorem exists_rep_of_mem_twistMod (n : ℕ) {j : Fin (N + 1)} (hj : y j ≠ 0) {z : Ω}
    (hz : z ∈ twistMod S y (n : ℤ) (singleChart hj)) :
    ∃ (g s : Poly S N) (e : ℕ), s ∈ monos ({j} : Finset (Fin (N + 1))) ∧ s.IsHomogeneous e ∧
      g.IsHomogeneous (e + n) ∧ aeval y g = z * aeval y s := by
  rw [twistMod_eq_span (n : ℤ) (singleChart hj) (Finset.mem_singleton_self j),
    Submodule.mem_span_singleton] at hz
  obtain ⟨b, rfl⟩ := hz
  obtain ⟨f, s, e, hs, hf, hse, hb⟩ := b.2
  have hs0 : aeval y s ≠ 0 := eval_ne_zero_of_mem_monos (singleChart hj) hs
  refine ⟨f * X j ^ n, s, e, hs, hse, hf.mul (isHomogeneous_X_pow j n), ?_⟩
  rw [chartRing_smul_def, hb, map_mul, map_pow, aeval_X, zpow_natCast]
  field_simp

theorem smul_quot_eq_zero {q : Poly S N} (hq : q ∈ primeOf (S := S) y)
    (m : Poly S N ⧸ primeOf (S := S) y) : q • m = 0 := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective m
  change Ideal.Quotient.mk _ (q * f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right f _ hq

theorem locMod_quot_eq_zero {J : Finset (Fin (N + 1))} {i : Fin (N + 1)} (hi : i ∈ J) (hyi : y i = 0)
    (x : LocMod S N (Poly S N ⧸ primeOf (S := S) y) J) : x = 0 := by
  revert x
  refine LocalizedModule.induction_on ?_
  intro m s
  show (LocalizedModule.mk m s : LocalizedModule (monos (S := S) J) _) = 0
  rw [← LocalizedModule.zero_mk s]
  refine LocalizedModule.mk_eq.mpr ⟨⟨X i, X_mem_monos hi⟩, ?_⟩
  rw [smul_zero, smul_zero, Submonoid.smul_def]
  exact smul_quot_eq_zero y
    ((mem_primeOf_of_isHomogeneous y (isHomogeneous_X S i)).mpr (by rw [aeval_X, hyi])) _

theorem locRes_rep_eq {n : ℕ} {z : Ω} {J : Finset (Fin (N + 1))} {a b : Fin (N + 1)}
    (ha : a ∈ J) (hb : b ∈ J) (ga sa gb sb : Poly S N) (ea eb : ℕ)
    (hsa : sa ∈ monos ({a} : Finset (Fin (N + 1)))) (hsb : sb ∈ monos ({b} : Finset (Fin (N + 1))))
    (hsae : sa.IsHomogeneous ea) (hsbe : sb.IsHomogeneous eb)
    (hga : ga.IsHomogeneous (ea + n)) (hgb : gb.IsHomogeneous (eb + n))
    (hza : aeval y ga = z * aeval y sa) (hzb : aeval y gb = z * aeval y sb) :
    locRes (Finset.singleton_subset_iff.mpr ha)
        (LocalizedModule.mk (Ideal.Quotient.mk (primeOf (S := S) y) ga) ⟨sa, hsa⟩ :
          LocMod S N (Poly S N ⧸ primeOf (S := S) y) {a}) =
      locRes (Finset.singleton_subset_iff.mpr hb)
        (LocalizedModule.mk (Ideal.Quotient.mk (primeOf (S := S) y) gb) ⟨sb, hsb⟩ :
          LocMod S N (Poly S N ⧸ primeOf (S := S) y) {b}) := by
  rw [locRes_mk, locRes_mk]
  refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
  rw [one_smul, one_smul, Submonoid.smul_def, Submonoid.smul_def]
  change Ideal.Quotient.mk _ (sb * ga) = Ideal.Quotient.mk _ (sa * gb)
  rw [Ideal.Quotient.eq]
  have h1 : (sb * ga).IsHomogeneous (eb + (ea + n)) := hsbe.mul hga
  have h2 : (sa * gb).IsHomogeneous (eb + (ea + n)) := by
    have := hsae.mul hgb
    rwa [show ea + (eb + n) = eb + (ea + n) by omega] at this
  rw [mem_primeOf_of_isHomogeneous y (h1.sub h2), map_sub, map_mul, map_mul, hza, hzb]
  ring

theorem secs_le_of_surjective (hy : y ≠ 0) (n : ℕ)
    (hsurj : Function.Surjective (toH0 (primeQuotGraded (S := S) y) (n : ℤ))) :
    (twistSys S y (n : ℤ)).secs ≤ (coordGraded S y).piece (n : ℤ) := by
  intro z hz
  have hloc : ∀ j : Fin (N + 1), ∃ w : LocMod S N (Poly S N ⧸ primeOf (S := S) y) {j},
      w ∈ degLoc (primeQuotGraded (S := S) y) (n : ℤ)
        ⟨{j}, Finset.singleton_nonempty j, Finset.subset_univ _⟩ ∧
      ∀ _ : y j ≠ 0, ∃ (g s : Poly S N) (e : ℕ) (hs : s ∈ monos ({j} : Finset (Fin (N + 1)))),
        s.IsHomogeneous e ∧ g.IsHomogeneous (e + n) ∧ aeval y g = z * aeval y s ∧
        w = LocalizedModule.mk (Ideal.Quotient.mk (primeOf (S := S) y) g) ⟨s, hs⟩ := by
    intro j
    by_cases hj : y j = 0
    · exact ⟨0, Submodule.zero_mem _, fun h => absurd hj h⟩
    · have hzj : z ∈ twistMod S y (n : ℤ) (singleChart hj) := by
        have h' := hz
        simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem] at h'
        exact h' (singleChart hj)
      obtain ⟨g, s, e, hs, hse, hg, hgz⟩ := exists_rep_of_mem_twistMod y n hj hzj
      refine ⟨LocalizedModule.mk (Ideal.Quotient.mk (primeOf (S := S) y) g) ⟨s, hs⟩,
        Submodule.subset_span ⟨Ideal.Quotient.mk (primeOf (S := S) y) g, ⟨s, hs⟩, ((e + n : ℕ) : ℤ), e,
          mem_quotGraded_piece.mpr ⟨g, isWeightedHomogeneous_int_of_isHomogeneous hg, rfl⟩, hse,
          by push_cast; ring, rfl⟩,
        fun _ => ⟨g, s, e, hs, hse, hg, hgz, rfl⟩⟩
  choose w hwdeg hwrep using hloc
  have hcompat : ∀ (J : Finset (Fin (N + 1))) (a b : Fin (N + 1)) (ha : a ∈ J) (hb : b ∈ J),
      locRes (Finset.singleton_subset_iff.mpr ha) (w a) =
        locRes (Finset.singleton_subset_iff.mpr hb) (w b) := by
    intro J a b ha hb
    by_cases h0 : ∃ i ∈ J, y i = 0
    · obtain ⟨i, hi, hyi⟩ := h0
      rw [locMod_quot_eq_zero y hi hyi (locRes (Finset.singleton_subset_iff.mpr ha) (w a)),
        locMod_quot_eq_zero y hi hyi (locRes (Finset.singleton_subset_iff.mpr hb) (w b))]
    · push Not at h0
      obtain ⟨ga, sa, ea, hsa, hsae, hga, hza, hwa⟩ := hwrep a (h0 a ha)
      obtain ⟨gb, sb, eb, hsb, hsbe, hgb, hzb, hwb⟩ := hwrep b (h0 b hb)
      rw [hwa, hwb]
      exact locRes_rep_eq y ha hb ga sa gb sb ea eb hsa hsb hsae hsbe hga hgb hza hzb
  let v : ∀ I : StdCell N, LocMod S N (Poly S N ⧸ primeOf (S := S) y) I.1 := fun I =>
    locRes (Finset.singleton_subset_iff.mpr (I.1.min'_mem I.2.1)) (w (I.1.min' I.2.1))
  have hv : ∀ (I : StdCell N) (a : Fin (N + 1)) (ha : a ∈ I.1),
      v I = locRes (Finset.singleton_subset_iff.mpr ha) (w a) :=
    fun I a ha => hcompat I.1 _ a (I.1.min'_mem I.2.1) ha
  have hvres : ∀ (I J : StdCell N) (h : I.1 ⊆ J.1), locResS I J h (v I) = v J := by
    intro I J h
    change locRes h (v I) = v J
    obtain ⟨a, ha⟩ := I.2.1
    rw [hv I a ha, hv J a (h ha), locRes_locRes]
  let ζ : Cech.Cochain (locSys S N (Poly S N ⧸ primeOf (S := S) y)) 0 := fun I => v I.1
  have hζ : ζ ∈ Cech.cocyDeg (locSys S N (Poly S N ⧸ primeOf (S := S) y))
      (degLoc (primeQuotGraded (S := S) y) (n : ℤ)) locResS 0 := by
    refine Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr
      (Cech.d_zero_of_compat (G := locSys S N (Poly S N ⧸ primeOf (S := S) y)) (ρ := locResS) v hvres), ?_⟩
    rw [Cech.Cdeg, Submodule.mem_pi]
    intro I _
    obtain ⟨a, ha⟩ := I.1.2.1
    change v I.1 ∈ _
    rw [hv I.1 a ha]
    exact locRes_mem_degLoc _ _ ⟨{a}, Finset.singleton_nonempty a, Finset.subset_univ _⟩ I.1 _ (hwdeg a)
  obtain ⟨m, hm⟩ := hsurj (Submodule.Quotient.mk ⟨ζ, hζ⟩)
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra h
    push Not at h
    exact hy (funext h)
  have heq : constCochain (m : Poly S N ⧸ primeOf (S := S) y) = ζ := by
    change Submodule.Quotient.mk (⟨constCochain (m : Poly S N ⧸ primeOf (S := S) y),
      constCochain_mem _ _ _ m.2⟩ : Cech.cocyDeg (locSys S N (Poly S N ⧸ primeOf (S := S) y))
        (degLoc (primeQuotGraded (S := S) y) (n : ℤ)) locResS 0) = _ at hm
    have h2 := (Submodule.Quotient.eq _).mp hm
    rw [Submodule.mem_comap] at h2
    change _ ∈ (⊥ : Submodule S (Cech.Cochain (locSys S N (Poly S N ⧸ primeOf (S := S) y)) 0)) at h2
    rw [Submodule.mem_bot, map_sub] at h2
    exact sub_eq_zero.mp h2
  have hj1 := congrFun heq ⟨⟨{j}, Finset.singleton_nonempty j, Finset.subset_univ _⟩,
    Finset.card_singleton j⟩
  have hvj : v ⟨{j}, Finset.singleton_nonempty j, Finset.subset_univ _⟩ = w j := by
    rw [hv _ j (Finset.mem_singleton_self j), locRes_self]
  obtain ⟨g, s, e, hs, hse, hg, hgz, hwj⟩ := hwrep j hj
  obtain ⟨f, hf, hfm⟩ := mem_quotGraded_piece.mp m.2
  change LocalizedModule.mk (m : Poly S N ⧸ primeOf (S := S) y) 1 =
    v ⟨{j}, Finset.singleton_nonempty j, Finset.subset_univ _⟩ at hj1
  rw [hvj, hwj, ← hfm] at hj1
  obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp hj1
  rw [one_smul, Submonoid.smul_def, Submonoid.smul_def, Submonoid.smul_def] at hu
  change Ideal.Quotient.mk _ ((u : Poly S N) * (s * f)) = Ideal.Quotient.mk _ ((u : Poly S N) * g) at hu
  rw [Ideal.Quotient.eq, ← mul_sub] at hu
  have hu0 : (u : Poly S N) ∉ primeOf (S := S) y := by
    obtain ⟨eu, heu⟩ := monos_isHomogeneous u.2
    rw [mem_primeOf_of_isHomogeneous y heu]
    exact eval_ne_zero_of_mem_monos (singleChart hj) u.2
  have hsf := (Ideal.IsPrime.mem_or_mem inferInstance hu).resolve_left hu0
  have hfh : f.IsHomogeneous n := isHomogeneous_of_isWeightedHomogeneous_one hf
  have h1 : (s * f - g).IsHomogeneous (e + n) := (hse.mul hfh).sub hg
  rw [mem_primeOf_of_isHomogeneous y h1, map_sub, map_mul, hgz] at hsf
  have hs0 : aeval y s ≠ 0 := eval_ne_zero_of_mem_monos (singleChart hj) hs
  have hzf : z = aeval y f := by
    have h3 : aeval y s * (aeval y f - z) = 0 := by linear_combination hsf
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h hs0
    · exact (sub_eq_zero.mp h).symm
  rw [hzf]
  exact Submodule.subset_span ⟨f, n, hfh, rfl, rfl⟩

end Proof

theorem TwistSections.proof (h : SerreOnto.Statement.{u, u}) : TwistSections.Statement.{u, w} := by
  intro S _ _ Ω _ _ N y hy
  obtain ⟨c₀, hc₀⟩ := h S N (Poly S N ⧸ primeOf (S := S) y) (primeQuotGraded y) (finite_quot _)
  rw [Filter.eventually_atTop]
  refine ⟨c₀.toNat, fun n hn => le_antisymm ?_ (coordGraded_piece_le_secs y n)⟩
  exact secs_le_of_surjective y hy n (hc₀ n ((Int.self_le_toNat c₀).trans (by exact_mod_cast hn)))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerreTail
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

theorem SerreTail.proof (hFin : SerreFinite.Statement.{u, v}) (hOnto : SerreOnto.Statement.{u, v}) :
    SerreTail.Statement.{u, v} := by
  classical
  intro S _ _ N M _ _ _ _ 𝓜 hM c₁

  have hfg : ∀ c : ℤ, ∃ s : Finset (Cech.Cochain (locSys S N M) 0),
      Submodule.span S (s : Set _) = Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS 0 := by
    intro c
    have h0 : (Cech.bdryDeg (locSys S N M) (degLoc 𝓜 c) locResS 0).comap
        (Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS 0).subtype = ⊥ := by
      change Submodule.comap _ ⊥ = ⊥
      rw [Submodule.comap_bot, Submodule.ker_subtype]
    have hf : Module.Finite S (Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS 0 ⧸
        (Cech.bdryDeg (locSys S N M) (degLoc 𝓜 c) locResS 0).comap
          (Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS 0).subtype) := hFin S N M 𝓜 hM 0 c
    have hf' : Module.Finite S (Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS 0) :=
      Module.Finite.equiv (Submodule.quotEquivOfEqBot _ h0)
    obtain ⟨s, hs⟩ := Module.Finite.iff_fg.mp hf'
    exact ⟨s, hs⟩
  choose s hs using hfg
  obtain ⟨c₀, hc₀⟩ := hOnto S N M 𝓜 hM
  set c₂ := max c₀ c₁

  let Φ : M →ₗ[Poly S N] Cech.Cochain (locSys S N M) 0 := LinearMap.pi fun I => locMk M I.1.1
  let T : Finset (Cech.Cochain (locSys S N M) 0) := (Finset.Ico c₁ c₂).biUnion s
  let B : Submodule (Poly S N) (Cech.Cochain (locSys S N M) 0) :=
    LinearMap.range Φ ⊔ Submodule.span (Poly S N) (T : Set _)
  have hB : B.FG := by
    refine Submodule.FG.sup ?_ (Submodule.fg_span T.finite_toSet)
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map Φ

  have hA : H0tail 𝓜 c₁ ≤ B.restrictScalars S := by
    refine iSup₂_le fun c hc => ?_
    intro z hz
    by_cases hc2 : c₂ ≤ c
    · obtain ⟨m, hm⟩ := hc₀ c (le_trans (le_max_left _ _) hc2) (Submodule.Quotient.mk ⟨z, hz⟩)
      have hz' : (constCochain (m : M) : Cech.Cochain (locSys S N M) 0) = z := by
        have := (Submodule.Quotient.eq _).mp hm
        change _ ∈ Submodule.comap _ ⊥ at this
        rw [Submodule.mem_comap, Submodule.mem_bot, map_sub, sub_eq_zero] at this
        exact this
      rw [← hz']
      exact Submodule.mem_sup_left ⟨(m : M), rfl⟩
    · have hcI : c ∈ Finset.Ico c₁ c₂ := Finset.mem_Ico.mpr ⟨hc, lt_of_not_ge hc2⟩
      rw [← hs c] at hz
      refine Submodule.mem_sup_right (Submodule.span_le_restrictScalars S (Poly S N) _ ?_)
      refine Submodule.span_mono ?_ hz
      intro y hy
      exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨c, hcI, hy⟩)
  have hspan : Submodule.span (Poly S N) (H0tail 𝓜 c₁ : Set (Cech.Cochain (locSys S N M) 0)) ≤ B :=
    Submodule.span_le.mpr hA
  have : IsNoetherian (Poly S N) B := isNoetherian_of_fg_of_noetherian B hB
  obtain ⟨t, ht, hteq⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).mp
    (Submodule.FG.of_le_of_isNoetherian hspan)
  refine ⟨t, fun z hz => ht hz, fun z hz => ?_⟩
  change z ∈ Submodule.span (Poly S N) (t : Set _)
  rw [← hteq]
  exact Submodule.subset_span hz

end

end GroundTheory.Heights₂.Heights.Kleiman
end
