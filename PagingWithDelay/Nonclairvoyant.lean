import PagingWithDelay.Online

/-!
# Nonclairvoyance, and how it relates to onlineness

`Model.lean` defines `Algorithm.Nonclairvoyant` by comparing two instances that
have revealed the same thing by a time `t`.  This file records the elementary
facts about that comparison: `Request.AgreeUpTo` is an equivalence at each `t`,
two instances with equal truncations agree in particular, and therefore every
nonclairvoyant algorithm is online.

Stating nonclairvoyance by comparing two instances, rather than by comparing an
instance with a canonical truncation of itself, keeps the definition free of
any choice of how a delay curve is to be continued past the delay it has
accrued: no continuation is named, and none is assumed to exist.
-/

namespace PagingWithDelay

noncomputable section

variable {Page : Type*}

namespace Request

@[refl] theorem AgreeUpTo.refl (t : Time) (request : Request Page) :
    AgreeUpTo t request request :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

theorem AgreeUpTo.symm {t : Time} {first second : Request Page}
    (agree : AgreeUpTo t first second) : AgreeUpTo t second first where
  page := agree.page.symm
  arrival := agree.arrival.symm
  delay wait hwait := (agree.delay wait (by rw [agree.arrival]; exact hwait)).symm

theorem AgreeUpTo.trans {t : Time} {first second third : Request Page}
    (left : AgreeUpTo t first second) (right : AgreeUpTo t second third) :
    AgreeUpTo t first third where
  page := left.page.trans right.page
  arrival := left.arrival.trans right.arrival
  delay wait hwait :=
    (left.delay wait hwait).trans (right.delay wait (by rw [← left.arrival]; exact hwait))

end Request

namespace Instance

/-- Truncations that are literally equal agree, so `Instance.AgreeUpTo` asks
for less than the hypothesis of `Algorithm.Online`. -/
theorem AgreeUpTo.of_upTo_eq {first second : Instance Page} {t : Time}
    (heq : first.upTo t = second.upTo t) : first.AgreeUpTo second t where
  cacheSize := by
    have hcache := congrArg Instance.cacheSize heq
    exact hcache
  requests := by
    rw [heq]
    exact List.forall₂_same.mpr fun request _ => Request.AgreeUpTo.refl t request

theorem AgreeUpTo.refl (input : Instance Page) (t : Time) : input.AgreeUpTo input t :=
  AgreeUpTo.of_upTo_eq rfl

theorem AgreeUpTo.symm {first second : Instance Page} {t : Time}
    (agree : first.AgreeUpTo second t) : second.AgreeUpTo first t where
  cacheSize := agree.cacheSize.symm
  requests := by
    apply List.Forall₂.flip
    exact agree.requests.imp fun _ _ hrequest => hrequest.symm

end Instance

variable [DecidableEq Page]

/-- **Nonclairvoyance implies onlineness.**  An algorithm that cannot see the
delay a request has yet to accrue certainly cannot see a request that has yet
to arrive. -/
theorem Algorithm.Nonclairvoyant.online {algorithm : Algorithm Page}
    (nonclairvoyant : Algorithm.Nonclairvoyant algorithm) : Algorithm.Online algorithm where
  prefixDetermined first second hfirst hsecond t heq :=
    nonclairvoyant.observationDetermined first second hfirst hsecond t
      (Instance.AgreeUpTo.of_upTo_eq heq)

end
end PagingWithDelay
