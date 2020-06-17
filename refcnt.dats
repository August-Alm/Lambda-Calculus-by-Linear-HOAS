(* ***** ***** *)

#include "share/atspre_define.hats"
#include "share/atspre_staload.hats"
staload UN = "prelude/SATS/unsafe.sats"
staload "refcnt.sats"

(* ***** ***** *)

datavtype
refcnt_(a: vt0ype+) = REFCNT of (uint, a)

assume
refcnt_vt0p(a) = refcnt_(a)

(* ***** ***** *)

implement{a: vt0p}
refcnt_make_elt(x0) = REFCNT(1u, x0)

implement{a: vt0p}
refcnt_get0_elt(rc) =
  case rc of
  | @REFCNT(u, x) =>
    if u <= 1u then
      let val res = x in
        (free@(rc); res)
      end
    else let
        val res = gcopy$val<a>(x)
        val () = u := pred(u)
        prval () = fold@(rc)
        prval () = $UN.castvwtp0(rc)
      in
        res
      end

implement{a: vt0p}
refcnt_get1_elt(rc) =
  let val+ REFCNT(u, x) = rc
  in gcopy$val<a>(x) end

implement{a: vt0p}
refcnt_get1_cnt(rc) =
  let val+ REFCNT(u, x) = rc
  in $UN.cast{intGte(1)}(u) end

(* ***** ***** *)

implement{a: vt0p}
refcnt_decref(rc) = let
    val @REFCNT(u, x) = rc
  in if (u <= 1u)
    then (gfree$val<a>(x); free@(rc))
    else let
      val () = u := pred(u)
      prval () = fold@(rc)
      prval () = $UN.castvwtp0(rc)
    in
      ()
    end
  end

implement{a: vt0p}
refcnt_incref(rc) = let
    val @REFCNT(u, x) = rc
    val () = u := succ(u)
    prval () = fold@(rc)
  in
    $UN.castvwtp1{refcnt(a)}(rc)
  end

(* ***** ***** *)

implement{a: vt0p}
refcnt_vtakeout(rc) = res where
    val @REFCNT(_, x) = rc
    val res = $UN.castvwtp0(addr@(x))
    prval () = fold@(rc)
  end

(* ***** ***** *)

// End of `refcnt.dats`.

