(* ***** ***** *)

//  ==================
//  REFERENCE COUNTING
//  ==================

//  A port of
//  https://github.com/githwxi/ATS-Temptory/blob/master/libats/SATS/refcnt.sats

(* ***** ***** *)

//  These must be implemented in order
//  for this library to be compiled, for
//  the reference counted `a` in question.

fun{a: vt0p}
gcopy$val(!a): a

fun{a: vt0p}
gfree$val(a): void

(* ***** ***** *)

absvtype
refcnt_vt0p(a: vt0ype+) = ptr

vtypedef
refcnt(a: vt0p) = refcnt_vt0p(a)

(* ***** ***** *)

fun{a:vt0p}
refcnt_make_elt(x0: a): refcnt(a)

symintr refcnt
overload refcnt with refcnt_make_elt

(* ****** ****** *)

fun{a:vt0p}
refcnt_get0_elt(refcnt(a)): a

fun{a:vt0p}
refcnt_get1_elt(!refcnt(a)): a

fun{a:vt0p}
refcnt_get1_cnt(!refcnt(a)): intGte(1)

(* ****** ****** *)

fun{a:vt0p}
refcnt_decref(refcnt(a)): void

fun{a:vt0p}
refcnt_incref(!refcnt(a)): refcnt(a)

symintr decref
overload decref with refcnt_decref
symintr incref
overload incref with refcnt_incref

(* ****** ****** *)

fun{a:vt0p}
refcnt_vtakeout
  (rfc: !refcnt(a)) :
  [l: agz]
  ( a @ l
  , a @ l -<lin,prf> void
  | ptr(l)
  )

overload vtakeout with refcnt_vtakeout

(* ****** ****** *)

//  End of `refcnt.sats`.
