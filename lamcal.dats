//  =======================
//  LAMBDA CALCULUS without
//  garbage by HOAS in ATS2
//  =======================
//
//  A small and efficient program to compute (normalize)
//  terms in the untyped λ-calculus. The interpreter uses
//  a higher order abstract syntax (HOAS) encoding with
//  linear ATS-types and requires no garbage collection.
//
//  Should compile with
//  patscc -g -flto -D_GNU_SOURCE -DATS_MEMALLOC_LIBC lamcal.dats -o a -latslib
//
//  Closely based on the Javascript algorithm here:
//  https://github.com/MaiaVictor/lambda-calculus/issues/1
//

(* ***** ***** *)

#include "share/atspre_define.hats"
#include "share/atspre_staload.hats"
staload UN = "prelude/SATS/unsafe.sats"
staload IO = "libats/libc/SATS/stdio.sats"

(* ***** ***** *)

//  ===========================
//  Prelude: REFERENCE COUNTING
//  ===========================
//
//  A port of a minimal subset of
//  https://github.com/githwxi/ATS-Temptory/blob/master/libats/SATS/refcnt.sats


//  This must be implemented in order for this `library` to
//  be compiled, for the reference counted `a` in question.
extern fun{a: vt0p}
gfree$val(a): void

(* ***** ***** *)

absvtype
refcnt_vt0p(a: vt0ype+) = ptr

vtypedef
refcnt(a: vt0p) = refcnt_vt0p(a)

(* ***** ***** *)

extern fun{a: vt0p}
refcnt_make_elt(x0: a): refcnt(a)

symintr refcnt
overload refcnt with refcnt_make_elt

//  Never used. Remove dead code?
extern fun{a: vt0p}
refcnt_get1_cnt(!refcnt(a)): intGte(1)

extern fun{a: vt0p}
refcnt_decref(refcnt(a)): void

extern fun{a: vt0p}
refcnt_incref(!refcnt(a)): refcnt(a)

symintr decref
overload decref with refcnt_decref
symintr incref
overload incref with refcnt_incref

extern fun{a: vt0p}
refcnt_vtakeout
  (rfc: !refcnt(a)):
  [l: agz](a @ l, a @ l -<lin,prf> void| ptr(l))

overload vtakeout with refcnt_vtakeout

//  The following two functions require implementation of
//  a `duplication`:
extern fun{a: vt0p}
gcopy$val(!a): a

extern fun{a: vt0p}
refcnt_get0_elt(refcnt(a)): a

extern fun{a: vt0p}
refcnt_get1_elt(!refcnt(a)): a

(* ****** ****** *)

// Implementation.

local

  datavtype
  refcnt_(a: vt0ype+) = REFCNT of (uint, a)

  assume
  refcnt_vt0p(a) = refcnt_(a)

in

  implement{a}
  refcnt_make_elt(x0) = REFCNT(1u, x0)

  implement{a}
  refcnt_get1_cnt(rc) =
    let val+ REFCNT(u, x) = rc
    in $UN.cast{intGte(1)}(u) end

  implement{a}
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

  implement{a}
  refcnt_incref(rc) = let
      val @REFCNT(u, x) = rc
      val () = u := succ(u)
      prval () = fold@(rc)
    in
      $UN.castvwtp1{refcnt(a)}(rc)
    end

  implement{a}
  refcnt_vtakeout(rc) = res where
      val @REFCNT(_, x) = rc
      val res = $UN.castvwtp0(addr@(x))
      prval () = fold@(rc)
    end

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

end // of local (and implementation).

(* ***** ***** *)

// Reference-counted strings.

vtypedef
rcstr = refcnt(strptr)

implement
gfree$val<strptr>(s) = free(s)

fun{}
s2rc(s: strptr): rcstr = refcnt_make_elt<strptr>(s)

(* ***** ***** *)

//  Functions involving duplication/copying.

implement
gcopy$val<strptr>(s) = strptr0_copy(s)

fun{}
rc2s(rcs: rcstr): strptr = refcnt_get0_elt<strptr>(rcs)

fun{}
rc2s_cpy(rcs: !rcstr): strptr = refcnt_get1_elt<strptr>(rcs)

(* ***** ***** *)

//  =====================
//  ABSTRACT SYNTAX TREES
//  =====================

//  Our type-to-be of the abstract syntax trees.
absvtype
term = ptr

//  Linear function type.
vtypedef
lam_vtype = term -<lincloptr1> term

//  Note: Linear closures want to be evaluated before
//  they are freed with this macro.
macdef
free_end(f) = cloptr_free($UN.castvwtp0(,(f)))

//  HOAS encoding of untyped λ-calculus.
datavtype
term_vtype = Var of rcstr
           | Lam of (rcstr, lam_vtype)
           | App of (term_vtype, term_vtype)

assume
term = term_vtype

//  Frees an abstract syntax tree (all nodes).
fun{}
free_term(t0: term): void =
  case+ t0 of
  | ~Var(rcs) => decref<strptr>(rcs)
  | ~Lam(rcs, f) => (free_term(fs); free_end(f))
      where val fs = f(Var(rcs)) end
  | ~App(t1, t2) => (free_term(t1); free_term(t2))

//  Pretty-printing. Note that it consumes the input term.
//  It also allocates more than necessary.
fun
fprint_term(out: FILEref, t: term): void =
  case+ t of
  | ~Var(rcs) => let
        val s = rc2s(rcs) in (fprint_strptr(out, s); free(s))
      end
  | ~Lam(rcs, f) => () where
        val s = rc2s_cpy(rcs)
        val () = ( fprint_string(out, "λ")
                 ; fprint_strptr(out, s)
                 ; fprint_string(out, ".")
                 ; free(s)
                 )
        val fs = f(Var(rcs))
        val () = (fprint_term(out, fs); free_end(f))
      end
  | ~App(f, x) => ( fprint_term(out, f)
                  ; fprint_string(out, "(")
                  ; fprint_term(out, x)
                  ; fprint_string(out, ")")
                  )

(* ***** ***** *)

//  =========================
//  NORMALIZING λ-EXPRESSIONS
//  =========================

//  With HOAS encoding of the syntax we are rewarded with a
//  short and easy route to evaluation (i.e., normalization)
//  of λ-calculus terms.

extern fun
normalize(term): term

(* ***** ***** *)

//  Reduces a term to weak head normal form.
fun{}
reduce(t0: term): term =
  case+ t0 of
  | ~App(~Lam(rcs, f), t) => let
        val ft = f(t) in (decref<strptr>(rcs); free_end(f); reduce(ft))
      end
  | _ => t0

//  Reduces a term to normal form.
implement
normalize(t0): term =
  let
    val red = reduce(t0)
  in
    case+ red of
    | ~Lam(arg, f) => let
          // Evade scope restriction on linear variable:
          val f = $UN.castvwtp0{ptr}(f)
        in
          Lam( arg
             , llam(x) => normalize(fx) where
                   // Get back to where you once belonged.
                   val f = $UN.castvwtp0{lam_vtype}(f)
                   val fx = f(x)
                   val () = free_end(f)
                 end
             )
        end
    | ~App(h, t) => App(normalize(h), normalize(t))
    | _ (*Var(rcs)*) => red
  end

(* ***** ***** *)

//  =================
//  VARIABLE BINDINGS
//  =================

vtypedef
bind = @{nam = rcstr, trm = term}

fun{}
free_bind(bnd: bind): void =
  (decref<strptr>(bnd.nam); free_term(bnd.trm))

(* ***** ***** *)

//  Contexts.

//  Our parser can handle terms with at most 256 lambdas.
#define CTXCAP 256

vtypedef
ctxarr = @[bind][CTXCAP]

typedef
ctxidx = [i: nat | i < CTXCAP] uint(i)

vtypedef
ctxstruct = @{arr = ctxarr, cur = ctxidx}

//  Contexts are reference-counted arrays of bindings. We
//  leave `gcopy$val` without implementation. This makes
//  the templates `refcnt_get0_elt` and `refcnt_get1_elt`
//  illegal to call. So we don't.
vtypedef
context = refcnt(ctxstruct)

//  Create an empty context.
extern fun{}
make_empty_ctx(): context

//  Adding a binding to a context.
extern fun{}
add_to_ctx(!context, bind): void

exception
UnboundNameExn of ()

//  The exception is raised if the `strptr` argument is not
//  found as a bound name in the context.
extern fun{}
find_in_ctx(strptr, !context): term

(* ***** ***** *)

//  This looks a bit fishy. Valgrind will tell...
implement
gfree$val<ctxstruct>(w) =
  let
    var v = w.arr

    implement
    array_uninitize$clear<bind>(i, b) = let
        val bnd = b
      in
        if i < u2sz(w.cur) then free_bind(bnd) else $UN.castvwtp0{void}(bnd)
      end

  in
    array_uninitize<bind>(v, i2sz(256))
  end

(* ***** ***** *)

local

  viewdef
  ctxarr_v(l: addr) = array_v(bind, l, CTXCAP)

  fun{}
  get_arr_ptr{l: agz}
    (pfctx: ctxstruct @ l | p: ptr(l)):
    [l1: agz](ctxarr_v(l1), ctxarr_v(l1) -<lin> ctxstruct @ l | ptr(l1)) =
    let val addr_arr = addr@(p->arr) in $UN.castvwtp0((pfctx | addr_arr)) end

  fun{}
  get_arr_ptr_uninit{l: agz}
    (pfctx: ctxstruct? @ l | p: ptr(l)):
    [l1: agz]( array_v(bind?, l1, CTXCAP)
             , array_v(bind?, l1, CTXCAP) -<lin> ctxstruct? @ l
             | ptr(l1)) =
    let val addr_arr = addr@(p->arr) in $UN.castvwtp0((pfctx | addr_arr)) end

  fun{}
  get_cur_ptr{l: agz}
    (pfctx: ctxstruct @ l | p: ptr(l)):
    [l1: agz](ctxidx @ l1, ctxidx @ l1 -<lin> ctxstruct @ l | ptr(l1)) =
    let val addr_cur = addr@(p->cur) in $UN.castvwtp0((pfctx | addr_cur)) end

  fun{}
  term_of_bindopt(bndopt: Option_vt(bind)): term =
    case bndopt of
    | ~None_vt() => $raise UnboundNameExn()
    | ~Some_vt(bnd) => (decref<strptr>(bnd.nam); bnd.trm)

in
  implement
  array_initize$init<bind>(i, b) = let
      val noname = s2rc(string0_copy(""))
    in
      (b.nam := incref<strptr>(noname); b.trm := Var(noname))
    end

  implement
  make_empty_ctx<>() = let
      val (pf, pfgc | p) = ptr_alloc<ctxstruct>()
      prval () = mfree_gc_v_elim(pfgc)
      val (pfarr, fpfarr | parr) = get_arr_ptr_uninit(pf | p)
      val (pfngc | A) = arrayptr_objectify(pfarr | parr)
      val () = arrayptr_initize(A, i2sz(CTXCAP))
      val (pfarr | parr) = arrayptr_unobjectify(pfngc | A)
      // `fpfarr` does not know `A` has been initized.
      prval pf = $UN.castview0(fpfarr(pfarr))
      val (pfcur, fpfcur | pcur) = get_cur_ptr(pf | p)
      val () = !pcur := 0u
      prval pf = fpfcur(pfcur)
    in
      $UN.castvwtp0{context}((pf | p))
    end

  implement
  add_to_ctx<>(ctx, bnd) = let
      val (pf, fpf | p) = vtakeout<ctxstruct>(ctx)
      val (pfcur, fpfcur | pcur) = get_cur_ptr(pf | p)
      val i: ctxidx = !pcur
      prval pf = fpfcur(pfcur)
      val (pfarr, fpfarr | parr) = get_arr_ptr(pf | p)
      val (pfngc | A) = arrayptr_objectify(pfarr | parr)
      var b = bnd
      val () = (arrayptr_exch_at(A, i, b); free_bind(b))
      val (pfarr | parr) = arrayptr_unobjectify(pfngc | A)
      prval pf = fpfarr(pfarr)
      val (pfcur, fpfcur | pcur) = get_cur_ptr(pf | p)
      val i = !pcur
      val si = (if (i = i2u(CTXCAP) - 1u) then i else i + 1u)
      val si = $UN.cast{ctxidx}(si) // Dumb constraint solver.
      val () = !pcur := si
      prval () = fpf(fpfcur(pfcur))
    in
      ()
    end

   implement
   find_in_ctx<>(name, ctx) =
     let
       fun loop
         (x: Strptr1, p: ptr, k: uint): Option_vt(bind) =
         if (k = 0u) then
           (free(x); None_vt())
         else let
             val bnd = $UN.ptr0_get<bind>(p)
             val nam = $UN.castvwtp0{string}(rc2s_cpy(bnd.nam))
           in
             if x = nam then
               (free(x); free($UN.castvwtp0{strptr}(nam)); Some_vt(bnd))
             else
               ( $UN.castvwtp0{void}(bnd) // free_bind(bnd)?
               ; loop(x, ptr_pred<bind>(p), pred(k))
               )
           end

       val (pf, fpf | p) = vtakeout<ctxstruct>(ctx)
       val (pfcur, fpfcur | pcur) = get_cur_ptr(pf | p)
       val i: uint = !pcur
       prval pf = fpfcur(pfcur)
       val (pfarr, fpfarr | parr) = get_arr_ptr(pf | p)
       val bndopt = loop($UN.castvwtp0{Strptr1}(name), parr, i)
       prval () = fpf(fpfarr(pfarr))
     in
       term_of_bindopt(bndopt)
     end

end // of local.

(* ***** ***** *)

//  =====================
//  PARSING λ-EXPRESSIONS
//  =====================

(* ***** ***** *)

//  String buffer.

//  We use a statically allocated array for intermediate parsing.
//  The fixed size means we only handle variable names that are
//  at most 32 chars long.

#define BUFCAP 32

extern fun
add_to_the_buf(char): void

extern fun
read_the_buf(): Strptr1

extern fun
reset_the_buf(): void

(* ***** ***** *)

local
  var _the_buf = @[char][BUFCAP]()
  var _the_buf_sz: [i: nat | i < BUFCAP] uint(i) = 0u

  val the_buf_ptr = addr@_the_buf
  val the_buf_sz = ref_make_viewptr(view@_the_buf_sz | addr@_the_buf_sz)
in
  // First deal with the size.
  fun get_the_buf_sz(): [i: nat| i < BUFCAP] uint(i) =
    ref_get_elt(the_buf_sz)

  fun inc_the_buf_sz(): void = let
      val i = get_the_buf_sz()
    in
      if i = pred(BUFCAP) then
        ( println!("The \"buffer\" array is full!")
        ; ref_set_elt(the_buf_sz, i)
        )
      else
        ref_set_elt(the_buf_sz, succ(i))
    end

  implement
  reset_the_buf(): void = (free(read_the_buf()); !the_buf_sz := 0u)

  // Now the actual buffer functions.
  implement
  add_to_the_buf(c) = let
      val i = get_the_buf_sz()
      val the_buf_ptr_i = ptr1_add_guint<char>(the_buf_ptr, i)
    in
      ( $UN.ptr0_set<char>(the_buf_ptr_i, c)
      ; inc_the_buf_sz()
      )
    end

  implement
  read_the_buf() = let
      val sz = get_the_buf_sz()
      val n = sz
      val [n: int] n = g1ofg0_uint(n)
      val s = string_make_substring
                ( $UN.cast{string(n)}(the_buf_ptr)
                , i2sz(0)
                , u2sz(n)
                )
      prval () = lemma_strnptr_param(s)
    in
      (!the_buf_sz := 0u; strnptr2strptr(s))
    end
end

(* ***** ***** *)

//  Input type.

abstype
input

//  "Popping"; reading one char and advancing the current position in
//  the source code (input).
extern fun{}
input_getc(input): char // fgetc0(FILEref): <wrt!> int

//  Need the equation
//  input_getc(inp) = (input_ungetc(input_getc(inp), inp); input_getc(inp))
//  to hold (except possibly for corner cases).
extern fun{}
input_ungetc(char, input): void  //ungetc0_exn(FILEref): <exnwrt!> void

(* ***** ***** *)

// Implementing [input] from files.

#define i2c int2char0

extern fun
input_from_fileref(FILEref): input

local
  assume
  input = FILEref
in
  implement
  input_from_fileref(inp) = inp

  implement
  input_getc<>(inp) = i2c($IO.fgetc0(inp))

  implement
  input_ungetc<>(c, inp) = $IO.ungetc0_exn(c, inp)
end

(* ***** ***** *)

// Parsing helper functions.

fun{}
parse_char(chr: char, inp: input): void =
  let val c = input_getc(inp) in
    if (c != chr) then
      (input_ungetc(c, inp); println!("Bad char parse."))
  end

fun{}
parse_whitespace(inp: input): void =
  let val c = input_getc(inp) in
    if isspace(c) then parse_whitespace(inp)
    else input_ungetc(c, inp)
  end

fun{}
parse_name(inp: input): strptr =
  let
    fun loop(p: input): void =
      let val c = input_getc(p) in
        if (isalnum(c) || c = '_') then add_to_the_buf(c)
        else input_ungetc(c, inp)
      end
  in
    (loop(inp); read_the_buf())
  end

(* ***** ***** *)

//  The core parsing algorithm.
extern fun{}
parse_term(input, context): term

fun{}
parse_lam(inp: input, ctx: context): term =
  let
    val name = s2rc(parse_name(inp))
    val ((*check*)) = parse_char('.', inp)
    // Duplicate and dodge scope restriction.
    val name1 = incref<strptr>(name)
    val name = $UN.castvwtp0{ptr}(name)
    val name1 = $UN.castvwtp0{ptr}(name1)
  in
      Lam( $UN.castvwtp0{rcstr}(name)
         , llam(x) => let
               val name1 = $UN.castvwtp0{rcstr}(name1)
             in
               ( add_to_ctx(ctx, @{nam = name1, trm = x})
               ; parse_term(inp, ctx)
               )
             end
         )
  end

fun{}
parse_app(inp: input, ctx: context): term =
  let
    val func = parse_term(inp, incref<ctxstruct>(ctx))
    val argm = parse_term(inp, ctx)
    val ((*check*)) = parse_char(')', inp)
  in
    App(func, argm)
  end

implement
parse_term<>(inp, ctx) =
  let
    val () = parse_whitespace(inp)
    val chr = input_getc(inp)
  in
    case chr of
    | '\\' => parse_lam(inp, ctx)
    | '\(' => parse_app(inp, ctx)
    | _ =>  let
          // `chr` should be part of a name:
          val () = input_ungetc(chr, inp)
          val result = find_in_ctx(parse_name(inp), ctx)
        in
          (decref<ctxstruct>(ctx); result)
        end
  end

(* ***** ***** *)

//  Our parser function.

fun
parse(inp: input): term = let
    val () = reset_the_buf()
    val ctx = make_empty_ctx()
  in
    parse_term(inp, ctx)
  end

(* ***** ***** *)

implement
main() = 0 where
  // The file contains "\\x.x".
  val fref = fileref_open_exn("src.lc", file_mode_r)
  val inp = input_from_fileref(fref)
  val prs = parse(inp)
  val wow = normalize(prs)
  val () = (fprint_term(stdout_ref, wow); print_newline())
  val () = fileref_close(fref)
end
