(* xml-tree -- recursive descent XML tree parser *)
(* Nodes store integer offsets into the input buffer. *)
(* Size-indexed datavtypes for proven-terminating free. *)
(* No $UNSAFE. *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR

(* ============================================================
   Types -- indexed by the document's length and by size
   ============================================================ *)

(* Every offset and length is a span [o, o + k) of the parsed document of
   n bytes: o + k <= n, so a consumer reads it with no range check. The
   size index proves the frees terminate. *)
#pub datavtype xml_node(n:int, sz:int) =
  | {sa,sc:nat}{no,nl:nat | no + nl <= n}
    xml_element(n, 1+sa+sc) of (int no, int nl, xml_attr_list(n, sa), xml_node_list(n, sc))
  | {o:nat}{k:pos | o + k <= n}
    xml_text(n, 1) of (int o, int k)

#pub and xml_node_list(n:int, sz:int) =
  | xml_nodes_nil(n, 0) of ()
  | {s1:pos}{s2:nat}
    xml_nodes_cons(n, s1+s2) of (xml_node(n, s1), xml_node_list(n, s2))

#pub and xml_attr_list(n:int, sz:int) =
  | xml_attrs_nil(n, 0) of ()
  | {s1:nat}{ao,al,vo,vl:nat | ao + al <= n; vo + vl <= n}
    xml_attrs_cons(n, 1+s1) of (int ao, int al, int vo, int vl, xml_attr_list(n, s1))

(* ============================================================
   Public API
   ============================================================ *)

#pub fun parse_document
  {lb:agz}{n:pos}
  (data: !$A.borrow(byte, lb, n), len: int n): [sz:nat] xml_node_list(n, sz)

#pub fun free_nodes {n:int}{sz:nat} (nodes: xml_node_list(n, sz)): void

#pub fun free_node {n:int}{sz:pos} (node: xml_node(n, sz)): void

(* ============================================================
   Positions
   ============================================================ *)

(* Positions are indexed ints p <= n; each scanner returns a position at
   or after the one it started from, and recurses on the metric n - p.
   A read happens only after a p < len test (the end of the input). *)

fn _at {lb:agz}{n:pos}{p:nat | p < n}
  (data: !$A.borrow(byte, lb, n), p: int p): int =
  byte2int0($A.read<byte>(data, p))

fn _is_ws(c: int): bool =
  c = 32 || c = 9 || c = 10 || c = 13

fn _is_name_char(c: int): bool =
  if c >= 97 then c < 123
  else if c >= 65 then c < 91
  else if c = 58 then true
  else if c >= 48 then c < 58
  else c = 95 || c = 45 || c = 46

(* ============================================================
   Scanning helpers
   ============================================================ *)

fun _skip_ws {lb:agz}{n:pos}{p:nat | p <= n} .<n - p>.
  (data: !$A.borrow(byte, lb, n), len: int n, p: int p): [q:int | p <= q; q <= n] int q =
  if p >= len then p
  else if _is_ws(_at(data, p)) then _skip_ws(data, len, p + 1)
  else p

(* Just past the "-->" that ends a comment, or the end *)
fun _skip_comment {lb:agz}{n:pos}{p:nat | p <= n} .<n - p>.
  (data: !$A.borrow(byte, lb, n), len: int n, p: int p): [q:int | p <= q; q <= n] int q =
  if p + 2 >= len then len
  else if _at(data, p) = 45 && _at(data, p + 1) = 45 && _at(data, p + 2) = 62 then p + 3
  else _skip_comment(data, len, p + 1)

(* Just past the "?>" that ends a processing instruction, or the end *)
fun _skip_pi {lb:agz}{n:pos}{p:nat | p <= n} .<n - p>.
  (data: !$A.borrow(byte, lb, n), len: int n, p: int p): [q:int | p <= q; q <= n] int q =
  if p + 1 >= len then len
  else if _at(data, p) = 63 && _at(data, p + 1) = 62 then p + 2
  else _skip_pi(data, len, p + 1)

(* Just past the '>' that closes a declaration opened depth '<' deep
   (nested ones included), or the end *)
fun _skip_doctype {lb:agz}{n:pos}{p:nat | p <= n} .<n - p>.
  (data: !$A.borrow(byte, lb, n), len: int n, p: int p, depth: int): [q:int | p <= q; q <= n] int q =
  if p >= len then len
  else let val c = _at(data, p) in
    if c = 60 then _skip_doctype(data, len, p + 1, depth + 1)
    else if c = 62 then
      (if depth = 1 then p + 1 else _skip_doctype(data, len, p + 1, depth - 1))
    else _skip_doctype(data, len, p + 1, depth)
  end

fun _scan_name {lb:agz}{n:pos}{p:nat | p <= n} .<n - p>.
  (data: !$A.borrow(byte, lb, n), len: int n, p: int p): [q:int | p <= q; q <= n] int q =
  if p >= len then p
  else if _is_name_char(_at(data, p)) then _scan_name(data, len, p + 1)
  else p

(* The first byte q in [p, e) equal to quote, or e *)
fun _scan_quote {lb:agz}{n:pos}{p,e:nat | p <= e; e <= n} .<e - p>.
  (data: !$A.borrow(byte, lb, n), p: int p, e: int e, quote: int): [q:int | p <= q; q <= e] int q =
  if p >= e then e
  else if _at(data, p) = quote then p
  else _scan_quote(data, p + 1, e, quote)

(* Just past the quote that closes a value, or the end *)
fun _skip_quoted {lb:agz}{n:pos}{p:nat | p <= n} .<n - p>.
  (data: !$A.borrow(byte, lb, n), len: int n, p: int p, quote: int): [q:int | p <= q; q <= n] int q =
  if p >= len then p
  else if _at(data, p) = quote then p + 1
  else _skip_quoted(data, len, p + 1, quote)

(* The first '<' at or after p, or the end *)
fun _scan_text {lb:agz}{n:pos}{p:nat | p <= n} .<n - p>.
  (data: !$A.borrow(byte, lb, n), len: int n, p: int p): [q:int | p <= q; q <= n] int q =
  if p >= len then p
  else if _at(data, p) = 60 then p
  else _scan_text(data, len, p + 1)

(* Just past the next '>', or the end *)
fun _skip_closing {lb:agz}{n:pos}{p:nat | p <= n} .<n - p>.
  (data: !$A.borrow(byte, lb, n), len: int n, p: int p): [q:int | p <= q; q <= n] int q =
  if p >= len then p
  else if _at(data, p) = 62 then p + 1
  else _skip_closing(data, len, p + 1)

(* Where a start tag ends, searching from lo: its '>' at t, the "/>" of
   an empty element at t, or no end before the end of the input. *)
datatype tag_end(n:int, lo:int) =
  | {t:int | lo <= t; t < n} tag_open(n, lo) of int t
  | {t:int | lo <= t; t + 1 < n} tag_self(n, lo) of int t
  | tag_eof(n, lo) of ()

(* A '>' or '/' inside a quoted attribute value does not end the tag. *)
fun _find_tag_end {lb:agz}{n:pos}{p:nat | p <= n} .<n - p>.
  (data: !$A.borrow(byte, lb, n), len: int n, p: int p): [lo:int | p <= lo] tag_end(n, lo) =
  if p >= len then (tag_eof(): tag_end(n, p))
  else let val c = _at(data, p) in
    if c = 62 then (tag_open(p): tag_end(n, p))
    else if c = 47 then
      (if p + 1 >= len then (tag_eof(): tag_end(n, p))
       else if _at(data, p + 1) = 62 then (tag_self(p): tag_end(n, p))
       else _find_tag_end(data, len, p + 1))
    else if c = 34 || c = 39 then _find_tag_end(data, len, _skip_quoted(data, len, p + 1, c))
    else _find_tag_end(data, len, p + 1)
  end

(* ============================================================
   Attribute parser
   ============================================================ *)

(* The attributes name="value" (or 'value') in [p, e), up to the first
   byte that does not continue one. Each one found consumes its name
   (at least one byte), so the metric n - p decreases. *)
fun _parse_attrs {lb:agz}{n:pos}{p,e:nat | p <= e; e <= n} .<n - p>.
  (data: !$A.borrow(byte, lb, n), len: int n, p: int p, e: int e): [sa:nat] xml_attr_list(n, sa) = let
  val p = _skip_ws(data, len, p)
in
  if p >= e then xml_attrs_nil()
  else if ~_is_name_char(_at(data, p)) then xml_attrs_nil()
  else let
    val name_end = _scan_name(data, len, p + 1)
    val p2 = _skip_ws(data, len, name_end)
  in
    if p2 >= e then xml_attrs_nil()
    else if _at(data, p2) <> 61 then xml_attrs_nil()
    else let
      val p3 = _skip_ws(data, len, p2 + 1)
    in
      if p3 >= e then xml_attrs_nil()
      else let val quote = _at(data, p3) in
        if quote = 34 || quote = 39 then let
          val vs = p3 + 1
          val ve = _scan_quote(data, vs, e, quote)
          (* the rest starts past the closing quote; a value that runs to
             e ends the attributes *)
          val rest = (if ve < e then _parse_attrs(data, len, ve + 1, e) else xml_attrs_nil()): [s:nat] xml_attr_list(n, s)
        in xml_attrs_cons(p, name_end - p, vs, ve - vs, rest) end
        else xml_attrs_nil()
      end
    end
  end
end

(* ============================================================
   Recursive descent parser
   ============================================================ *)

(* The nodes from p up to a closing tag ("</") or the end, and where they
   stop. The metric is lexicographic: every recursive call either moves
   past at least one byte, or (the call to _parse_element at the same
   position) lowers the second component. *)
fun _parse_nodes {lb:agz}{n:pos}{p:nat | p <= n} .<n - p, 1>.
  (data: !$A.borrow(byte, lb, n), len: int n, p: int p)
  : [sz:nat][q:int | p <= q; q <= n] (xml_node_list(n, sz), int q) =
  if p >= len then (xml_nodes_nil(), p)
  else if _at(data, p) = 60 then
    if p + 1 >= len then (xml_nodes_nil(), p)
    else let val c2 = _at(data, p + 1) in
      if c2 = 33 then let
        (* <!-- comment -->, or <!DOCTYPE ...> and other declarations *)
        val next = (if p + 3 >= len then _skip_doctype(data, len, p + 2, 1)
          else if _at(data, p + 2) = 45 && _at(data, p + 3) = 45 then _skip_comment(data, len, p + 4)
          else _skip_doctype(data, len, p + 2, 1)): [q:int | p + 2 <= q; q <= n] int q
      in _parse_nodes(data, len, next) end
      else if c2 = 63 then _parse_nodes(data, len, _skip_pi(data, len, p + 2))
      else if c2 = 47 then (xml_nodes_nil(), p)
      else let
        val (node, next) = _parse_element(data, len, p)
        val (rest, q) = _parse_nodes(data, len, next)
      in (xml_nodes_cons(node, rest), q) end
    end
  else let
    (* text: at least the byte at p, which is not '<' *)
    val text_end = _scan_text(data, len, p + 1)
    val (rest, q) = _parse_nodes(data, len, text_end)
  in (xml_nodes_cons(xml_text(p, text_end - p), rest), q) end

(* The element whose '<' is at p, and the position just after it. *)
and _parse_element {lb:agz}{n:pos}{p:nat | p + 1 < n} .<n - p, 0>.
  (data: !$A.borrow(byte, lb, n), len: int n, p: int p)
  : [sz:pos][q:int | p < q; q <= n] (xml_node(n, sz), int q) = let
  val name_start = _skip_ws(data, len, p + 1)
  val name_end = _scan_name(data, len, name_start)
  val name_len = name_end - name_start
  val p2 = _skip_ws(data, len, name_end)
in
  case+ _find_tag_end(data, len, p2) of
  | tag_self(t) =>
      (xml_element(name_start, name_len, _parse_attrs(data, len, p2, t), xml_nodes_nil()), t + 2)
  | tag_eof() =>
      (xml_element(name_start, name_len, _parse_attrs(data, len, p2, len), xml_nodes_nil()), len)
  | tag_open(t) => let
      val attrs = _parse_attrs(data, len, p2, t)
      val (children, c) = _parse_nodes(data, len, t + 1)
      val node = xml_element(name_start, name_len, attrs, children)
    in
      (* past the closing tag "</name>", when it is there *)
      if c + 1 >= len then (node, c)
      else if _at(data, c) = 60 && _at(data, c + 1) = 47 then let
        val q = _skip_closing(data, len, c + 2)
      in (node, q) end
      else (node, c)
    end
end

implement parse_document {lb}{n} (data, len) = let
  val (nodes, _) = _parse_nodes(data, len, 0)
in nodes end

(* ============================================================
   Free -- termination metric is the size index
   ============================================================ *)

fun _free_attrs {n:int}{sa:nat} .<sa>.
  (attrs: xml_attr_list(n, sa)): void =
  case+ attrs of
  | ~xml_attrs_nil() => ()
  | ~xml_attrs_cons(_, _, _, _, rest) => _free_attrs(rest)

implement free_node {n}{sz} (node) =
  case+ node of
  | ~xml_element(_, _, attrs, children) => let
      val () = _free_attrs(attrs)
    in free_nodes(children) end
  | ~xml_text(_, _) => ()

implement free_nodes {n}{sz} (nodes) =
  case+ nodes of
  | ~xml_nodes_nil() => ()
  | ~xml_nodes_cons(node, rest) => let
      val () = free_node(node)
    in free_nodes(rest) end
