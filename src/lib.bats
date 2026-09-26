(* xml-tree -- recursive descent XML tree parser *)
(* Nodes store integer offsets into the input buffer. *)
(* Size-indexed datavtypes for proven-terminating free. *)
(* No $UNSAFE. *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR

(* ============================================================
   Types -- size-indexed for termination proofs
   ============================================================ *)

#pub datavtype xml_node(sz:int) =
  | {sa:nat}{sc:nat}
    xml_element(1+sa+sc) of (int, int, xml_attr_list(sa), xml_node_list(sc))
  | xml_text(1) of (int, int)

#pub and xml_node_list(sz:int) =
  | xml_nodes_nil(0) of ()
  | {s1:pos}{s2:nat}
    xml_nodes_cons(s1+s2) of (xml_node(s1), xml_node_list(s2))

#pub and xml_attr_list(sz:int) =
  | xml_attrs_nil(0) of ()
  | {s1:nat}
    xml_attrs_cons(1+s1) of (int, int, int, int, xml_attr_list(s1))

(* ============================================================
   Public API
   ============================================================ *)

#pub fun parse_document
  {lb:agz}{n:pos}
  (data: !$A.borrow(byte, lb, n), len: int n): [sz:nat] xml_node_list(sz)

#pub fun free_nodes {sz:nat} (nodes: xml_node_list(sz)): void

#pub fun free_node {sz:pos} (node: xml_node(sz)): void

(* ============================================================
   Safe byte read
   ============================================================ *)

(* A position in the input: an indexed int of statically unknown
   value. Keeping positions indexed lets comparisons with the length
   prove reads, instead of casting. *)
typedef pos_t = [x:int] int x

(* Byte at off, or ~1 outside the buffer. Positions are indexed ints
   throughout this file, so these two comparisons prove the read. *)
fn _peek {lb:agz}{n:pos}{o:int}
  (data: !$A.borrow(byte, lb, n), off: int o, len: int n): int =
  if off >= 0 then
    if off < len then byte2int0($A.read<byte>(data, off))
    else ~1
  else ~1

fn _is_ws(c: int): int =
  if c = 32 then 1 else if c = 9 then 1 else if c = 10 then 1 else if c = 13 then 1 else 0

fn _is_name_char(c: int): int =
  if c >= 97 then (if c < 123 then 1 else 0)
  else if c >= 65 then (if c < 91 then 1 else 0)
  else if c = 58 then 1
  else if c >= 48 then (if c < 58 then 1 else 0)
  else if c = 95 then 1 else if c = 45 then 1 else if c = 46 then 1 else 0

(* ============================================================
   Scanning helpers
   ============================================================ *)

fun _skip_ws {lb:agz}{n:pos}{k:nat} .<k>.
  (data: !$A.borrow(byte, lb, n), len: int n, rem: int(k), p: pos_t): pos_t =
  if rem <= 0 then p
  else if p >= len then p
  else if _is_ws(_peek(data, p, len)) = 1 then _skip_ws(data, len, rem - 1, p + 1)
  else p

fun _skip_comment {lb:agz}{n:pos}{k:nat} .<k>.
  (data: !$A.borrow(byte, lb, n), len: int n, rem: int(k), p: pos_t): pos_t =
  if rem <= 0 then len
  else if p + 2 >= len then len
  else if _peek(data, p, len) = 45 then
    if _peek(data, p + 1, len) = 45 then
      if _peek(data, p + 2, len) = 62 then p + 3
      else _skip_comment(data, len, rem - 1, p + 1)
    else _skip_comment(data, len, rem - 1, p + 1)
  else _skip_comment(data, len, rem - 1, p + 1)

fun _skip_pi {lb:agz}{n:pos}{k:nat} .<k>.
  (data: !$A.borrow(byte, lb, n), len: int n, rem: int(k), p: pos_t): pos_t =
  if rem <= 0 then len
  else if p + 1 >= len then len
  else if _peek(data, p, len) = 63 then
    if _peek(data, p + 1, len) = 62 then p + 2
    else _skip_pi(data, len, rem - 1, p + 1)
  else _skip_pi(data, len, rem - 1, p + 1)

fun _skip_doctype {lb:agz}{n:pos}{k:nat} .<k>.
  (data: !$A.borrow(byte, lb, n), len: int n, rem: int(k), p: pos_t, depth: int): pos_t =
  if rem <= 0 then len
  else if p >= len then len
  else let val c = _peek(data, p, len) in
    if c = 60 then _skip_doctype(data, len, rem - 1, p + 1, depth + 1)
    else if c = 62 then
      (if depth = 1 then p + 1 else _skip_doctype(data, len, rem - 1, p + 1, depth - 1))
    else _skip_doctype(data, len, rem - 1, p + 1, depth)
  end

fun _scan_name {lb:agz}{n:pos}{k:nat} .<k>.
  (data: !$A.borrow(byte, lb, n), len: int n, rem: int(k), p: pos_t): pos_t =
  if rem <= 0 then p
  else if p >= len then p
  else if _is_name_char(_peek(data, p, len)) = 1 then _scan_name(data, len, rem - 1, p + 1)
  else p

(* ============================================================
   Attribute parser
   ============================================================ *)

fun _parse_attrs {lb:agz}{n:pos}{k:nat} .<k>.
  (data: !$A.borrow(byte, lb, n), len: int n,
   rem: int(k), pos: pos_t, end_pos: pos_t): [sa:nat] (xml_attr_list(sa), pos_t) = let
  val p = _skip_ws(data, len, len, pos)
in
  if rem <= 0 then (xml_attrs_nil(), p)
  else if p >= end_pos then (xml_attrs_nil(), p)
  else if _is_name_char(_peek(data, p, len)) = 0 then (xml_attrs_nil(), p)
  else let
    val name_start = p
    val name_end = _scan_name(data, len, len, p)
    val name_len = name_end - name_start
    val p2 = _skip_ws(data, len, len, name_end)
  in
    if p2 >= end_pos then (xml_attrs_nil(), p2)
    else if _peek(data, p2, len) = 61 then let
      val p3 = _skip_ws(data, len, len, p2 + 1)
    in
      if p3 >= end_pos then (xml_attrs_nil(), p3)
      else let val quote = _peek(data, p3, len) in
        if quote = 34 orelse quote = 39 then let
          val vs = p3 + 1
          fun scan_q {lb:agz}{n:pos}{j:nat} .<j>.
            (data: !$A.borrow(byte, lb, n), len: int n,
             jrem: int(j), p4: pos_t, q: int): pos_t =
            if jrem <= 0 then p4
            else if p4 >= end_pos then p4
            else if _peek(data, p4, len) = q then p4
            else scan_q(data, len, jrem - 1, p4 + 1, q)
          val ve = scan_q(data, len, len, vs, quote)
          val vl = ve - vs
          val np = (if end_pos > ve then ve + 1 else ve): pos_t
          val (rest, fp) = _parse_attrs(data, len, rem - 1, np, end_pos)
        in (xml_attrs_cons(name_start, name_len, vs, vl, rest), fp) end
        else (xml_attrs_nil(), p3)
      end
    end
    else (xml_attrs_nil(), p2)
  end
end

(* ============================================================
   Recursive descent parser
   ============================================================ *)

fun _parse_nodes {lb:agz}{n:pos}{k:nat} .<k>.
  (data: !$A.borrow(byte, lb, n), len: int n,
   rem: int(k), pos: pos_t): [sz:nat] (xml_node_list(sz), pos_t) = let
  val p = pos
in
  if rem <= 0 then (xml_nodes_nil(), p)
  else if p >= len then (xml_nodes_nil(), p)
  else let val c = _peek(data, p, len) in
    if c = 60 then
      if p + 1 >= len then (xml_nodes_nil(), p)
      else let val c2 = _peek(data, p + 1, len) in
        if c2 = 33 then let
          val new_pos: pos_t =
            if p + 3 >= len then _skip_doctype(data, len, len, p + 2, 1)
            else if _peek(data, p + 2, len) = 45 then
              if _peek(data, p + 3, len) = 45 then _skip_comment(data, len, len, p + 4)
              else _skip_doctype(data, len, len, p + 2, 1)
            else _skip_doctype(data, len, len, p + 2, 1)
        in _parse_nodes(data, len, rem - 1, new_pos) end
        else if c2 = 63 then
          _parse_nodes(data, len, rem - 1, _skip_pi(data, len, len, p + 2))
        else if c2 = 47 then
          (xml_nodes_nil(), p)
        else let
          val (node, new_pos) = _parse_element(data, len, rem - 1, p)
          val (rest, final_pos) = _parse_nodes(data, len, rem - 1, new_pos)
        in (xml_nodes_cons(node, rest), final_pos) end
      end
    else let
      val text_start = p
      fun scan_text {lb:agz}{n:pos}{j:nat} .<j>.
        (data: !$A.borrow(byte, lb, n), len: int n,
         jrem: int(j), p2: pos_t): pos_t =
        if jrem <= 0 then p2
        else if p2 >= len then p2
        else if _peek(data, p2, len) = 60 then p2
        else scan_text(data, len, jrem - 1, p2 + 1)
      val text_end = scan_text(data, len, len, p)
      val text_len = text_end - text_start
      val (rest, final_pos) = _parse_nodes(data, len, rem - 1, text_end)
    in (xml_nodes_cons(xml_text(text_start, text_len), rest), final_pos) end
  end
end

and _parse_element {lb:agz}{n:pos}{k:nat} .<k>.
  (data: !$A.borrow(byte, lb, n), len: int n,
   rem: int(k), pos: pos_t): [sz:pos] (xml_node(sz), pos_t) = let
  val p = _skip_ws(data, len, len, pos + 1)
  val name_start = p
  val name_end = _scan_name(data, len, len, p)
  val name_len = name_end - name_start
  val p2 = _skip_ws(data, len, len, name_end)
  fun find_tag_end {lb:agz}{n:pos}{j:nat} .<j>.
    (data: !$A.borrow(byte, lb, n), len: int n,
     jrem: int(j), p3: pos_t): @(pos_t, int) =
    if jrem <= 0 then @(p3, 0)
    else if p3 >= len then @(p3, 0)
    else let val c = _peek(data, p3, len) in
      if c = 62 then @(p3, 0)
      else if c = 47 then
        if len > p3 + 1 then
          if _peek(data, p3 + 1, len) = 62 then @(p3, 1)
          else find_tag_end(data, len, jrem - 1, p3 + 1)
        else @(p3, 0)
      else if c = 34 then let
        fun skip_dq {lb:agz}{n:pos}{j2:nat} .<j2>.
          (data: !$A.borrow(byte, lb, n), len: int n, j2rem: int(j2), p4: pos_t): pos_t =
          if j2rem <= 0 then p4 else if p4 >= len then p4
          else if _peek(data, p4, len) = 34 then p4 + 1
          else skip_dq(data, len, j2rem - 1, p4 + 1)
      in find_tag_end(data, len, jrem - 1, skip_dq(data, len, len, p3 + 1)) end
      else if c = 39 then let
        fun skip_sq {lb:agz}{n:pos}{j2:nat} .<j2>.
          (data: !$A.borrow(byte, lb, n), len: int n, j2rem: int(j2), p4: pos_t): pos_t =
          if j2rem <= 0 then p4 else if p4 >= len then p4
          else if _peek(data, p4, len) = 39 then p4 + 1
          else skip_sq(data, len, j2rem - 1, p4 + 1)
      in find_tag_end(data, len, jrem - 1, skip_sq(data, len, len, p3 + 1)) end
      else find_tag_end(data, len, jrem - 1, p3 + 1)
    end
  val @(tag_end_pos, is_self) = find_tag_end(data, len, len, p2)
  val (attrs, _) = _parse_attrs(data, len, len, p2, tag_end_pos)
  val after_tag = (if is_self = 1 then tag_end_pos + 2 else tag_end_pos + 1): pos_t
in
  if is_self = 1 then
    (xml_element(name_start, name_len, attrs, xml_nodes_nil()), after_tag)
  else if rem <= 0 then
    (xml_element(name_start, name_len, attrs, xml_nodes_nil()), after_tag)
  else let
    val (children, child_end_pos) = _parse_nodes(data, len, rem - 1, after_tag)
    fun skip_closing {lb:agz}{n:pos}{j:nat} .<j>.
      (data: !$A.borrow(byte, lb, n), len: int n, jrem: int(j), p3: pos_t): pos_t =
      if jrem <= 0 then p3 else if p3 >= len then p3
      else if _peek(data, p3, len) = 62 then p3 + 1
      else skip_closing(data, len, jrem - 1, p3 + 1)
    val final_pos: pos_t =
      if child_end_pos >= len then child_end_pos
      else if _peek(data, child_end_pos, len) = 60 then
        if child_end_pos + 1 >= len then child_end_pos
        else if _peek(data, child_end_pos + 1, len) = 47 then
          skip_closing(data, len, len, child_end_pos + 2)
        else child_end_pos
      else child_end_pos
  in (xml_element(name_start, name_len, attrs, children), final_pos) end
end

(* ============================================================
   Free -- termination metric is the size index
   ============================================================ *)

implement parse_document {lb}{n} (data, len) = let
  val (nodes, _) = _parse_nodes(data, len, len, 0)
in nodes end

fun _free_attrs {sa:nat} .<sa>.
  (attrs: xml_attr_list(sa)): void =
  case+ attrs of
  | ~xml_attrs_nil() => ()
  | ~xml_attrs_cons(_, _, _, _, rest) => _free_attrs(rest)

implement free_node {sz} (node) =
  case+ node of
  | ~xml_element(_, _, attrs, children) => let
      val () = _free_attrs(attrs)
    in free_nodes(children) end
  | ~xml_text(_, _) => ()

implement free_nodes {sz} (nodes) =
  case+ nodes of
  | ~xml_nodes_nil() => ()
  | ~xml_nodes_cons(node, rest) => let
      val () = free_node(node)
    in free_nodes(rest) end
