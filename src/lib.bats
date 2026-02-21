(* xml-tree -- recursive descent XML tree parser *)
(* Builds a tree of elements/text from XML bytes. *)
(* Tree nodes reference the input buffer (zero-copy). *)

#include "share/atspre_staload.hats"

#use arith as AR

(* ============================================================
   Types
   ============================================================ *)

#pub datavtype xml_node =
  | xml_element of (ptr, int, xml_attr_list, xml_node_list)
  | xml_text of (ptr, int)

#pub and xml_node_list =
  | xml_nodes_nil of ()
  | xml_nodes_cons of (xml_node, xml_node_list)

#pub and xml_attr_list =
  | xml_attrs_nil of ()
  | xml_attrs_cons of (ptr, int, ptr, int, xml_attr_list)

(* ============================================================
   Public API
   ============================================================ *)

#pub fun parse_document(data: ptr, data_len: int): xml_node_list

#pub fun free_nodes(nodes: xml_node_list): void

#pub fun free_node(node: xml_node): void

#pub fun serialize_nodes(nodes: !xml_node_list, buf: ptr, pos: int, max: int): int

#pub fun serialize_node(node: !xml_node, buf: ptr, pos: int, max: int): int

(* ============================================================
   C runtime helpers
   ============================================================ *)

$UNSAFE begin
%{#
static inline int _xml_buf_get_u8(void *p, int off) {
  return ((unsigned char*)p)[off];
}
static inline void _xml_buf_set_u8(void *p, int off, int v) {
  ((unsigned char*)p)[off] = (unsigned char)v;
}
%}
end

extern fun _buf_get_u8(p: ptr, off: int): int = "mac#_xml_buf_get_u8"
extern fun _buf_set_u8(p: ptr, off: int, v: int): void = "mac#_xml_buf_set_u8"
extern fun _ptr_add_int(p: ptr, n: int): ptr = "mac#atspre_add_ptr0_bsz"

(* Cast functions for linear type borrowing *)
extern castfn _ptr_to_nodes(p: ptr): xml_node_list
extern castfn _nodes_to_ptr(ns: xml_node_list): ptr
extern castfn _ptr_to_node(p: ptr): xml_node
extern castfn _node_to_ptr(n: xml_node): ptr
extern castfn _ptr_to_attrs(p: ptr): xml_attr_list
extern castfn _attrs_to_ptr(a: xml_attr_list): ptr
extern castfn _node_borrow_ptr(n: !xml_node): ptr
extern castfn _nodes_borrow_ptr(ns: !xml_node_list): ptr
extern castfn _attrs_borrow_ptr(a: !xml_attr_list): ptr

(* ============================================================
   Internal helpers
   ============================================================ *)

fn _is_ws(c: int): int =
  if $AR.eq_int_int(c, 32) then 1
  else if $AR.eq_int_int(c, 9) then 1
  else if $AR.eq_int_int(c, 10) then 1
  else if $AR.eq_int_int(c, 13) then 1
  else 0

fn _is_name_char(c: int): int =
  if $AR.gte_int_int(c, 97) then
    if $AR.gt_int_int(123, c) then 1 else 0
  else if $AR.gte_int_int(c, 65) then
    if $AR.gt_int_int(91, c) then 1 else 0
  else if $AR.gte_int_int(c, 48) then
    if $AR.gt_int_int(58, c) then 1 else 0
  else if $AR.eq_int_int(c, 95) then 1
  else if $AR.eq_int_int(c, 45) then 1
  else if $AR.eq_int_int(c, 46) then 1
  else if $AR.eq_int_int(c, 58) then 1
  else 0

fn _skip_ws(data: ptr, pos: int, len: int): int = let
  fun loop {k:nat} .<k>.
    (rem: int(k), p: int): int =
    if $AR.lte_g1(rem, 0) then p
    else if $AR.gte_int_int(p, len) then p
    else if $AR.eq_int_int(_is_ws(_buf_get_u8(data, p)), 1) then loop($AR.sub_g1(rem, 1), p + 1)
    else p
in loop($AR.checked_nat(len), pos) end

fn _skip_comment(data: ptr, pos: int, len: int): int = let
  fun loop {k:nat} .<k>.
    (rem: int(k), p: int): int =
    if $AR.lte_g1(rem, 0) then len
    else if $AR.gte_int_int(p + 2, len) then len
    else if $AR.eq_int_int(_buf_get_u8(data, p), 45) then
      if $AR.eq_int_int(_buf_get_u8(data, p + 1), 45) then
        if $AR.eq_int_int(_buf_get_u8(data, p + 2), 62) then p + 3
        else loop($AR.sub_g1(rem, 1), p + 1)
      else loop($AR.sub_g1(rem, 1), p + 1)
    else loop($AR.sub_g1(rem, 1), p + 1)
in loop($AR.checked_nat(len), pos) end

fn _skip_pi(data: ptr, pos: int, len: int): int = let
  fun loop {k:nat} .<k>.
    (rem: int(k), p: int): int =
    if $AR.lte_g1(rem, 0) then len
    else if $AR.gte_int_int(p + 1, len) then len
    else if $AR.eq_int_int(_buf_get_u8(data, p), 63) then
      if $AR.eq_int_int(_buf_get_u8(data, p + 1), 62) then p + 2
      else loop($AR.sub_g1(rem, 1), p + 1)
    else loop($AR.sub_g1(rem, 1), p + 1)
in loop($AR.checked_nat(len), pos) end

fn _skip_doctype(data: ptr, pos: int, len: int): int = let
  fun loop {k:nat} .<k>.
    (rem: int(k), p: int, depth: int): int =
    if $AR.lte_g1(rem, 0) then len
    else if $AR.gte_int_int(p, len) then len
    else let val c = _buf_get_u8(data, p) in
      if $AR.eq_int_int(c, 60) then loop($AR.sub_g1(rem, 1), p + 1, depth + 1)
      else if $AR.eq_int_int(c, 62) then
        (if $AR.eq_int_int(depth, 1) then p + 1 else loop($AR.sub_g1(rem, 1), p + 1, $AR.sub_int_int(depth, 1)))
      else loop($AR.sub_g1(rem, 1), p + 1, depth)
    end
in loop($AR.checked_nat(len), pos, 1) end

fn _copy_bytes(src: ptr, src_off: int, dst: ptr, dst_off: int, count: int, max: int): void = let
  fun loop {k:nat} .<k>.
    (rem: int(k), i: int): void =
    if $AR.lte_g1(rem, 0) then ()
    else if $AR.gte_int_int(i, count) then ()
    else if $AR.gte_int_int(dst_off + i, max) then ()
    else let
      val () = _buf_set_u8(dst, dst_off + i, _buf_get_u8(src, src_off + i))
    in loop($AR.sub_g1(rem, 1), i + 1) end
in loop($AR.checked_nat(count), 0) end

(* ============================================================
   Attribute parser
   ============================================================ *)

fun _parse_attrs {k:nat} .<k>.
  (rem: int(k), data: ptr, pos: int, end_pos: int): (xml_attr_list, int) = let
  val p = _skip_ws(data, pos, end_pos)
in
  if $AR.lte_g1(rem, 0) then (xml_attrs_nil(), p)
  else if $AR.gte_int_int(p, end_pos) then (xml_attrs_nil(), p)
  else if $AR.eq_int_int(_is_name_char(_buf_get_u8(data, p)), 0) then (xml_attrs_nil(), p)
  else let
    val name_start = p
    fun scan_name {j:nat} .<j>.
      (jrem: int(j), p2: int): int =
      if $AR.lte_g1(jrem, 0) then p2
      else if $AR.gte_int_int(p2, end_pos) then p2
      else if $AR.eq_int_int(_is_name_char(_buf_get_u8(data, p2)), 1) then scan_name($AR.sub_g1(jrem, 1), p2 + 1)
      else p2
    val name_end = scan_name($AR.checked_nat(end_pos), p)
    val name_len = $AR.sub_int_int(name_end, name_start)
    val name_ptr = _ptr_add_int(data, name_start)
    val p2 = _skip_ws(data, name_end, end_pos)
  in
    if $AR.gte_int_int(p2, end_pos) then (xml_attrs_nil(), p2)
    else if $AR.eq_int_int(_buf_get_u8(data, p2), 61) then let
      val p3 = _skip_ws(data, p2 + 1, end_pos)
    in
      if $AR.gte_int_int(p3, end_pos) then (xml_attrs_nil(), p3)
      else let val quote = _buf_get_u8(data, p3) in
        if $AR.eq_int_int(quote, 34) then let
          val vs = p3 + 1
          fun scan_dq {j:nat} .<j>.
            (jrem: int(j), p4: int): int =
            if $AR.lte_g1(jrem, 0) then p4
            else if $AR.gte_int_int(p4, end_pos) then p4
            else if $AR.eq_int_int(_buf_get_u8(data, p4), 34) then p4
            else scan_dq($AR.sub_g1(jrem, 1), p4 + 1)
          val ve = scan_dq($AR.checked_nat(end_pos), vs)
          val vl = $AR.sub_int_int(ve, vs)
          val vp = _ptr_add_int(data, vs)
          val np = if $AR.gt_int_int(end_pos, ve) then ve + 1 else ve
          val (rest, fp) = _parse_attrs($AR.sub_g1(rem, 1), data, np, end_pos)
        in (xml_attrs_cons(name_ptr, name_len, vp, vl, rest), fp) end
        else if $AR.eq_int_int(quote, 39) then let
          val vs = p3 + 1
          fun scan_sq {j:nat} .<j>.
            (jrem: int(j), p4: int): int =
            if $AR.lte_g1(jrem, 0) then p4
            else if $AR.gte_int_int(p4, end_pos) then p4
            else if $AR.eq_int_int(_buf_get_u8(data, p4), 39) then p4
            else scan_sq($AR.sub_g1(jrem, 1), p4 + 1)
          val ve = scan_sq($AR.checked_nat(end_pos), vs)
          val vl = $AR.sub_int_int(ve, vs)
          val vp = _ptr_add_int(data, vs)
          val np = if $AR.gt_int_int(end_pos, ve) then ve + 1 else ve
          val (rest, fp) = _parse_attrs($AR.sub_g1(rem, 1), data, np, end_pos)
        in (xml_attrs_cons(name_ptr, name_len, vp, vl, rest), fp) end
        else (xml_attrs_nil(), p3)
      end
    end
    else (xml_attrs_nil(), p2)
  end
end

(* ============================================================
   Recursive descent parser
   ============================================================ *)

fun _parse_nodes {k:nat} .<k>.
  (rem: int(k), data: ptr, pos: int, len: int): (xml_node_list, int) = let
  val p = _skip_ws(data, pos, len)
in
  if $AR.lte_g1(rem, 0) then (xml_nodes_nil(), p)
  else if $AR.gte_int_int(p, len) then (xml_nodes_nil(), p)
  else let val c = _buf_get_u8(data, p) in
    if $AR.eq_int_int(c, 60) then
      if $AR.gte_int_int(p + 1, len) then (xml_nodes_nil(), p)
      else let val c2 = _buf_get_u8(data, p + 1) in
        if $AR.eq_int_int(c2, 33) then let
          val new_pos =
            if $AR.gte_int_int(p + 3, len) then _skip_doctype(data, p + 2, len)
            else if $AR.eq_int_int(_buf_get_u8(data, p + 2), 45) then
              if $AR.eq_int_int(_buf_get_u8(data, p + 3), 45) then _skip_comment(data, p + 4, len)
              else _skip_doctype(data, p + 2, len)
            else _skip_doctype(data, p + 2, len)
        in _parse_nodes($AR.sub_g1(rem, 1), data, new_pos, len) end
        else if $AR.eq_int_int(c2, 63) then
          _parse_nodes($AR.sub_g1(rem, 1), data, _skip_pi(data, p + 2, len), len)
        else if $AR.eq_int_int(c2, 47) then
          (xml_nodes_nil(), p)
        else let
          val r1 = $AR.sub_g1(rem, 1)
          val (node, new_pos) = _parse_element(r1, data, p, len)
          val (rest, final_pos) = _parse_nodes(r1, data, new_pos, len)
        in (xml_nodes_cons(node, rest), final_pos) end
      end
    else let
      val text_start = p
      fun scan_text {j:nat} .<j>.
        (jrem: int(j), p2: int): int =
        if $AR.lte_g1(jrem, 0) then p2
        else if $AR.gte_int_int(p2, len) then p2
        else if $AR.eq_int_int(_buf_get_u8(data, p2), 60) then p2
        else scan_text($AR.sub_g1(jrem, 1), p2 + 1)
      val text_end = scan_text($AR.checked_nat(len), p)
      val text_len = $AR.sub_int_int(text_end, text_start)
      val text_ptr = _ptr_add_int(data, text_start)
      val (rest, final_pos) = _parse_nodes($AR.sub_g1(rem, 1), data, text_end, len)
    in (xml_nodes_cons(xml_text(text_ptr, text_len), rest), final_pos) end
  end
end

and _parse_element {k:nat} .<k>.
  (rem: int(k), data: ptr, pos: int, len: int): (xml_node, int) = let
  val p = pos + 1
  val p = _skip_ws(data, p, len)
  val name_start = p
  fun scan_name {j:nat} .<j>.
    (jrem: int(j), p2: int): int =
    if $AR.lte_g1(jrem, 0) then p2
    else if $AR.gte_int_int(p2, len) then p2
    else if $AR.eq_int_int(_is_name_char(_buf_get_u8(data, p2)), 1) then scan_name($AR.sub_g1(jrem, 1), p2 + 1)
    else p2
  val name_end = scan_name($AR.checked_nat(len), p)
  val name_len = $AR.sub_int_int(name_end, name_start)
  val name_ptr = _ptr_add_int(data, name_start)
  val p2 = _skip_ws(data, name_end, len)
  fun find_tag_end {j:nat} .<j>.
    (jrem: int(j), p3: int): (int, int) =
    if $AR.lte_g1(jrem, 0) then (p3, 0)
    else if $AR.gte_int_int(p3, len) then (p3, 0)
    else let val c = _buf_get_u8(data, p3) in
      if $AR.eq_int_int(c, 62) then (p3, 0)
      else if $AR.eq_int_int(c, 47) then
        if $AR.gt_int_int(len, p3 + 1) then
          if $AR.eq_int_int(_buf_get_u8(data, p3 + 1), 62) then (p3, 1)
          else find_tag_end($AR.sub_g1(jrem, 1), p3 + 1)
        else (p3, 0)
      else if $AR.eq_int_int(c, 34) then let
        fun skip_dq {j2:nat} .<j2>.
          (j2rem: int(j2), p4: int): int =
          if $AR.lte_g1(j2rem, 0) then p4
          else if $AR.gte_int_int(p4, len) then p4
          else if $AR.eq_int_int(_buf_get_u8(data, p4), 34) then p4 + 1
          else skip_dq($AR.sub_g1(j2rem, 1), p4 + 1)
      in find_tag_end($AR.sub_g1(jrem, 1), skip_dq($AR.checked_nat(len), p3 + 1)) end
      else if $AR.eq_int_int(c, 39) then let
        fun skip_sq {j2:nat} .<j2>.
          (j2rem: int(j2), p4: int): int =
          if $AR.lte_g1(j2rem, 0) then p4
          else if $AR.gte_int_int(p4, len) then p4
          else if $AR.eq_int_int(_buf_get_u8(data, p4), 39) then p4 + 1
          else skip_sq($AR.sub_g1(j2rem, 1), p4 + 1)
      in find_tag_end($AR.sub_g1(jrem, 1), skip_sq($AR.checked_nat(len), p3 + 1)) end
      else find_tag_end($AR.sub_g1(jrem, 1), p3 + 1)
    end
  val (tag_end_pos, is_self) = find_tag_end($AR.checked_nat(len), p2)
  val (attrs, _) = _parse_attrs($AR.checked_nat(len), data, p2, tag_end_pos)
  val after_tag =
    if $AR.eq_int_int(is_self, 1) then tag_end_pos + 2
    else tag_end_pos + 1
in
  if $AR.eq_int_int(is_self, 1) then
    (xml_element(name_ptr, name_len, attrs, xml_nodes_nil()), after_tag)
  else if $AR.lte_g1(rem, 0) then
    (xml_element(name_ptr, name_len, attrs, xml_nodes_nil()), after_tag)
  else let
    val (children, child_end_pos) = _parse_nodes($AR.sub_g1(rem, 1), data, after_tag, len)
    fun skip_closing {j:nat} .<j>.
      (jrem: int(j), p3: int): int =
      if $AR.lte_g1(jrem, 0) then p3
      else if $AR.gte_int_int(p3, len) then p3
      else if $AR.eq_int_int(_buf_get_u8(data, p3), 62) then p3 + 1
      else skip_closing($AR.sub_g1(jrem, 1), p3 + 1)
    val final_pos =
      if $AR.gte_int_int(child_end_pos, len) then child_end_pos
      else if $AR.eq_int_int(_buf_get_u8(data, child_end_pos), 60) then
        if $AR.gte_int_int(child_end_pos + 1, len) then child_end_pos
        else if $AR.eq_int_int(_buf_get_u8(data, child_end_pos + 1), 47) then
          skip_closing($AR.checked_nat(len), child_end_pos + 2)
        else child_end_pos
      else child_end_pos
  in (xml_element(name_ptr, name_len, attrs, children), final_pos) end
end

(* ============================================================
   Public implementations
   ============================================================ *)

implement parse_document(data, data_len) = let
  val (nodes, _) = _parse_nodes($AR.checked_nat(data_len), data, 0, data_len)
in nodes end

fun _free_attrs(attrs: xml_attr_list): void =
  case+ attrs of
  | ~xml_attrs_nil() => ()
  | ~xml_attrs_cons(_, _, _, _, rest) => _free_attrs(rest)

implement free_node(node) =
  case+ node of
  | ~xml_element(_, _, attrs, children) => let
      val () = _free_attrs(attrs)
    in free_nodes(children) end
  | ~xml_text(_, _) => ()

implement free_nodes(nodes) =
  case+ nodes of
  | ~xml_nodes_nil() => ()
  | ~xml_nodes_cons(node, rest) => let
      val () = free_node(node)
    in free_nodes(rest) end

(* ============================================================
   Serializer
   ============================================================ *)

extern fun _serialize_attrs_b(attrs: !xml_attr_list, buf: ptr, pos: int, max: int): int

implement serialize_node(node, buf, pos, max) = let
  val np = _node_borrow_ptr(node)
  val node2 = _ptr_to_node(np)
in
  case+ node2 of
  | xml_element(name, nlen, attrs, children) => let
      val () = if $AR.gt_int_int(max, pos) then _buf_set_u8(buf, pos, 60)
      val p = pos + 1
      val () = _copy_bytes(name, 0, buf, p, nlen, max)
      val p = p + nlen
      val ap = _attrs_borrow_ptr(attrs)
      val a2 = _ptr_to_attrs(ap)
      val p = _serialize_attrs_b(a2, buf, p, max)
      val _ = _attrs_to_ptr(a2)
      val () = if $AR.gt_int_int(max, p) then _buf_set_u8(buf, p, 62)
      val p = p + 1
      val cp = _nodes_borrow_ptr(children)
      val c2 = _ptr_to_nodes(cp)
      val p = serialize_nodes(c2, buf, p, max)
      val _ = _nodes_to_ptr(c2)
      val () = if $AR.gt_int_int(max, p) then _buf_set_u8(buf, p, 60)
      val p = p + 1
      val () = if $AR.gt_int_int(max, p) then _buf_set_u8(buf, p, 47)
      val p = p + 1
      val () = _copy_bytes(name, 0, buf, p, nlen, max)
      val p = p + nlen
      val () = if $AR.gt_int_int(max, p) then _buf_set_u8(buf, p, 62)
      val _ = _node_to_ptr(node2)
    in p + 1 end
  | xml_text(text, tlen) => let
      val () = _copy_bytes(text, 0, buf, pos, tlen, max)
      val _ = _node_to_ptr(node2)
    in pos + tlen end
end

implement serialize_nodes(nodes, buf, pos, max) = let
  val np = _nodes_borrow_ptr(nodes)
  val nodes2 = _ptr_to_nodes(np)
in
  case+ nodes2 of
  | xml_nodes_nil() => let
      val _ = _nodes_to_ptr(nodes2)
    in pos end
  | xml_nodes_cons(node, rest) => let
      val np2 = _node_borrow_ptr(node)
      val rp2 = _nodes_borrow_ptr(rest)
      val _ = _nodes_to_ptr(nodes2)
      val n3 = _ptr_to_node(np2)
      val p = serialize_node(n3, buf, pos, max)
      val _ = _node_to_ptr(n3)
      val r3 = _ptr_to_nodes(rp2)
      val p2 = serialize_nodes(r3, buf, p, max)
      val _ = _nodes_to_ptr(r3)
    in p2 end
end

implement _serialize_attrs_b(attrs, buf, pos, max) = let
  val ap = _attrs_borrow_ptr(attrs)
  val attrs2 = _ptr_to_attrs(ap)
in
  case+ attrs2 of
  | xml_attrs_nil() => let
      val _ = _attrs_to_ptr(attrs2)
    in pos end
  | xml_attrs_cons(name, nlen, vp, vlen, rest) => let
      val () = if $AR.gt_int_int(max, pos) then _buf_set_u8(buf, pos, 32)
      val p = pos + 1
      val () = _copy_bytes(name, 0, buf, p, nlen, max)
      val p = p + nlen
      val () = if $AR.gt_int_int(max, p) then _buf_set_u8(buf, p, 61)
      val p = p + 1
      val () = if $AR.gt_int_int(max, p) then _buf_set_u8(buf, p, 34)
      val p = p + 1
      val () = _copy_bytes(vp, 0, buf, p, vlen, max)
      val p = p + vlen
      val () = if $AR.gt_int_int(max, p) then _buf_set_u8(buf, p, 34)
      val p = p + 1
      val rp = _attrs_borrow_ptr(rest)
      val _ = _attrs_to_ptr(attrs2)
      val r2 = _ptr_to_attrs(rp)
      val p2 = _serialize_attrs_b(r2, buf, p, max)
      val _ = _attrs_to_ptr(r2)
    in p2 end
end
