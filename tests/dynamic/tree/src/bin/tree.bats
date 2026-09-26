#include "share/atspre_staload.hats"
#use array as A
#use str as S
#use xml-tree as X

(* Parses documents and folds each tree into a checksum over every
   element name, attribute and text span (offsets and lengths, weighted
   by position in the walk), plus a node count. Exact values are pinned;
   truncated inputs must parse without reading out of bounds.
   Exits 1 on any mismatch. *)
fun walk_attrs {s:nat} .<s>. (a: !$X.xml_attr_list(s), acc: int, k: int): @(int, int) =
  case+ a of
  | $X.xml_attrs_nil() => @(acc, k)
  | $X.xml_attrs_cons(ns, nl, vs, vl, rest) =>
      walk_attrs(rest, acc + k * (ns + 3 * nl + 5 * vs + 7 * vl), k + 1)

fun walk_nodes {s:nat} .<s, 1>. (l: !$X.xml_node_list(s), acc: int, k: int): @(int, int) =
  case+ l of
  | $X.xml_nodes_nil() => @(acc, k)
  | $X.xml_nodes_cons(node, rest) => let
      val @(a2, k2) = walk_node(node, acc, k)
    in walk_nodes(rest, a2, k2) end

and walk_node {s:pos} .<s, 0>. (n: !$X.xml_node(s), acc: int, k: int): @(int, int) =
  case+ n of
  | $X.xml_text(ts, tl) => @(acc + k * (11 * ts + 13 * tl), k + 1)
  | $X.xml_element(ns, nl, attrs, kids) => let
      val a1 = acc + k * (17 * ns + 19 * nl)
      val @(a2, k2) = walk_attrs(attrs, a1, k + 1)
    in walk_nodes(kids, a2, k2) end

fn run {m:pos | m <= 1048576} (name: string, src: &(@[char][m]), m: int m, want_sum: int, want_nodes: int): bool = let
  val @(f, b) = $A.freeze<byte>($S.from_char_array(src, m))
  val nodes = $X.parse_document(b, m)
  val @(sum, cnt) = walk_nodes(nodes, 0, 1)
  val () = $X.free_nodes(nodes)
  val () = $A.drop<byte>(f, b)
  val () = $A.free<byte>($A.thaw<byte>(f))
  val ok = sum = want_sum && cnt = want_nodes
  val () = (if ok then () else println! ("FAIL ", name, ": sum ", sum, " count ", cnt))
in ok end

implement main0 () = let
  (* <a x="1" y='2'><b/>hi<!--c--><?p?></a> *)
  var d1 = @[char][40]('<', 'a', ' ', 'x', '=', '\042', '1', '\042', ' ', 'y', '=', '\047', '2', '\047', '>', '<', 'b', '/', '>', 'h', 'i', '<', '!', '-', '-', 'c', '-', '-', '>', '<', '?', 'p', '?', '>', '<', '/', 'a', '>', ' ', ' ')
  (* truncated inside an attribute value: <a x="1 *)
  var d2 = @[char][7]('<', 'a', ' ', 'x', '=', '\042', '1')
  (* truncated inside a comment: <!--ab *)
  var d3 = @[char][6]('<', '!', '-', '-', 'a', 'b')
  (* text only *)
  var d4 = @[char][3]('t', 'x', 't')
  val r1 = run("document", d1, 40, 5362, 7)
  val r2 = run("truncated attribute", d2, 7, 122, 3)
  val r3 = run("truncated comment", d3, 6, 0, 1)
  val r4 = run("text only", d4, 3, 39, 2)
in
  if r1 && r2 && r3 && r4 then println! ("tree: all cases pass")
  else exit_void(1)
end
