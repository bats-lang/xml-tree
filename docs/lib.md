# lib

### `datavtype xml_node(sz:int) =
  | {sa:nat}{sc:nat}
    xml_element(1+sa+sc) of (int, int, xml_attr_list(sa), xml_node_list(sc))
  | xml_text(1) of (int, int)`

### `and xml_node_list(sz:int) =
  | xml_nodes_nil(0) of ()
  | {s1:pos}{s2:nat}
    xml_nodes_cons(s1+s2) of (xml_node(s1), xml_node_list(s2))`

### `and xml_attr_list(sz:int) =
  | xml_attrs_nil(0) of ()
  | {s1:nat}
    xml_attrs_cons(1+s1) of (int, int, int, int, xml_attr_list(s1))`

### `fun parse_document
  {lb:agz}{n:pos}
  (data: !$A.borrow(byte, lb, n), len: int n): [sz:nat] xml_node_list(sz)`

### `fun free_nodes {sz:nat} (nodes: xml_node_list(sz)): void`

### `fun free_node {sz:pos} (node: xml_node(sz)): void`
