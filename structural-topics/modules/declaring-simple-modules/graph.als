module graph

pred dag [node: set univ, r: node->node] {
  all n: node | n not in n.^r
}

pred rootedAt[node: set univ, r: node->node, root: node] {
  node in root.*r
}
