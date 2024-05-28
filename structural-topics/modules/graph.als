module graph[node]


/*
pred dag [node: set univ, r: node->node] {
  all n: node | n not in n.^r
}

pred rootedAt[node: set univ, r: node->node, root: node] {
  node in root.*r
}
*/

pred dag [r: node->node] {
  all n: node | n not in n.^r
}

pred rootedAt [r: node->node, root: node] {
  node in root.*r
}

pred forest [r: node->node] {
  dag[r]
  all n: node | lone r.n
}


run dag_example { some r:node->node | dag[r] } for exactly 4 node
