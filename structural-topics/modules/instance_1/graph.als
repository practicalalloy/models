module graph[node]

pred dag [r: node -> node] {
  all n: node | n not in n.^r
}

pred rootedAt [r: node -> node, root: node] {
  node in root.*r
}

run dag_example { 
  some r: node -> node | dag[r] 
} for exactly 4 node

run book_instance_1 {
  some disj n0, n1, n2, n3 : node, r: node -> node {
    node = n0 + n1 + n2 + n3
    r = n0 -> n1 + n0 -> n2 + n1 -> n3 + n2 -> n3
  }
} for exactly 4 node
