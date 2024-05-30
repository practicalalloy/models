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

run book_instance1 {
  some disj o0, o1, o2, o3 : univ, r: node -> node {
    node = o0 + o1 + o2 + o3
    univ = node + Int
    r = o0 -> o1 + o0 -> o2 + o1 -> o3 + o2 -> o3
  }
} for exactly 4 node
