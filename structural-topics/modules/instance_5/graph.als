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
