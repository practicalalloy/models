/*  
Graph model at the end of the "Parametrized modules" section, "Module
system" topic, of the Practical Alloy book.

https://practicalalloy.github.io/chapters/structural-topics/topics/modules/index.html#parametrized-modules
*/

module graph[node]

pred dag [r: node -> node] {
  all n : node | n not in n.^r
}

pred rootedAt [r: node -> node, root: node] {
  node in root.*r
}

run dag_example { 
  some r: node -> node | dag[r] 
} for exactly 4 node