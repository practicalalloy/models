/*  
Graph model for the generation of instance 2 of the "Module system" topic,
"Adding fields to module parameters" section, of the Practical Alloy book.

https://practicalalloy.github.io/book/chapters/structural-topics/topics/modules/index.html#adding-fields-to-module-parameters
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