/*  
Graph model at the end of the "Declaring simple modules" section, "Module
system" topic, of the Practical Alloy book.

https://practicalalloy.github.io/book/chapters/structural-topics/topics/modules/index.html#declaring-simple-modules
*/

module graph

pred dag [node: set univ, r: node->node] {
  all n: node | n not in n.^r
}

pred rootedAt[node: set univ, r: node->node, root: node] {
  node in root.*r
}
