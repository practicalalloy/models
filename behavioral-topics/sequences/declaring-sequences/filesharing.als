module filesharing

sig Token {}
sig File {
  var shared : set Token
}
var sig uploaded in File {}
one sig Trash {
  var trashed : seq uploaded
}

run example {} expect 1
