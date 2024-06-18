module filesharing

sig Token {}

var sig File {
  var shared : set Token
}
var sig trashed in File {}

fact init {
  // Initially there are no files uploaded nor shared
  no File
}

fact transitions {
  // The system must only evolve according to the defined actions
  always (
    upload or
    (some f : File | delete[f] or restore[f]) or
    (some f : File, t : Token | share[f,t]) or
    (some t : Token | download[t]) or
    empty or
    stutter
  )
}

run example {} expect 1
