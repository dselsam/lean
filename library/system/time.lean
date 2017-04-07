import .io

meta constant time : Type

namespace time

meta constant sdiff : time → time → string
meta constant get  [io.interface] : io time

end time
