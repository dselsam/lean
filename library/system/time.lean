import .io

def time : Type := sorry

namespace time

def sdiff : time → time → string := sorry
meta def get  [io.interface] : io time := sorry

end time
