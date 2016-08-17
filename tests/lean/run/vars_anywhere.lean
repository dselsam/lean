variable {A : Type}

check @id

xinductive List
| nil : List
| cons : A → List → List

check @List.cons
