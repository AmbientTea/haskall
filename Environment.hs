module Environment where
import Values
import Types

import Data.Map (Map)

type Env = Map String Integer
type State = Map Integer Value
