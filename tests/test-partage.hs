import qualified Data.Map.Strict as M

import qualified Data.Tree as R
import qualified NLP.Partage.Tree.Other as O
import qualified NLP.Partage.FactGram.DAG as D
import           NLP.Partage.FactGram.DAG (DID(..))
import qualified NLP.Partage.Auto.WeiTrie as WeiTrie
import qualified NLP.Partage.Auto as A
import qualified NLP.Partage.FactGram.Weighted  as W
import qualified NLP.Partage.Inject as Inj


t1 = R.Node (O.NonTerm "S")
  [ R.Node (O.NonTerm "NP") []
  , R.Node (O.NonTerm "VP")
    [R.Node (O.NonTerm "V")
      [R.Node (O.Term "sleep") []]
    ]
  ]


t2 = R.Node (O.NonTerm "NP")
  [ R.Node (O.NonTerm "N")
    [R.Node (O.Term "John") []]
  ]

g = D.mkGram [(t1, 1), (t2, 2)]


dag = D.dagGram g
wei = WeiTrie.fromGram (D.factGram g)
dag' = Inj.injectWeights wei dag


auto = A.fromWei wei


main = do
  -- mapM_ print $ M.toList (D.nodeMap dag)
  -- putStrLn "========="
  -- mapM_ print $ A.allEdges auto

  -- mapM_ print $ D.setIDs dag'

  let xs = [A.Body (DID 0), A.Body (DID 3), A.Head (DID 4)]
  print xs
  print $ Inj.weights xs wei
