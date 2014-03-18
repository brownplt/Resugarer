#lang ragg

term: (node | list | STRING) [tags]
node: LABEL "(" terms ")"
list: "[" terms "]"
terms: [ term ("," term)* ]

tags: "{" "[" tag ("," tag)* "]" "}"
tag: "Head" "(" LABEL "," NUMBER "," term ")"
     | "Body" | "Alien" | "!Body"