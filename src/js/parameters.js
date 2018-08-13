export function Cancel(order) {
  return {
            "prim": "Right",
            "args": [
              {
                "prim": "Right",
                "args": [
                  {
                    "prim": "Left",
                    "args": [
                      {
                        "prim": "Pair",
                        "args": [
                          {
                            "string": order.token
                          },
                          {
                            "prim": "Pair",
                            "args": [
                              {
                                "prim": order.is_buy ? "True" : "False",
                                "args": []
                              },
                              {
                                "int": order.price
                              }
                            ]
                          }
                        ]
                      }
                    ]
                  }
                ]
              }
            ]
          }
}