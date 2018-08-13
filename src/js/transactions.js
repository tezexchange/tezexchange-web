import { getContract } from './contracts.js'

export function ExecuteSelling(order, amount) {
  amount = amount + ''
  const parameters = {
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
                            "int": order.price
                          },
                          {
                            "prim": "Pair",
                            "args": [
                              {
                                "int": "0"
                              },
                              {
                                "string": order.owner
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

  return tezbridge({
      method: 'transfer', 
      amount: amount,
      destination: getContract('main'), 
      parameters
    })
}

export function ExecuteBuying(order, amount) {
  amount = amount + ''
  return tezbridge({
    method: 'pack_data',
    data: { "prim": "Pair", "args": [ { "int": "1" }, { "int": order.price } ] },
    type: { "prim": "pair", "args": [ { "prim": "nat" }, { "prim": "mutez" } ] }
  })
  .then(x => {
    const parameters = {
            "prim": "Right",
            "args": [
              {
                "prim": "Left",
                "args": [
                  {
                    "prim": "Pair",
                    "args": [
                      {
                        "string": order.owner
                      },
                      {
                        "prim": "Pair",
                        "args": [
                          {
                            "int": amount
                          },
                          {
                            "prim": "Some",
                            "args": [
                              {
                                "prim": "Pair",
                                "args": [
                                  {
                                    "string": getContract('adapter')
                                  },
                                  {
                                    "bytes": x
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
            ]
          }

    return tezbridge({
      method: 'transfer', 
      destination: order.token, 
      parameters
    })
  })
}

export function CreateSelling(amount, token, price) {
  amount = amount + ''
  price = price + ''
  return tezbridge({
    method: 'pack_data',
    data: { "prim": "Pair", "args": [ { "int": "0" }, { "int": price } ] },
    type: { "prim": "pair", "args": [ { "prim": "nat" }, { "prim": "mutez" } ] }
  })
  .then(x => {
    const parameters = {
            "prim": "Right",
            "args": [
              {
                "prim": "Left",
                "args": [
                  {
                    "prim": "Pair",
                    "args": [
                      {
                        "string": getContract('main')
                      },
                      {
                        "prim": "Pair",
                        "args": [
                          {
                            "int": amount
                          },
                          {
                            "prim": "Some",
                            "args": [
                              {
                                "prim": "Pair",
                                "args": [
                                  {
                                    "string": getContract('adapter')
                                  },
                                  {
                                    "bytes": x
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
            ]
          }

    return tezbridge({
      method: 'transfer', 
      destination: token, 
      parameters
    })
  })

}

export function CreateBuying(amount, token, price) {
  amount = amount + ''
  price = price + ''
  const parameters = {
            "prim": "Left",
            "args": [
              {
                "prim": "Pair",
                "args": [
                  {
                    "string": token
                  },
                  {
                    "prim": "Pair",
                    "args": [
                      {
                        "int": price
                      },
                      {
                        "int": "0"
                      }
                    ]
                  }
                ]
              }
            ]
          }

  return tezbridge({
    method: 'transfer', 
    amount: amount,
    destination: getContract('main'), 
    parameters
  })
}

export function CancelOrder(order) {
  const parameters = {
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

  return tezbridge({
    method: 'transfer', 
    destination: getContract('main'), 
    parameters
  })
}