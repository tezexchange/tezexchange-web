import { getContract } from './contracts.js'
import { showTip } from './data.js'

export function RewardWithdraw() {
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
                        "string": getContract('reward')
                      },
                      {
                        "prim": "Pair",
                        "args": [
                          {
                            "int": "0"
                          },
                          {
                            "prim": "Some",
                            "args": [
                              {
                                "prim": "Pair",
                                "args": [
                                  {
                                    "string": getContract('reward')
                                  },
                                  {
                                    "bytes": "050000"
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
    destination: getContract('token'), 
    parameters
  })
  .then(x => {
    showTip(true, x.operation_id)
    return x
  })
  .catch(err => {
    showTip(false, err)
  })
}

export function RewardUnlock() {
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
                        "string": getContract('reward')
                      },
                      {
                        "prim": "Pair",
                        "args": [
                          {
                            "int": "0"
                          },
                          {
                            "prim": "Some",
                            "args": [
                              {
                                "prim": "Pair",
                                "args": [
                                  {
                                    "string": getContract('reward')
                                  },
                                  {
                                    "bytes": "050002"
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
    destination: getContract('token'), 
    parameters
  })
  .then(x => {
    showTip(true, x.operation_id)
    return x
  })
  .catch(err => {
    showTip(false, err)
  })
}

export function RewardLock(token_amount) {
  token_amount = token_amount + ''
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
                        "string": getContract('reward')
                      },
                      {
                        "prim": "Pair",
                        "args": [
                          {
                            "int": token_amount
                          },
                          {
                            "prim": "Some",
                            "args": [
                              {
                                "prim": "Pair",
                                "args": [
                                  {
                                    "string": getContract('reward')
                                  },
                                  {
                                    "bytes": "050001"
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
    destination: getContract('token'), 
    parameters
  })
  .then(x => {
    showTip(true, x.operation_id)
    return x
  })
  .catch(err => {
    showTip(false, err)
  })
}

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
  .then(x => {
    showTip(true, x.operation_id)
    return x
  })
  .catch(err => {
    showTip(false, err)
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
    .then(x => {
      showTip(true, x.operation_id)
      return x
    })
    .catch(err => {
      showTip(false, err)
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
    .then(x => {
      showTip(true, x.operation_id)
      return x
    })
    .catch(err => {
      showTip(false, err)
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
  .then(x => {
    showTip(true, x.operation_id)
    return x
  })
  .catch(err => {
    showTip(false, err)
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
  .then(x => {
    showTip(true, x.operation_id)
    return x
  })
  .catch(err => {
    showTip(false, err)
  })
}