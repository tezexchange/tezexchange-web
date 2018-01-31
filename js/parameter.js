((window, document) => {
  const prim = window.TEZEX.util.prim
  const fix_tez = window.TEZEX.util.fix_tez

  const add_order = info => {
    return prim('Pair', [
        {string: info.symbol},
        prim('Right', [
          prim('Left', [
            prim('Pair', [
                {int: info.direction + ''},
                prim('Pair', [
                  {int: info.amount.nat + ''},
                  {string: fix_tez(info.amount.tez)}
                ])
              ])
            ])
        ])
      ])
  }

  const cancel_order = info => {
    return prim('Pair', [
        {string: info.symbol},
        prim('Right', [
          prim('Right', [
            prim('Right', [
                prim('Left', [
                    {int: info.order_id + ''}
                  ])
              ])
            ])
        ])
      ])
  }

  const approve_token = info => {
    return prim('Right', [
        prim('Right', [
            prim('Right', [
                prim('Right', [
                    prim('Left', [
                        prim("Pair", [
                            {string: info.target + ''},
                            {int: info.amount_nat + ''}
                          ])
                      ])
                  ])
              ])
          ])
      ])
  }

  const execute = info => {
    return prim('Pair', [
        {string: info.symbol},
        prim('Right', [
          prim('Right', [
              prim('Left', [
                  prim('Pair', [
                      {int: info.amount_nat + ''},
                      prim('Pair', [
                          {int: info.id + ''},
                          prim('Pair', [
                              {int: info.direction ? '1' : '0'},
                              {string: fix_tez(info.price)}
                            ])
                        ])
                    ])
                ])
            ])
        ])
      ])
    
  }

  const redeem_tez = () => {
    return prim('Pair', [
        {string: 'TES'},
        prim('Right', [
          prim('Right', [
              prim('Right', [
                  prim('Right', [
                      prim('Unit', [])
                    ])
                ])
            ])
        ])
      ])
    
  }

  const redeem_token = () => {
    return prim('None', [])
  }

  const token_transfer = info => {
    return prim('Right', [
        prim('Right', [
            prim('Right', [
                prim('Left', [
                    prim('Pair', [
                        {string: info.target},
                        {int: info.amount + ''}
                      ])
                  ])
              ])
          ])
      ])
  }

  const token_approve = info => {
    return prim('Right', [
        prim('Right', [
            prim('Right', [
              prim('Right', [
                prim('Left', [
                  prim('Pair', [
                      {string: info.target},
                      {int: info.amount + ''}
                    ])
                  ])
                ])
              ])
          ])
      ])
  }

  const token_withdraw = info => {
    return prim('Right', [
        prim('Right', [
            prim('Right', [
              prim('Right', [
                prim('Right', [
                  prim('Left', [
                    prim('Pair', [
                      {string: info.source},
                      prim('Pair', [
                        {string: info.target},
                        {int: info.amount + ''}
                      ])
                    ])
                  ])
                ])
              ])
            ])
          ])
      ])
  }

  const share_distribute = () => {
    return prim('Right', [
        prim('Right', [
            prim('Unit', [])
          ])
      ])
  }

  const share_withdraw = () => {
    return prim('Right', [
        prim('Left', [
            prim('Unit', [])
          ])
      ])
  }

  window.TEZEX.parameter = {
    add_order,
    cancel_order,
    approve_token,
    execute,
    share_distribute,
    share_withdraw,
    redeem_tez,
    redeem_token,
    token_transfer,
    token_approve,
    token_withdraw
  }

})(window, document)