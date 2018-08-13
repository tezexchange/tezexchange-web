import { CONTRACTS, TOKENS } from './contracts.js'
import { enc58, makePlain } from './helper.js'

export const TIPS = [
]
export function showTip(is_success, content) {
  TIPS.unshift({mode: (is_success ? 'success' : 'error'), content})
  setTimeout(() => {
    TIPS.pop()
  }, 5000)
}

export const DATA = {
  pkh: '',
  ready: false,
  orders: {},
  my_orders: {}
}

setInterval(() => {
  if (!DATA.ready) return false

  dataRefresh()
}, 10 * 1000)

export function dataReady() {
  if (DATA.ready)
    return Promise.resolve(DATA)
  else 
    return updateOrders()
}

export function dataRefresh() {
  return updateOrders()
  .then(() => {
    updateMyOrders()
  })
}

export function updateMyOrders() {
  return Promise.all([dataReady(), tezbridge({method: 'public_key_hash', noalert: true})])
  .then(([_, pkh]) => {
    if (!pkh) return Promise.reject()

    DATA.pkh = pkh

    const my_orders = {}
    for (const name in DATA.orders) {
      my_orders[name] = []

      DATA.orders[name].buying.forEach(x => {
        if (x.owner === pkh)
          my_orders[name].push(x)
      })
      DATA.orders[name].selling.forEach(x => {
        if (x.owner === pkh)
          my_orders[name].push(x)
      })
    }

    DATA.my_orders = my_orders
    return DATA.my_orders
  })
}

export function updateOrders() {
  const contracts = CONTRACTS.versions[CONTRACTS.selected]

  return tezbridge({method: 'raw_storage', contract: contracts['CONTRACT.main']})
  .then(x => {
    const order_lst = x.big_map.map(x => {
      const result = makePlain(x)
      return {
        token: enc58('contract', result[0]),
        owner: enc58('identity', result[1]),
        is_buy: result[2].toLowerCase() === 'true' ? true : false,
        price: result[3],
        tez_amount: result[4],
        token_amount: result[5]
      }
    })
    
    const orders = {}
    order_lst.forEach(x => {
      if (x.token in TOKENS) {
        const key = TOKENS[x.token]
        if (!orders[key])
          orders[key] = {buying: [], selling: []}

        orders[key][x.is_buy ? 'buying' : 'selling'].push(x)
      }
    })

    DATA.orders = orders
    DATA.ready = true
    return DATA
  })
}


export const sample_my_assets = {
  XTZ: '2312141',
  WEQ: '3234235353',
  ABC: '324'
}

const sample_my_orders = {
  WEQ: [
    {direction: true, price: 2114, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '323'},
    {direction: true, price: 2114, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '323'},
    {direction: true, price: 2114, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '323'},
    {direction: true, price: 2114, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '323'},
    {direction: true, price: 2114, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '323'},
    {direction: true, price: 2114, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '323'},
    {direction: true, price: 2114, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '323'},
    {direction: true, price: 2114, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '323'},
    {direction: true, price: 2114, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '323'},
    {direction: true, price: 2114, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '323'},
    {direction: true, price: 2114, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '323'},
    {direction: true, price: 2114, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '323'},
    {direction: true, price: 2114, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '323'},
    {direction: true, price: 2114, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '323'},
    {direction: true, price: 2114, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '323'},
    {direction: true, price: 2114, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '323'},
    {direction: false, price: 1314, owner: 'tz1dfagfvWf', amount_tez: '133423444', amount_token: '3223'}
  ],
  ABC: [
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: false, price: 1145, owner: 'tz1dfagvWf', amount_tez: '144', amount_token: '3234234234223'},
    {direction: true, price: 145, owner: 'tz1dfagvWfz', amount_tez: '1443', amount_token: '6323'},
    {direction: false, price: 2143, owner: 'tz1dfagfvWf', amount_tez: '13232223244', amount_token: '32223232223'}
  ]
}

const sample_orders = {
	WEQ: {
    selling: [
      {
        price: 345,
        owner: 'tz1fwneonaboa',
        tez_amount: 0,
        token_amount: 2332
      },
      {
        price: 3435,
        owner: 'tz1fwneonaboa',
        tez_amount: 0,
        token_amount: 56776
      },
      {
        price: 3454,
        owner: 'tz1fwneonaboa',
        tez_amount: 0, 
        token_amount: 456356
      },
      {
        price: 34234,
        owner: 'tz1fwneonaboa',
        tez_amount: 0,
        token_amount: 24562
      }
    ],
    buying: [
      {
        price: 222,
        owner: 'tz1fniobeoine',
        tez_amount: 132234,
        token_amount: 0
      },
      {
        price: 2232,
        owner: 'tz1fniobeoine',
        tez_amount: 132342,
        token_amount: 0
      },
      {
        price: 22323,
        owner: 'tz1fniobeoine',
        tez_amount: 3453132,
        token_amount: 0
      },
      {
        price: 223200,
        owner: 'tz1fniobeoine',
        tez_amount: 3433132,
        token_amount: 0
      }
    ]
  },
  ABC: {
    selling: [
     {
        price: 345,
        owner: 'tz1fwneonaboa',
        tez_amount: 0,
        token_amount: 43553
      },
      {
        price: 3435,
        owner: 'tz1fwneonaboa',
        tez_amount: 0,
        token_amount: 21234
      }
    ],
    buying: [
      {
        price: 22323,
        owner: 'tz1fniobeoine',
        tez_amount: 3245132,
        token_amount: 0
      },
      {
        price: 223200,
        owner: 'tz1fniobeoine',
        tez_amount: 1345232,
        token_amount: 0
      }
    ]
  }
}