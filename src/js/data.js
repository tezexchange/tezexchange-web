export const DATA = {
  ready: false,
  orders: {},
  my_orders: {}
}

export function dataReady() {
  if (Object.keys(DATA.orders).length)
    return Promise.resolve(DATA)
  else 
    return updateOrders()
}

export function updateOrders() {
  return Promise.resolve(sample_my_orders)
  .then(x => {
    DATA.orders = sample_orders
    DATA.my_orders = sample_my_orders
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