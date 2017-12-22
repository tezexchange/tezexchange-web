((window, document) => {
  // init
  document.body.style.display = 'block'

  let contracts = {}
  window.TEZEX.util.get('contracts.json')
  .then(x => {
    contracts = JSON.parse(x)
  })
  .catch(code => console.error(code))

  // helper functions
  const unpair = window.TEZEX.util.unpair
  const tezbridge_iframe = document.querySelector('#tezbridge')
  const tezbridge = window.tezbridgeCreator(tezbridge_iframe)

  tezbridge_iframe.onload = () => {
    TEZEXApp.state.splash = false
  }  

  const TEZEXApp = new Vue({
    el: '#tezex-app',
    components: {
    },
    data: {
      account: {
        pkh: '',
        balance: 0
      },
      state: {
        splash: true,
        loading: {
          type: 'none', // call | pass | fail | none
          tip: '',
          timeout: 0
        },
        display_creating_buying: false,
        display_creating_selling: false
      },
      operations: [],
      selected_token: '',
      token_op: {
        display_more_token_op: false,
        transfer_to: '',
        transfer_amount: 0,
        approve_to: '',
        approve_amount: 0,
        withdraw_from: '',
        withdraw_amount: 0
      },
      redeem_xtz: 0,
      direction: '1',
      amount: {
        decimal: 0,
        nat: 0,
        tez: 0
      },
      tokens: {},
      orders: {
        buy: [],
        sell: []
      },
      order_tab: 'buy'
    },
    watch: {
      'amount.decimal'(x) {
        this.amount.nat = Math.round(x * this.tokens[this.selected_token].precision)
      },
      'state.loading.type'(x) {
        clearTimeout(this.state.loading.timeout)
        if (x === 'call') {
          this.state.loading.tip = ''

        } else if (x === 'pass') {
          this.state.loading.tip = 'TRANSACTION SUCCESS'

          this.state.loading.timeout = setTimeout(() => {
            this.state.loading.type = 'none'
            this.state.loading.tip = ''
          }, 3000)
        } else if (x === 'fail') {
          this.state.loading.timeout = setTimeout(() => {
            this.state.loading.type = 'none'
            this.state.loading.tip = ''
          }, 6000)
        }
      }
    },
    methods: {
      tezbridge: function(params){
        this.state.loading.type = 'call'

        return tezbridge(params)
        .then(x => {
          this.state.loading.type = 'pass'
          if (x.injectedOperation)
            this.operations.push(x.injectedOperation)

          return x
        })
        .catch(err => {
          this.state.loading.type = 'fail'

          let err_text = ``
          const err_result = {}

          if (err instanceof Array)
            err.forEach(x => {
              if (x.id === 'scriptRejectedRuntimeError') {
                err_result.location = x.location
              } else if (x.id === 'scriptRuntimeError') {
                err_result.contract = x.contractHandle
              } else if (x.id === 'contract.balance_too_low') {
                err_text += `balance insufficient`
              } else if (x.missing_key) {
                err_text += `current account doesn't exist in tezos blockchain\nplease add balance first`
              } else if (x.id === 'illTypedDataTypeError') {
                err_text += `invalid parameters`
              }
            })
          else
            err_text = err

          this.state.loading.tip = `[ERROR]\n${err_text}`
          return Promise.reject(err_result.contract ? err_result : null)
        })
      },
      token_transfer: function(){
        const token_contract = this.tokens[this.selected_token].token_contract
        if (!token_contract) return

        const precision = this.tokens[this.selected_token].precision

        this.tezbridge({
          method: 'transfer', 
          amount: 0, 
          destination: token_contract,
          parameters: window.TEZEX.parameter.token_transfer({
            amount: Math.round(this.token_op.transfer_amount * precision),
            target: this.token_op.transfer_to
          })
        })
        .catch(err => {
          if (err) 
            this.state.loading.tip += `token balance insufficient`
        })
      },
      token_approve: function(){
        const token_contract = this.tokens[this.selected_token].token_contract
        if (!token_contract) return

        const precision = this.tokens[this.selected_token].precision

        this.tezbridge({
          method: 'transfer', 
          amount: 0, 
          destination: token_contract,
          parameters: window.TEZEX.parameter.token_approve({
            amount: Math.round(this.token_op.approve_amount * precision),
            target: this.token_op.approve_to
          })
        })
      },
      token_withdraw: function(){
        const token_contract = this.tokens[this.selected_token].token_contract
        if (!token_contract) return

        const precision = this.tokens[this.selected_token].precision

        this.tezbridge({
          method: 'transfer', 
          amount: 0, 
          destination: token_contract,
          parameters: window.TEZEX.parameter.token_withdraw({
            target: this.account.pkh,
            amount: Math.round(this.token_op.withdraw_amount * precision),
            source: this.token_op.withdraw_from
          })
        })
        .catch(err => {
          if (err) 
            this.state.loading.tip += `insufficient amount of approval`
        })
      },
      load_orders: function(){
        if (!this.selected_token) return

        this.tezbridge({method: 'get_contract_info', contract: this.tokens[this.selected_token].contract})
        .then(x => {
          const storage = x.script.storage

          this.tokens[this.selected_token].token_contract = unpair(storage, 1, 1, 1, 1, 0).string

          // get orders
          const orders = unpair(storage, 1, 1, 1, 1, 1, 0).args

          const orders_parsed = orders.map(x => {
            const nat = parseInt(x.args[1].args[1].args[0].args[0].int)
            const tez = window.TEZEX.util.get_tez(x.args[1].args[1].args[0].args[1].string)
            const price = window.TEZEX.util.get_tez(x.args[1].args[1].args[1].args[0].string)
            return {
              id: x.args[0].int,
              direction: x.args[1].args[0].int === '1' ? true : false,
              key: x.args[1].args[1].args[1].args[1].string,
              amount: {nat, tez},
              price
            }
          })

          this.orders = {
            buy: [],
            sell: []
          }

          orders_parsed.forEach(x => {
            if (x.direction)
              this.orders.buy.push(x)
            else
              this.orders.sell.push(x)
          })

          this.orders.buy.sort((a, b) => {
            if (a.price > b.price) 
              return -1
            else if (a.price === b.price) 
              return 0
            else if (a.price < b.price) 
              return 1
          })
          this.orders.sell.sort((a, b) => {
            if (a.price > b.price) 
              return 1
            else if (a.price === b.price) 
              return 0
            else if (a.price < b.price) 
              return -1
          })

          // get redeem
          const redeem = {}
          const redeem_lst = unpair(storage, 1, 1, 1, 1, 1, 1, 1).args
          redeem_lst.forEach(x => {
            redeem[x.args[0].string] = x.args[1].int
          })
          this.tokens[this.selected_token].redeem = redeem[this.account.pkh] || 0

        })
      },
      execute: function(direction, order){
        const precision = this.tokens[this.selected_token].precision

        if (direction) {
          const amount_tez = window.prompt(`Total: ${order.amount.tez} XTZ\nInput the amount you want to spend`)
          if (!amount_tez || !amount_tez.trim() || isNaN(parseFloat(amount_tez))) return
          if (amount_tez > order.amount.tez) return

          this.tezbridge({
            method: 'transfer', 
            amount: amount_tez, 
            destination: contracts.main.contract,
            parameters: window.TEZEX.parameter.execute(
              Object.assign({symbol: this.selected_token, amount_nat: 0}, order))
          })
          .catch(err => {
            if (err) {
              if (err.contract === contracts.execute.contract && err.location === 888) {
                this.state.loading.tip += `the total amount may be consumed by others\nplease reduce the amount and try again`
              }
            }
          })

        } else {
          const amount_nat = window.prompt(`Total: ${order.amount.nat / precision} ${this.selected_token}\nInput the amount you want to spend`)
          if (!amount_nat || !amount_nat.trim() || isNaN(parseFloat(amount_nat))) return

          const calculated_amount_nat = Math.round(amount_nat * precision)
          if (calculated_amount_nat > order.amount.nat) return

          this.tezbridge({
            method: 'transfer', 
            amount: 0, 
            destination: contracts.token.contract,
            parameters: window.TEZEX.parameter.approve_token({
              target: window.TEZEX.key, 
              amount_nat: calculated_amount_nat
            })
          })
          .then(x => {
            return this.tezbridge({
              method: 'transfer', 
              amount: 0, 
              destination: contracts.main.contract,
              parameters: window.TEZEX.parameter.execute(
                Object.assign({symbol: this.selected_token, amount_nat: calculated_amount_nat}, order))
            })
          })
          .catch(err => {
            if (err) {
              if (err.contract === contracts.execute.contract && err.location === 888) {
                this.state.loading.tip += `the total amount may be consumed by others\nplease reduce the amount and try again`
              } else if (err.contract === this.tokens[this.selected_token].token_contract)
                this.state.loading.tip += `insufficient amount of approval`
            }
          })
        }
      },
      redeem_tez: function(){
        this.tezbridge({
          method: 'transfer', 
          amount: 0, 
          destination: contracts.main.contract,
          parameters: window.TEZEX.parameter.redeem_tez(this.selected_token)
        })
        .catch(err => {
          if (err) {
            this.state.loading.tip += `zero amount`
          }
        })
      },
      redeem_token: function(){
        const contract = this.tokens[this.selected_token].contract
        if (!contract) return

        this.tezbridge({
          method: 'transfer', 
          amount: 0, 
          destination: contract,
          parameters: window.TEZEX.parameter.redeem_token()
        })
        .catch(err => {
          if (err) {
            this.state.loading.tip += `zero amount`
          }
        })
      },
      cancel_order: function(order){
        this.tezbridge({
          method: 'transfer', 
          amount: 0, 
          destination: contracts.main.contract,
          parameters: window.TEZEX.parameter.cancel_order({symbol: this.selected_token, order_id: order.id})
        })
      },
      submit_order: function(direction){
        if (this.amount.tez === 0 || this.amount.nat === 0)
          return

        this.direction = direction

        if (this.direction === '1') {
          this.tezbridge({
            method: 'transfer', 
            amount: this.amount.tez, 
            destination: contracts.main.contract,
            parameters: window.TEZEX.parameter.add_order({
              symbol: this.selected_token, 
              direction: this.direction, 
              amount: this.amount
            })
          })

        } else {
          this.tezbridge({
            method: 'transfer', 
            amount: 0, 
            destination: contracts.token.contract,
            parameters: window.TEZEX.parameter.approve_token({
              target: window.TEZEX.key, 
              amount_nat: this.amount.nat, 
            })
          })
          .then(x => {
            return this.tezbridge({
              method: 'transfer', 
              amount: 0, 
              destination: contracts.main.contract,
              parameters: window.TEZEX.parameter.add_order({
                symbol: this.selected_token, 
                direction: this.direction, 
                amount: this.amount
              })
            })
          })
          .catch(err => {
            if (err)
              this.state.loading.tip += `insufficient amount of approval`
          })
        }
      },
      refresh_token_balance: function(){
        const token_contract = this.tokens[this.selected_token].token_contract
        if (!token_contract) return

        this.tezbridge({method: 'get_contract_info', contract: token_contract})
        .then(x => {
          const storage = x.script.storage
          const balance_lst = unpair(storage, 1, 0).args

          const balance_map = {}
          const precision = this.tokens[this.selected_token].precision

          balance_lst.forEach(x => {
            balance_map[x.args[0].string] = parseInt(x.args[1].int) / precision 
          })

          this.tokens[this.selected_token].balance = balance_map[this.account.pkh] || 0
        })  
      },
      refresh_redeem_both: function(){
        this.tezbridge({method: 'get_contract_info', contract: contracts.main.contract})
        .then(x => {
          const storage = x.script.storage

          this.refresh_redeem_xtz(storage)

          this.load_orders()
        })
      },
      refresh_redeem_xtz: function(storage){
        const redeem = {}
        const redeem_lst = unpair(storage, 1, 1).args
        redeem_lst.forEach(x => {
          redeem[x.args[0].string] = window.TEZEX.util.get_tez(x.args[1].string)
        })
        this.redeem_xtz = redeem[this.account.pkh] || 0
      },
      refresh_account: function(){
        this.tezbridge({method: 'get_pkh'})
        .then(x => {
          this.account.pkh = x
          return this.tezbridge({method: 'get_balance'})
        })
        .then(x => {
          this.account.balance = (x / 100).toFixed(2)

          return Object.keys(this.tokens).length ? null :
            this.tezbridge({method: 'get_contract_info', contract: contracts.main.contract})
        })
        .then(x => {
          if (!x) return

          const storage = x.script.storage

          this.refresh_redeem_xtz(storage)

          const tokens = unpair(storage, 1, 0).args
          this.tokens = {}
          tokens.forEach(x => {
            const name = x.args[0].string
            this.tokens[name] = {
              name,
              decimal: +x.args[1].args[0].int,
              redeem: 0,
              precision: window.TEZEX.util.get_precision(+x.args[1].args[0].int),
              balance: 0,
              contract: x.args[1].args[1].string
            }
          })

          setInterval(() => {
            if (this.state.loading.type === 'call') return

            tezbridge({method: 'get_block_head'})
            .then(x => {
              if (!x) return
                
              const hashes = {}
              x.operations[0].forEach(x => hashes[x.hash] = true)

              const uncommitted_operations = this.operations.filter(x => !(x in hashes))
              this.operations = uncommitted_operations
            })
          }, 60000)
        })
        .catch(err => {})
      }
    }
  })

  
})(window, document)