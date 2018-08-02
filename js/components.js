((window, document) => {
  if (!Promise.prototype.finally) {
    Promise.prototype.finally = function(f) {
      return this.then(f, f).then(() => {})
    }
  }

  // init
  document.body.style.display = 'block'

  let contracts = {}
  let token_contracts = {}
  window.TEZEX.util.get('contracts.json')
  .then(x => {
    contracts = JSON.parse(x)
    return window.TEZEX.util.get('tokens.json')
  })
  .then(x => {
    token_contracts = JSON.parse(x)
    token_contracts.TES = contracts.token.TES.contract
  })
  .catch(code => console.error(code))


  // helper functions
  const unpair = window.TEZEX.util.unpair


  tezbridge({method: 'public_key_hash', noalert: true}).catch(() => {}).finally(() => {
    TEZEXApp.state.splash = false
  })

  const TEZEXApp = new Vue({
    el: '#tezex-app',
    components: {
    },
    data: {
      account: {
        pkh: '',
        pkh_hash: '',
        balance: 0,
        tes_share: 0
      },
      state: {
        splash: true,
        warning: true,
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
      token_description: {
        TES: '(tez.exchange share)',
        BTW: '(BettingWin)'
      },
      orders: {
        buy: [],
        sell: []
      },
      execution: {
        order: null,
        decimal: 0,
        tez: 0,
        focus: 0
      },
      order_tab: 'buy'
    },
    watch: {
      'execution.decimal'(x) {
        if (this.execution.focus !== 1) return
        const price = this.execution.order.price / 100000000 * this.tokens[this.selected_token].precision
        this.execution.tez = (x * price).toFixed(6)
      },
      'execution.tez'(x) {
        if (this.execution.focus !== 2) return
        const price = this.execution.order.price / 100000000 * this.tokens[this.selected_token].precision
        this.execution.decimal = (x / price).toFixed(this.tokens[this.selected_token].decimal)
      },
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
              } else if (x.id === 'tez.addition_overflow') {
                err_text += `xtz amount overflow`
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
            this.state.loading.tip += `\ntoken balance insufficient`
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
            this.state.loading.tip += `\ninsufficient amount of approval`
        })
      },
      share_distribute: function(){
        this.tezbridge({
          method: 'transfer',
          amount: 0,
          destination: contracts.share_reward.contract,
          parameters: window.TEZEX.parameter.share_distribute()
        })
        .then(x => {
          console.log(x)
        })
      },
      share_withdraw: function(){
        if (!this.account.tes_share) return

        this.tezbridge({
          method: 'transfer',
          amount: 0,
          destination: contracts.share_reward.contract,
          parameters: window.TEZEX.parameter.share_withdraw()
        })
        .catch(err => {
          if (err)
            this.state.loading.tip += `\nreward has been withdrawn`
        })
      },
      change_selected_token: function(){
        let p = Promise.resolve()
        if (this.selected_token === 'TES') {
          p = this.tezbridge({method: 'contract', contract: contracts.share_reward.contract})
          .then(x => {
            const storage = x.script.storage
            const balance_map = unpair(storage, 1)

            for (let i = 0; i < balance_map.length; i++) {
              const key_hash = balance_map[i].args[0].string
              const balance = balance_map[i].args[1].string

              if (key_hash === this.account.pkh_hash) {
                this.account.tes_share = balance
                break
              }
            }
          })
        }

        p.then(() => {
          this.load_orders()
        })
      },
      load_orders: function(){
        if (!this.selected_token) return

        this.tezbridge({method: 'contract', contract: this.tokens[this.selected_token].contract})
        .then(x => {
          const storage = x.script.storage

          this.tokens[this.selected_token].token_contract = unpair(storage, 1, 1, 0).string

          // get orders
          const orders = unpair(storage, 1, 1, 1, 0)

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
          const redeem_lst = unpair(storage, 1, 1, 1, 1, 1)
          redeem_lst.forEach(x => {
            redeem[x.args[0].string] = x.args[1].int
          })
          this.tokens[this.selected_token].redeem = redeem[this.account.pkh_hash] || 0

        })
      },
      show_execution_dialog: function(order){
        this.execution.order = order
        this.execution.decimal = order.amount.nat / this.tokens[this.selected_token].precision
        this.execution.tez = order.amount.tez
      },
      execute: function(){
        const precision = this.tokens[this.selected_token].precision
        const order = this.execution.order
        const direction = this.execution.order.direction
        const amount_tez = this.execution.tez
        const amount_nat = Math.round(this.execution.decimal * this.tokens[this.selected_token].precision)

        if (!direction) {
          if (amount_tez > order.amount.tez) {
            alert('amount of XTZ is out of range')
            return
          }

          this.tezbridge({
            method: 'transfer',
            amount: amount_tez,
            destination: contracts.main.contract,
            parameters: window.TEZEX.parameter.execute(
              Object.assign({symbol: this.selected_token, amount_nat: 0}, order))
          })
          .then(x => {
            this.execution.order = null
          })
          .catch(err => {
            if (err) {
              if (err.contract === contracts.execute.contract && err.location === 888) {
                this.state.loading.tip += `\nthe total amount may be consumed by others\nplease reduce the amount and try again`
              }
            }
          })

        } else {
          if (amount_nat > order.amount.nat) {
            alert(`amount of ${this.selected_token} is out of range`)
            return
          }

          this.tezbridge({
            method: 'operations',
            operations: [{
              method: 'transfer',
              amount: 0,
              destination: token_contracts[this.selected_token],
              parameters: window.TEZEX.parameter.approve_token({
                target: contracts.selfpkh.contract,
                amount_nat: amount_nat
              })
            }, {
              method: 'transfer',
              amount: 0,
              destination: contracts.main.contract,
              parameters: window.TEZEX.parameter.execute(
                Object.assign({symbol: this.selected_token, amount_nat: amount_nat}, order))
            }]
          })
          .then(x => {
            this.execution.order = null
          })
          .catch(err => {
            if (err) {
              if (err.contract === contracts.execute.contract && err.location === 888) {
                this.state.loading.tip += `\nthe total amount may be consumed by others\nplease reduce the amount and try again`
              } else if (err.contract === this.tokens[this.selected_token].token_contract)
                this.state.loading.tip += `\ninsufficient amount of approval`
            }
          })
        }
      },
      redeem_tez: function(){
        this.tezbridge({
          method: 'transfer',
          amount: 0,
          destination: contracts.main.contract,
          parameters: window.TEZEX.parameter.redeem_tez()
        })
        .catch(err => {
          if (err) {
            this.state.loading.tip += `\nzero amount`
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
            this.state.loading.tip += `\nzero amount`
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
            method: 'operations',
            operations: [{
              method: 'transfer',
              amount: 0,
              destination: token_contracts[this.selected_token],
              parameters: window.TEZEX.parameter.approve_token({
                target: contracts.selfpkh.contract,
                amount_nat: this.amount.nat,
              })
            }, {
              method: 'transfer',
              amount: 0,
              destination: contracts.main.contract,
              parameters: window.TEZEX.parameter.add_order({
                symbol: this.selected_token,
                direction: this.direction,
                amount: this.amount
              })
            }]
          })
          .catch(err => {
            if (err)
              this.state.loading.tip += `\ninsufficient amount of approval`
          })
        }
      },
      refresh_token_balance: function(){
        const token_contract = this.tokens[this.selected_token].token_contract
        if (!token_contract) return

        this.tezbridge({method: 'contract', contract: token_contract})
        .then(x => {
          const storage = x.script.storage
          const balance_lst = unpair(storage, 1, 0)

          const balance_map = {}
          const precision = this.tokens[this.selected_token].precision

          balance_lst.forEach(x => {
            balance_map[x.args[0].string] = parseInt(x.args[1].int) / precision
          })

          this.tokens[this.selected_token].balance = balance_map[this.account.pkh_hash] || 0
        })
      },
      refresh_redeem_both: function(){
        this.tezbridge({method: 'contract', contract: contracts.main.contract})
        .then(x => {
          const storage = x.script.storage

          this.refresh_redeem_xtz(storage)

          this.load_orders()
        })
      },
      refresh_redeem_xtz: function(storage){
        const redeem = {}
        const redeem_lst = unpair(storage, 1, 1)
        redeem_lst.forEach(x => {
          redeem[x.args[0].string] = window.TEZEX.util.get_tez(x.args[1].string)
        })
        this.redeem_xtz = redeem[this.account.pkh_hash] || 0
      },
      refresh_account: function(){
        this.tezbridge({method: 'public_key_hash'})
        .then(x => {
          this.account.pkh = x
          return this.tezbridge({method: 'hash_data', data: x, type: 'string'})
        })
        .then(x => {
          this.account.pkh_hash = x
          return this.tezbridge({method: 'balance'})
        })
        .then(x => {
          this.account.balance = x

          return Object.keys(this.tokens).length ? null :
            this.tezbridge({method: 'contract', contract: contracts.main.contract})
        })
        .then(x => {
          if (!x) return

          const storage = x.script.storage

          this.refresh_redeem_xtz(storage)

          const tokens = unpair(storage, 1, 0)
          this.tokens = {}
          tokens.reverse().forEach(x => {
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

          // setInterval(() => {
          //   if (this.state.loading.type === 'call') return

          //   tezbridge({method: 'block_head'})
          //   .then(x => {
          //     if (!x) return

          //     const hashes = {}
          //     x.operations[0].forEach(x => hashes[x.hash] = true)

          //     const uncommitted_operations = this.operations.filter(x => !(x in hashes))
          //     this.operations = uncommitted_operations
          //   })
          // }, 60000)
        })
        .catch(err => {})
      }
    }
  })

  window.TEZEXApp = TEZEXApp

})(window, document)