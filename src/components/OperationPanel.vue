<script>
  import { TOKENS } from '~/js/contracts.js'
  import { CreateBuying, CreateSelling, ExecuteBuying, ExecuteSelling } from '~/js/transactions.js'
  import { showTip } from '~/js/data.js'

  export default {
    props: ['symbol', 'active_order'],
    data() {
      return {
        can_convert: true,

        mode: 'create',
        price: '',
        token_amount: '',
        tez_amount: ''
      }
    },
    watch: {
      mode(m) {
        if (m === 'create')
          this.$emit('update:active_order', {})
      },
      active_order(v) {
        if (v.price) {
          this.can_convert = false
          this.mode = 'execute'
          this.price = v.price
          
          if (v.is_buy) {
            this.tez_amount = v.tez_amount
            this.token_amount = this.floor(v.tez_amount / v.price)
          }
          else {
            this.token_amount = v.token_amount
            this.tez_amount = v.token_amount * v.price
          }

          this.$nextTick(() => {
            this.can_convert = true
          })
        }
      },
      price() {
        this.price = this.floor(this.price)

        if (this.token_amount)
          this.convert(null, this.token_amount)
        else if (this.tez_amount)
          this.convert(this.tez_amount, null)
      },
      token_amount() {
        this.convert(null, this.token_amount)
      },
      tez_amount() {
        this.convert(this.tez_amount, null)
      }
    },
    methods: {
      create(is_buy) {
        let token = null
        for (const contract in TOKENS) {
          if (TOKENS[contract] === this.symbol) {
            token = contract
            break
          }
        }

        const promise = is_buy ? 
          CreateBuying(this.tez_amount, token, this.price) : 
          CreateSelling(this.token_amount, token, this.price)

        ;promise
        .then(x => {
          showTip(true, `TX:${x.operation_id}`)
        })
        .catch(err => {
          showTip(false, err)
        })
      },
      execute() {
        const promise = this.active_order.is_buy ?
          ExecuteBuying(this.active_order, this.token_amount) :
          ExecuteSelling(this.active_order, this.tez_amount)

        ;promise
        .then(x => {
          showTip(true, `TX:${x.operation_id}`)
        })
        .catch(err => {
          showTip(false, err)
        })
      },
      floor(x) {
        const result = parseInt(x)
        return result === 0 || isNaN(result) ? '' : result
      },
      convert(tez_amount, token_amount) {
        if (!this.can_convert) 
          return false

        this.can_convert = false

        if (this.price) {
          if (tez_amount) {
            this.tez_amount = this.floor(this.tez_amount)
            this.token_amount = this.floor(this.tez_amount / this.price)
          }
          else {
            this.token_amount = this.floor(this.token_amount)
            this.tez_amount = this.floor(this.price * this.token_amount)
          }
        }

        this.$nextTick(() => {
          this.can_convert = true
        })
      }
    }
  }
</script>

<template>
  <div class="form">
    <label>
      <span :class="price !== '' ? 'focus' : ''">PRICE (MUTEZ / TOKEN)</span>
      <input v-model="price" :disabled="mode === 'execute'"/> 
    </label>
    <label>
      <span :class="token_amount !== ''  ? 'focus' : ''">TOKEN AMOUNT</span>
      <input v-model="token_amount" />
    </label>
    <label>
      <span :class="tez_amount !== ''  ? 'focus' : ''">MUTEZ</span>
      <input v-model="tez_amount" />
      <p class="tip" :style="{opacity: tez_amount ? 1 : 0}">
        {{(tez_amount * 1e-6).toFixed(6).replace('.', ' . ')}} XTZ
      </p>
    </label>

    <div class="order-type-switcher">
      <span :class="mode === 'create' ? 'active' : ''" @click="mode = 'create'">Create</span>
      <span class="switcher" @click="mode = 'create'">
        <span class="pointer" :style="{left: (mode === 'create' ? 0 : 16) + 'px'}"></span>
      </span>
      <span :class="mode === 'execute' ? 'active' : ''">Execute</span>
    </div>
    <button class="buy-btn" v-if="mode === 'create'" @click="create(true)">
      <i class="fas fa-plus-square"></i> <span>BUY {{symbol}}</span>
    </button>
    <button class="sell-btn" v-if="mode === 'create'" @click="create(false)">
      <i class="fas fa-plus-square"></i> <span>SELL {{symbol}}</span>
    </button>
    <button v-if="mode === 'execute'" :class="active_order.is_buy ? 'buy-btn' : 'sell-btn'" @click="execute">
      <i class="fas fa-handshake"></i> <span>{{active_order.is_buy ? 'SELL' : 'BUY'}} {{symbol}} @ {{active_order.price}}</span>
    </button>
  </div>
</template>

<style scoped>
label {
  position: relative; 
  display: block;
  width: 180px; 
  margin: 16px auto;
}
label p.tip {
  text-align: left;
  margin-left: 8px;
  font-size: 12px;
  opacity: 0;
  transition: opacity 0.25s;
}
label span {
  font-size: 13px;
  position: absolute; 
  color: #ccc; 
  top: 4px; 
  left: 8px; 
  white-space: nowrap; 
  z-index: 1;
  transition: all 0.25s;
}
label span.focus {
  font-size: 9px;
  top: -10px;
  left: 0;
  animation-name: fadeIn;
  animation-duration: 0.35s;
}
@keyframes fadeIn {
  from {
    opacity: 0;
  }

  to {
    opacity: 1;
  }
}

input {
  color: #000;
  font-weight: 900;
  font-size: 14px; 
  width: 180px; 
  border: 0;
  border-bottom: 1px solid #f0f0f0;
  transition: all 0.5s;
  padding: 4px 8px;
  outline: none;
}
input:focus {
  border: 0;
  border-bottom: 1px solid #ccc;
}
input:disabled {
  background: transparent;
  color: #eee;
}
input::-webkit-outer-spin-button,
input::-webkit-inner-spin-button {
  -webkit-appearance: none;
  margin: 0; 
}

button {margin: 0 4px;}

.buy-btn * {color: #259e25;}
.sell-btn * {color: #9e2525;}

.order-type-switcher {margin-bottom: 16px;}
.order-type-switcher * {font-size: 13px; transition: all 0.25s; display: inline-block;vertical-align: middle;border-bottom: 1px solid transparent; color: #666;}
.order-type-switcher .active {border-bottom: 1px solid black; color: black;}
.order-type-switcher .switcher {position: relative; margin: 0 4px; width: 32px; border: 2px solid #ddd; border-radius: 16px; height: 16px;}
.order-type-switcher .pointer { position: absolute; background: #ddd; top: 0; left: 0; width: 16px; height: 16px; border-radius: 16px;}
</style>
