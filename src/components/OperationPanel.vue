<script>
  export default {
    props: ['symbol', 'active_orders'],
    data() {
      return {
        can_convert: true,

        mode: 'pending',
        price: '',
        amount_token: '',
        amount_tez: ''
      }
    },
    watch: {
      active_orders(v) {
        if (v.price) {
          this.mode = 'pending'
          this.price = v.price
          this.amount_token = v.orders.reduce((acc, x) => acc + +x.amount_token, 0)
        }
      },
      price() {
        this.price = this.floor(this.price)

        if (this.amount_token)
          this.convert(null, this.amount_token)
        else if (this.amount_tez)
          this.convert(this.amount_tez, null)
      },
      amount_token() {
        this.convert(null, this.amount_token)
      },
      amount_tez() {
        this.convert(this.amount_tez, null)
      }
    },
    methods: {
      switchMode() {
        this.mode = this.mode === 'pending' ? 'market' : 'pending'
      },
      floor(x) {
        const result = parseInt(x)
        return result === 0 || isNaN(result) ? '' : result
      },
      convert(amount_tez, amount_token) {
        if (!this.can_convert) 
          return false

        this.can_convert = false

        if (this.price) {
          if (amount_tez) {
            this.amount_tez = this.floor(this.amount_tez)
            this.amount_token = this.floor(this.amount_tez / this.price)
          }
          else {
            this.amount_token = this.floor(this.amount_token)
            this.amount_tez = this.floor(this.price * this.amount_token)
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
      <span :class="price !== '' ? 'focus' : ''">PRICE</span>
      <input v-model="price" :disabled="mode === 'market'"/> 
    </label>
    <label>
      <span :class="amount_token !== ''  ? 'focus' : ''">TOKEN AMOUNT</span>
      <input v-model="amount_token" />
    </label>
    <label>
      <span :class="amount_tez !== ''  ? 'focus' : ''">MUTEZ</span>
      <input v-model="amount_tez" />
      <p class="tip" :style="{opacity: amount_tez ? 1 : 0}">
        {{(amount_tez * 1e-6).toFixed(6).replace('.', ' . ')}} XTZ
      </p>
    </label>

    <div class="order-type-switcher">
      <span :class="mode === 'pending' ? 'active' : ''" @click="mode = 'pending'">Pending</span>
      <span class="switcher" @click="switchMode">
        <span class="pointer" :style="{left: (mode === 'pending' ? 0 : 16) + 'px'}"></span>
      </span>
      <span :class="mode === 'market' ? 'active' : ''" @click="mode = 'market'">Market</span>
    </div>
    <button class="buy-btn">
      <i class="fas fa-plus-square"></i> <span>BUY {{symbol}}</span>
    </button>
    <button class="sell-btn">
      <i class="fas fa-plus-square"></i> <span>SELL {{symbol}}</span>
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
