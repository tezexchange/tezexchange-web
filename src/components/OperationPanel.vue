<script>
  export default {
    props: ['active_orders'],
    data() {
      return {
        can_convert: true,
        is_update_from_parent: false,

        direction: false,
        price: '',
        amount_token: '',
        amount_tez: ''
      }
    },
    watch: {
      active_orders(v) {
        if (v.price) {
          this.is_update_from_parent = true
          this.price = v.price
          this.direction = v.direction
          this.amount_token = v.orders.reduce((acc, x) => acc + +x.amount_token, 0)

          this.$nextTick(() => {
            this.is_update_from_parent = false
          })
        }
      },
      price() {
        if (!this.is_update_from_parent)
          this.$emit('update:active_orders', {})

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
      <input v-model="price" /> 
    </label>
    <label>
      <span :class="amount_token !== ''  ? 'focus' : ''">TOKEN AMOUNT</span>
      <input v-model="amount_token" />
    </label>
    <label>
      <span :class="amount_tez !== ''  ? 'focus' : ''">MUTEZ</span>
      <input v-model="amount_tez" />
      <p class="tip" :style="{opacity: amount_tez ? 1 : 0}">
        {{(amount_tez * 1e-6).toFixed(6)}} XTZ
      </p>
    </label>

    <button class="buy-btn">
      <i class="fas fa-plus-square"></i> <span>BUY</span>
    </button>
    <button class="sell-btn">
      <i class="fas fa-plus-square"></i> <span>SELL</span>
    </button>
    <button :disabled="!active_orders.price">
      <i class="fas fa-handshake"></i> <span>EXECUTE</span>
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
input::-webkit-outer-spin-button,
input::-webkit-inner-spin-button {
  -webkit-appearance: none;
  margin: 0; 
}

button {margin: 0 4px;}

.buy-btn * {color: #259e25;}
.sell-btn * {color: #9e2525;}
</style>
