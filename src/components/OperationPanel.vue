<script>
  export default {
    data() {
      return {
        can_convert: true,
        direction: false,
        price: '',
        amount_token: '',
        amount_tez: ''
      }
    },
    methods: {
      floor(x) {
        const result = Math.floor(x)
        return result === 0 ? '' : result
      },
      convert(price, amount_tez, amount_token) {
        if (!this.can_convert) 
          return false

        this.can_convert = false

        if (this.price) {
          if (amount_tez) {
            this.amount_token = this.floor(amount_tez / price)
            this.amount_tez = this.floor(this.amount_tez)
          }
          else {
            this.amount_tez = this.floor(price * amount_token)
            this.amount_token = this.floor(this.amount_token)
          }
        }

        this.price = this.floor(this.price)

        this.$nextTick(() => {
          this.can_convert = true
        })
      },
      update(price, direction, amount_token) {
        this.price = price
        this.direction = direction
        this.amount_token = amount_token
      }
    },
    watch: {
      price() {
        if (this.amount_token)
          this.convert(this.price, null, this.amount_token)

        if (this.amount_tez)
          this.convert(this.price, this.amount_tez, null)
      },
      amount_token() {
        this.convert(this.price, null, this.amount_token)
      },
      amount_tez() {
        this.convert(this.price, this.amount_tez, null)
      }
    }
  }
</script>

<template>
  <div class="form">
    <label>
      <span :class="price !== '' ? 'focus' : ''">PRICE</span>
      <input type="number" v-model="price" /> 
    </label>
    <label>
      <span :class="amount_token !== ''  ? 'focus' : ''">TOKEN AMOUNT</span>
      <input type="number" v-model="amount_token" />
    </label>
    <label>
      <span :class="amount_tez !== ''  ? 'focus' : ''">MUTEZ</span>
      <input type="number" v-model="amount_tez" />
    </label>

    <button class="buy-btn">
      <i class="fas fa-plus-square"></i> <span>BUY</span>
    </button>
    <button class="sell-btn">
      <i class="fas fa-plus-square"></i> <span>SELL</span>
    </button>
    <button>
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
}
input {
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
