<script>
  import { CONTRACTS } from '~/js/contracts.js'
  import { DATA, dataReady, updateMyOrders, TIPS, showTip } from '~/js/data.js'

  export default {
    data() {
      return {
        tips: TIPS,
        data: DATA,
        contracts: CONTRACTS,
        versions: Object.keys(CONTRACTS.versions)
      }
    },
    methods: {
      copy(selector) {
        const range = document.createRange()
        const selection = window.getSelection()
        range.selectNodeContents(document.querySelector(selector))
        selection.removeAllRanges()
        selection.addRange(range)
        document.execCommand("copy")
        selection.removeAllRanges()
        showTip(true, 'Copied')
      },
      login() {
        window.open('https://www.tezbridge.com')
      },
      focus() {
        updateMyOrders()
      }
    },
    mounted() {
      window.onfocus = this.focus
      dataReady()
    }
  }  
</script>

<template>
  <div>
    <div class="tips">
      <div :class="tip.mode" v-for="(tip, i) in tips">
        <b @click="copy('.et-' + i)" v-if="tip.mode === 'error'">COPY</b>
        <span :class="'et-' + i">{{tip.content}}</span>
      </div>
    </div>
	  <header>
      <div class="top-wrapper">
        <div class="logo">
          <nuxt-link to="/">tez.exchange</nuxt-link>
        </div>
        <div class="menu">
          <nuxt-link to="/my-orders">
            <i class="fas fa-list-alt my-orders-btn" title="mine"></i>
          </nuxt-link>
        </div>
      </div>
      <div class="version-wrapper">
        <label>
          @
          <select v-model="contracts.selected">
            <option :value="v" v-for='v in versions'>{{v}}</option>
          </select>
        </label>
      </div>

      <div class="login-wrapper">
        <button @click="login"  v-if="!data.pkh">
          <i class="fas fa-sign-in-alt"></i>
          <span>LOGIN WITH TEZBRIDGE</span>
        </button>
        {{data.pkh ? `/ ${data.pkh} /` : ''}}
      </div>
    </header>
    <div class="wrapper" id="body-wrapper">
	    <nuxt />
      <div v-if="!data.ready" class="loading">
        <img src="/favicon.png" />
      </div>
    </div>
    <div class="footer">
      <div>
      </div>
      <div class="copyright">
        © 2018 <span class="logo">tez.exchange</span>
      </div>
    </div>
  </div>
</template>

<style scoped>
.wrapper {max-width: 480px; margin: 0 auto; position: relative;}  
header { max-width: 480px; margin: 8px auto;}
header .top-wrapper {display: flex; justify-content: center; align-items: center;}
.logo * {font-family: 'Sacramento'; font-size: 36px;}
.menu {margin-left: 16px}
.footer {max-width: 480px; margin: 0 auto; text-align: center}
.footer .logo {margin-left: 8px; font-family: 'Sacramento'; color: #000; font-size: 17px;}
.copyright {font-size: 10px;color: #666;}
select {
  font-size: 13px;
  border: 1px solid transparent;
  outline: none;
  -webkit-appearance: none;
  -moz-appearance: none;
  appearance: none;
}
.version-wrapper {transform: translate(-10px, -10px); text-align: center}
.login-wrapper {text-align: center; font-size: 12px}
.tips { position: fixed; z-index: 10; top: 0; left: 0; width: 100%; display: flex; flex-direction: column; justify-content: center; align-items: center; }
.tips b {float: right; text-decoration: underline; display: inline-block; margin: 3px 0 0 4px; cursor: pointer; font-size: 12px;}
.tips span {font-size: 14px;}
.tips > div { border-radius: 3px; max-height: 128px; overflow: hidden;  max-width: 480px; margin-bottom: 4px; padding: 0px 4px 2px 4px; animation-name: fadeIn; animation-duration: 0.5s}
.tips * {color: white; }
.tips .success { border: 1px solid rgb(0,210,0); background: rgb(0,200,0); opacity: 0.95; }
.tips .error { border: 1px solid rgb(210,0,0); background: rgb(200,0,0); opacity: 0.95; }

@keyframes fadeIn {
  from {
    opacity: 0
  }

  to {
    opacity: 1
  }
}

.loading { text-align: center; margin: 16px 0;}
.loading img { border-radius: 32px; width: 32px; animation: rotate .5s infinite; padding: 10px; opacity: 0.25; border: 2px solid transparent; }
@keyframes rotate {
  0% {
    border: 2px solid rgba(0,0,0,.1);
    border-left: 2px solid rgba(0,0,0,0.2);
    border-top: 2px solid rgba(0,0,0,0.3);
  }
  25% {
    border: 2px solid rgba(0,0,0,.1);
    border-top: 2px solid rgba(0,0,0,0.2);
    border-right: 2px solid rgba(0,0,0,0.3);
  }
  50% {
    border: 2px solid rgba(0,0,0,.1);
    border-right: 2px solid rgba(0,0,0,0.2);
    border-bottom: 2px solid rgba(0,0,0,0.3);
  }
  75% {
    border: 2px solid rgba(0,0,0,.1);
    border-bottom: 2px solid rgba(0,0,0,0.2);
    border-left: 2px solid rgba(0,0,0,0.3);
  }
  100% {
    border: 2px solid rgba(0,0,0,.1);
    border-left: 2px solid rgba(0,0,0,0.2);
    border-top: 2px solid rgba(0,0,0,0.3);
  }
}

</style>

<style>
* {margin: 0; padding: 0; font-family: 'Lato'; color: #666; font-size: 16px;}
b {font-weight: 900}
a {text-decoration: none; color: #000;}
i.fas {color: #666;}
i.far {color: #666;}
button {
  cursor: pointer;
  background: rgb(252,252,252); 
  background: linear-gradient(275deg, rgba(252,252,252,1) 0%, rgba(255,255,255,1) 100%); 
  padding: 4px 8px; 
  outline: none; 
  display: inline-flex;
  transition: border 0.5s;
  border: 1px solid #fff;
  border-right: 1px solid #eee;
  border-bottom: 1px solid #eee;
  transition: border 0.25s, background 0.25s;
}
button:hover {
  border: 1px solid #999;
}
button:active {
  border: 1px solid #fff;
  background: rgba(250,250,250,1); 
}
button:disabled {
  opacity: 0.25
}
button > i {margin-right: 4px;}
button span {font-family: 'Roboto Condensed'; font-size: 14px; }
h2 { font-weight: 900; font-size: 14px; }

.expand-enter-active {
  transition: all 5s;
}
.expand-leave-active {
  transition: all 5s;
}
.expand-enter, .expand-leave-to {
  opacity: 0;
  max-height: 0;
}

.slider {
  overflow: hidden;
  animation-name: slideDown;
  animation-timing-function: ease-in-out;
  animation-duration: 0.25s;
}

@keyframes slideDown {
  from {
    max-height: 0;
  }

  to {
    max-height: 256px;
  }
}

</style>


<style>
@font-face {
    font-family: 'Sacramento';
    src: url('../webfonts/Sacramento-Regular.woff2') format('woff2');
    font-weight: normal;
    font-style: normal;
}

@font-face {
    font-family: 'Lato';
    src: url('../webfonts/Lato-Regular.woff2') format('woff2');
    font-weight: normal;
    font-style: normal;
}

@font-face {
    font-family: 'Lato';
    src: url('../webfonts/Lato-Black.woff2') format('woff2');
    font-weight: 900;
    font-style: normal;
}

@font-face {
    font-family: 'Roboto Condensed';
    src: url('../webfonts/RobotoCondensed-Regular.woff2') format('woff2');
    font-weight: normal;
    font-style: normal;
}


</style>