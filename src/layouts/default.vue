<template>
  <div>
	  <header>
	  	<div class="logo">
	  		<nuxt-link to="/">tez.exchange</nuxt-link>
	  	</div>
      <div class="menu">
        <nuxt-link to="/my-orders">
          <i class="fas fa-list-alt my-orders-btn" title="mine"></i>
        </nuxt-link>
      </div>
    </header>
    <div class="wrapper">
	    <nuxt />
    </div>
  </div>
</template>

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

<style scoped>
.wrapper {max-width: 480px; margin: 0 auto; position: relative;}  
header {display: flex; justify-content: center; align-items: center; max-width: 480px; margin: 8px auto;}
.logo {}
.logo * {font-family: 'Roboto Condensed'; font-weight: 700; font-size: 21px;}
.menu {margin-left: 16px}
</style>

<style>
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

@font-face {
    font-family: 'Roboto Condensed';
    src: url('../webfonts/RobotoCondensed-Bold.woff2') format('woff2');
    font-weight: bold;
    font-style: normal;
}


</style>