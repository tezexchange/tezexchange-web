<template>
  <div>
	  <header>
	  	<div class="logo">
	  		<nuxt-link to="/">tez.exchange</nuxt-link>
	  	</div>
    </header>
    <div class="wrapper">
	    <nuxt />
    </div>
  </div>
</template>

<style>
* {margin: 0; padding: 0; font-family: 'Lato'; color: #666; font-size: 16px;}
a {text-decoration: none; color: #000;}
i.fas {color: #666;}

header {margin: 8px 0;}
.logo {text-align: center; transition: all 0.5s}
.logo * {font-family: 'Roboto Condensed'; font-weight: 700; font-size: 21px;}
</style>
<style scoped>
.wrapper {max-width: 480px; margin: 0 auto;}	
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