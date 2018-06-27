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
* {margin: 0; padding: 0; font-family: Lato; color: #666;}
a {text-decoration: none; color: #000;}
i.fas {color: #666;}

header {margin: 8px 0;}
.logo {text-align: center; transition: all 0.5s}
.logo * {font-family: 'Roboto Condensed'; font-weight: 700; font-size: 18px;}
</style>
<style scoped>
.wrapper {max-width: 480px; margin: 0 auto;}	
</style>

<style>
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
    src: url('../webfonts/RobotoCondensed-BoldItalic.woff2') format('woff2');
    font-weight: bold;
    font-style: italic;
}

@font-face {
    font-family: 'Lato';
    src: url('../webfonts/Lato-Light.woff2') format('woff2');
    font-weight: 300;
    font-style: normal;
}

@font-face {
    font-family: 'Lato';
    src: url('../webfonts/Lato-LightItalic.woff2') format('woff2');
    font-weight: 300;
    font-style: italic;
}

@font-face {
    font-family: 'Lato';
    src: url('../webfonts/Lato-BlackItalic.woff2') format('woff2');
    font-weight: 900;
    font-style: italic;
}

@font-face {
    font-family: 'Roboto Condensed';
    src: url('../webfonts/RobotoCondensed-Light.woff2') format('woff2');
    font-weight: 300;
    font-style: normal;
}

@font-face {
    font-family: 'Lato';
    src: url('../webfonts/Lato-BoldItalic.woff2') format('woff2');
    font-weight: bold;
    font-style: italic;
}

@font-face {
    font-family: 'Lato';
    src: url('../webfonts/Lato-Bold.woff2') format('woff2');
    font-weight: bold;
    font-style: normal;
}

@font-face {
    font-family: 'Lato Hairline';
    src: url('../webfonts/Lato-Hairline.woff2') format('woff2');
    font-weight: 300;
    font-style: normal;
}

@font-face {
    font-family: 'Roboto Condensed';
    src: url('../webfonts/RobotoCondensed-Bold.woff2') format('woff2');
    font-weight: bold;
    font-style: normal;
}

@font-face {
    font-family: 'Roboto Condensed';
    src: url('../webfonts/RobotoCondensed-LightItalic.woff2') format('woff2');
    font-weight: 300;
    font-style: italic;
}

@font-face {
    font-family: 'Lato Hairline';
    src: url('../webfonts/Lato-HairlineItalic.woff2') format('woff2');
    font-weight: 300;
    font-style: italic;
}

@font-face {
    font-family: 'Roboto Condensed';
    src: url('../webfonts/RobotoCondensed-Italic.woff2') format('woff2');
    font-weight: normal;
    font-style: italic;
}

@font-face {
    font-family: 'Lato';
    src: url('../webfonts/Lato-Regular.woff2') format('woff2');
    font-weight: normal;
    font-style: normal;
}

@font-face {
    font-family: 'Lato';
    src: url('../webfonts/Lato-Italic.woff2') format('woff2');
    font-weight: normal;
    font-style: italic;
}
</style>