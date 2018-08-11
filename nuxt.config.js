module.exports = {
  generate: {
    dir: 'docs'
  },
  srcDir: 'src/',
  head: {
    title: 'tez.exchange',
    meta: [
      {charset: 'utf-8'},
      {name: 'viewport', content: 'width=device-width, initial-scale=1.0, maximum-scale=1.0, user-scalable=no'},
      {name: 'description', content: 'Advanced DEX for Tezos token'}
    ],
    link: [
      { rel: 'icon', type: 'image/icon', href: '/favicon.png' }
    ]
  },    
  css: [
    '~/css/all.css'
  ]
}