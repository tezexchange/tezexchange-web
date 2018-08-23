export const CONTRACTS = {
  selected: "testnet#3",
  versions: {
    "testnet#1": {
      "ADMIN": "tz1e8FzYbvNdaHijnBTfZMAHHugKP5eKDhgu",
      "CONTRACT.token": "KT1UHQoA3tt6wH3aEjYkgM2LSFoqBEBMjcAR",
      "CONTRACT.reward": "KT1QKfEmx23ytfEPrUhzyDQJ3j2tHboa8ocu",
      "CONTRACT.main": "KT1WrabGBN2gqDdpr2Bg41Pyrs8Rvng2aAY3",
      "CONTRACT.adapter": "KT1BexCEqkG3e4NiC41fmVfyMEUjWjtkhLqW"
    },
    "testnet#2": {
      "ADMIN": "tz1e8FzYbvNdaHijnBTfZMAHHugKP5eKDhgu",
      "CONTRACT.token": "KT1Vu7py1imbRHcNsvgbtemxUoo16AQ1jUxq",
      "CONTRACT.reward": "KT1GbB51GRq4zhpMroCSFrKAb3MVDb7yeEW2",
      "CONTRACT.main": "KT1Q2Me8wUuDE88NnwEGwT8zWxxYLg3GfTct",
      "CONTRACT.adapter": "KT1AgWWKwXfJaJPFjDB7eMhCgmBvxhJMqgjk"
    },
    "testnet#3": {
      "ADMIN": "tz1UJPFiywU6uGeMpZnPrY4w7zNhLekvJaUo",
      "CONTRACT.token": "KT1WuNaA5HEujWvXXFNe5kyDLdsVfXdTW1FV",
      "CONTRACT.reward": "KT1L9dPozLBsg554S2U8KPxCFyLmWHuHDzb8",
      "CONTRACT.main": "KT1XXjDco86pHU9Jwas5EubiaSHKwv9ZWggQ",
      "CONTRACT.adapter": "KT1WRh4bdwDcsbPFhhLqrQCyoJMCU8Xy34Dj"
    }
  }
}

export const TOKENS = {
  testnet: {
    KT1WuNaA5HEujWvXXFNe5kyDLdsVfXdTW1FV: 'TES'
  },
  mainnet: {

  }
}

export function getContract(name) {
  return CONTRACTS.versions[CONTRACTS.selected][`CONTRACT.${name}`]
}

export function getTokens() {
  return TOKENS[CONTRACTS.selected.slice(0, 7)]
}