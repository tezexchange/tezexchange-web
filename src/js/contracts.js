export const CONTRACTS = {
  selected: "testnet#1",
  versions: {
    "testnet#1": {
      "ADMIN": "tz1e8FzYbvNdaHijnBTfZMAHHugKP5eKDhgu",
      "CONTRACT.token": "KT1UHQoA3tt6wH3aEjYkgM2LSFoqBEBMjcAR",
      "CONTRACT.reward": "KT1QKfEmx23ytfEPrUhzyDQJ3j2tHboa8ocu",
      "CONTRACT.main": "KT1WrabGBN2gqDdpr2Bg41Pyrs8Rvng2aAY3",
      "CONTRACT.adapter": "KT1BexCEqkG3e4NiC41fmVfyMEUjWjtkhLqW"
    }
  }
}

export const TOKENS = {
  KT1UHQoA3tt6wH3aEjYkgM2LSFoqBEBMjcAR: 'TES'
}

export function getContract(name) {
  return CONTRACTS.versions[CONTRACTS.selected][`CONTRACT.${name}`]
}