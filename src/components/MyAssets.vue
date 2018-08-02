<script>
  import { sample_my_assets } from '~/js/data'

  export default {
    data() {
      return {
        my_assets: sample_my_assets
      }
    }
  }
</script>

<template>
  <div>
    <div class="wrapper">
      <h2>My Assets</h2>
      <table>
        <tbody>
          <tr v-for="(amount, name) in my_assets">
            <th>{{name}}</th>
            <td>
              <b>{{amount}}</b>
            </td>
            <td>
              <button class="withdraw-btn">
                <i class="fas fa-sign-out-alt" title="withdraw"></i>
              </button>
            </td>
          </tr>
        </tbody>
      </table>
    </div>
  </div>
</template>

<style scoped>
h2 {padding: 4px 8px;}
.wrapper {max-width: 240px; margin: 8px auto; background: #f8f8f8; border-radius: 8px;}
table {width: 100%; }
b {font-size: 13px;}
th, td {padding: 3px 6px; font-size: 13px;}
th { font-weight: 400; text-align: right; }

.withdraw-btn i { font-size: 13px; margin: 0 }
</style>