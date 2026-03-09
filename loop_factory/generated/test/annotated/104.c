int main1(){
  int wx28, q, l;
  wx28=0;
  q=(1%20)+10;
  l=(1%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q >= 0;
  loop invariant l >= 0;
  loop invariant (9 - l) == wx28 / 2;
  loop invariant q + l + wx28 == 20;
  loop invariant 0 <= wx28 <= 20;
  loop invariant q == 11 - ((wx28 + 1) / 2);
  loop assigns q, l, wx28;
*/
while (q>0&&l>0) {
      if (wx28%2==0) {
          q = q - 1;
      }
      else {
          l--;
      }
      wx28 = wx28 + 1;
  }
}