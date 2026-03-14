int main1(int k){
  int h8, yf, bu;
  h8=2;
  yf=(k%20)+10;
  bu=(k%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h8 >= 2;
  loop invariant yf == ((\at(k,Pre) % 20) + 10) - (((h8 - 2) + 1) / 2);
  loop invariant bu == ((\at(k,Pre) % 15) + 8) - ((h8 - 2) / 2);
  loop invariant yf + bu + h8 == k%20 + k%15 + 20;
  loop assigns bu, h8, yf;
*/
while (1) {
      if (!(yf>0&&bu>0)) {
          break;
      }
      if (!(!(h8%2==0))) {
          yf -= 1;
      }
      else {
          bu = bu - 1;
      }
      h8++;
  }
}