int main1(){
  int f8, a6hi, q, j9, js;
  f8=4;
  a6hi=(1%18)+5;
  q=(1%15)+3;
  j9=a6hi;
  js=f8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j9 == 30 - 4*a6hi;
  loop invariant q == a6hi - 2;
  loop invariant 0 <= a6hi <= 6;
  loop invariant ((j9 - a6hi) % (f8 + 1)) == 0;
  loop assigns a6hi, j9, q;
*/
while (1) {
      if (!(a6hi!=0)) {
          break;
      }
      a6hi--;
      j9 += f8;
      q = q - 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant js - 2*j9 == -56;
  loop invariant j9 >= 0;
  loop invariant js >= 0;
  loop assigns js, j9;
*/
while (j9<f8) {
      js += 1;
      j9++;
      js += 1;
  }
}