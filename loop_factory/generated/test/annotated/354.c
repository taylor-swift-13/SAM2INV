int main1(int x){
  int d4, hfy, atr, kln4, ajtl;
  d4=61;
  hfy=0;
  atr=0;
  kln4=0;
  ajtl=(x%18)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kln4 == atr;
  loop invariant atr == hfy;
  loop invariant (x - \at(x, Pre)) % 61 == 0;
  loop invariant x >= \at(x, Pre);
  loop invariant x == \at(x, Pre) + ((\at(x, Pre) % 18) + 5 - ajtl) * d4;
  loop assigns kln4, atr, ajtl, hfy, x;
*/
while (ajtl>=1) {
      kln4 = kln4+x*x;
      atr = atr+x*x;
      ajtl -= 1;
      hfy = hfy+x*x;
      x += d4;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hfy >= atr;
  loop invariant hfy <= atr;
  loop invariant (x - \at(x, Pre)) % d4 == 0;
  loop assigns hfy;
*/
while (1) {
      hfy = hfy + 1;
      if (hfy>=atr) {
          break;
      }
  }
}