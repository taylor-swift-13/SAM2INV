int main1(){
  int eww6, e4, wjim, v5n;
  eww6=0;
  e4=0;
  wjim=0;
  v5n=(1%18)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wjim == e4;
  loop invariant eww6 == wjim * (wjim + 3) / 2;
  loop invariant v5n == 6 - wjim;
  loop invariant 0 <= v5n <= 6;
  loop assigns wjim, e4, eww6, v5n;
*/
while (1) {
      if (!(v5n>0)) {
          break;
      }
      wjim = wjim+1*1;
      e4 = e4+1*1;
      eww6 = eww6+1*1;
      v5n = v5n - 1;
      eww6 = eww6 + e4;
  }
}