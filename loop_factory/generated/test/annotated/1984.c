int main1(int e){
  int i, d0, ag, r2e, hd;
  i=e;
  d0=0;
  ag=3;
  r2e=0;
  hd=25;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d0 >= 0;
  loop invariant ag == d0 + 3;
  loop invariant r2e == -d0;
  loop invariant hd == 25 - d0 * (d0 + 1) / 2;
  loop invariant (i >= 0) ==> (d0 <= i);
  loop invariant i == \at(e, Pre);
  loop assigns ag, d0, r2e, hd;
*/
while (1) {
      if (!(d0 < i)) {
          break;
      }
      ag += 1;
      r2e -= 1;
      d0++;
      hd = hd + r2e;
  }
}