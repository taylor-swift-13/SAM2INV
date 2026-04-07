int main1(){
  int a, go, lzk, t, djs, wnxc;
  a=60;
  go=3;
  lzk=-3;
  t=0;
  djs=go;
  wnxc=a;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant -3 <= lzk <= a;
  loop invariant djs == lzk + 6;
  loop invariant t == (lzk*lzk - lzk - 12)/2;
  loop assigns t, lzk, djs, wnxc;
*/
while (1) {
      if (!(lzk<=a-1)) {
          break;
      }
      t = t + lzk;
      lzk++;
      djs = djs + 1;
      wnxc += t;
  }
}