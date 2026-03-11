int main1(){
  int jiz, wq9, iphd, sa, l, lzd;
  jiz=1;
  wq9=0;
  iphd=2;
  sa=0;
  l=jiz;
  lzd=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == 1 + sa * jiz;
  loop invariant iphd == 2 + sa;
  loop invariant sa <= jiz;
  loop invariant jiz == 1;
  loop assigns l, iphd, sa;
*/
while (sa<jiz) {
      l = l + jiz;
      iphd++;
      sa += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == 2 + wq9;
  loop invariant lzd == wq9;
  loop invariant jiz == 1;
  loop assigns l, lzd, wq9;
*/
while (l<jiz) {
      lzd = lzd + jiz;
      l = l + 1;
      wq9++;
  }
}