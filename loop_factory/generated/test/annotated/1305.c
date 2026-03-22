int main1(int c){
  int u6, xa, l, c3u, plj;
  u6=4;
  xa=0;
  l=(c%28)+10;
  c3u=0;
  plj=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant plj == xa * u6;
  loop invariant c3u == xa * u6;
  loop invariant xa >= 0;
  loop invariant l + xa*(xa-1)/2 == (c % 28) + 10;
  loop invariant l + (xa * (xa - 1)) / 2 == ((\at(c,Pre) % 28) + 10);
  loop invariant l == ((\at(c, Pre) % 28) + 10) - xa * (xa - 1) / 2;
  loop assigns l, plj, xa, c3u;
*/
while (l>xa) {
      l = l - xa;
      plj = plj + u6;
      xa++;
      c3u = c3u + u6;
  }
}