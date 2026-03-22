int main1(int m){
  int l6m, q, u9, u8, eey, ly;
  l6m=m+10;
  q=0;
  u9=1;
  u8=6;
  eey=0;
  ly=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q >= 0;
  loop invariant eey >= 0;
  loop invariant ly >= 0;
  loop invariant m - \at(m,Pre) >= q + eey;
  loop invariant l6m == \at(m, Pre) + 10;
  loop invariant u8 == 6*(eey+1);
  loop invariant ly <= 2*eey;
  loop invariant u9 == 1 + 3*eey*(eey+1);
  loop assigns q, eey, u9, ly, u8, m;
*/
while (eey<=l6m) {
      q += u9;
      eey += 1;
      u9 = u9 + u8;
      ly = ly+(q%3);
      u8 += 6;
      m = m+u9+eey;
  }
}