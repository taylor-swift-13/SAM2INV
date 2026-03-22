int main1(int g){
  int m8, f6, c, iw, e, ow, sn, p;
  m8=g+3;
  f6=0;
  c=0;
  iw=0;
  e=0;
  ow=3;
  sn=5;
  p=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f6 == 3*c + iw;
  loop invariant e == f6;
  loop invariant 0 <= c;
  loop invariant iw == f6 % 3;
  loop invariant c == f6 / 3;
  loop invariant m8 == \at(g, Pre) + 3;
  loop invariant p == 2;
  loop invariant ow == 3 + f6;
  loop invariant sn >= ow;
  loop invariant 0 <= iw <= 2;
  loop assigns iw, e, c, f6, g, sn, ow;
*/
while (f6<m8) {
      iw += 1;
      e += 1;
      if (iw>=3) {
          iw = iw - 3;
          c = c + 1;
      }
      f6 = f6 + 1;
      if (f6+7<=iw+m8) {
          g++;
      }
      sn += f6;
      g = ow+sn+p;
      ow += 1;
      sn = ow+c;
      g += ow;
  }
}