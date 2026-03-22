int main1(int o,int b){
  int tt, i6, w8, ux, ga, mbsj, kff8, gv, es;
  tt=41;
  i6=0;
  w8=i6;
  ux=0;
  ga=tt;
  mbsj=0;
  kff8=-2;
  gv=0;
  es=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kff8 == -2 + i6;
  loop invariant 0 <= i6 <= tt;
  loop invariant tt == 41;
  loop invariant gv == i6*(i6 - 1)/2;
  loop assigns w8, ux, ga, mbsj, i6, b, es, kff8, gv, o;
*/
while (i6 < tt) {
      w8 = (w8 + o) % (b + 1);
      ux = (ux + w8) % (b + 1);
      ga = (ga + ux) % (b + 1);
      mbsj = (mbsj + ga) % (b + 1);
      i6 = i6 + 1;
      if (b+1<tt) {
          b = w8+(-8);
      }
      if ((i6%3)==0) {
          es = kff8-es;
      }
      kff8++;
      gv += 1;
      o = o + ux;
      gv = gv + kff8;
      if (!(!(b<es+2))) {
          b += 1;
      }
  }
}