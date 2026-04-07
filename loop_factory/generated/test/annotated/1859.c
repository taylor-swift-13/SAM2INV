int main1(int c,int g){
  int xn, f4, w1g, xeh, vv, bbl4, r, l4j, lu, p8f;
  xn=39;
  f4=0;
  w1g=f4;
  xeh=-2;
  vv=c;
  bbl4=c+5;
  r=-2;
  l4j=f4;
  lu=0;
  p8f=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f4 == 0;
  loop invariant r == -2;
  loop invariant w1g == 0;
  loop invariant l4j == 0;
  loop invariant vv == c;
  loop invariant 0 <= f4 <= xn;
  loop invariant lu == 0;
  loop invariant c == \at(c,Pre);
  loop invariant g == \at(g,Pre);
  loop assigns w1g, xeh, vv, p8f, bbl4, r, l4j, lu, xn;
*/
while (1) {
      if (!(f4+1<=xn)) {
          break;
      }
      if (f4%6==3) {
          w1g++;
      }
      else {
          xeh++;
      }
      if (f4%6==4) {
          vv += 1;
      }
      else {
      }
      p8f = (p8f+vv)%4;
      bbl4 = (xeh)+(bbl4);
      r = r + w1g;
      l4j = (l4j+w1g)%2;
      bbl4 += 1;
      xn = (f4+1)-1;
      if (r+3<xn) {
          lu = lu + 1;
      }
      else {
          bbl4 += 1;
      }
  }
}