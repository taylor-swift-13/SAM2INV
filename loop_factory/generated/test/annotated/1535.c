int main1(){
  int rg5, d, m3, qh9, h, cq, irg, p3l8;
  rg5=(1%7)+5;
  d=0;
  m3=d;
  qh9=d;
  h=d;
  cq=0;
  irg=0;
  p3l8=-1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rg5 == 6;
  loop invariant p3l8 == -1;
  loop invariant irg == 0;
  loop invariant h == 0;
  loop invariant cq == 0;
  loop invariant m3 == -(d % 2);
  loop invariant qh9 == (d % 2);
  loop invariant 0 <= d <= rg5;
  loop assigns d, m3, qh9, cq, irg, h;
*/
while (1) {
      if (!(d < rg5)) {
          break;
      }
      d++;
      if ((d % 2) == 0) {
          m3++;
          qh9 -= 1;
      }
      else {
          m3 -= 1;
          qh9++;
      }
      if (!(!(cq+5<rg5))) {
          cq = cq*cq+p3l8;
      }
      irg = irg+qh9-qh9;
      cq = cq/2;
      h = h*2;
      if ((d%7)==0) {
          h = h*irg;
      }
      h = h*irg;
  }
}