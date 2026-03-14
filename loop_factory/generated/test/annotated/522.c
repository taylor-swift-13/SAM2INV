int main1(){
  int yu0, oj, bi, swn, izp, mv6x, od;
  yu0=1+19;
  oj=0;
  bi=2;
  swn=0;
  izp=yu0;
  mv6x=yu0;
  od=oj;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mv6x - yu0 == swn;
  loop invariant bi - swn == 2;
  loop invariant izp - yu0 == 3*swn;
  loop invariant od == 2*swn + swn*(swn+1)/2;
  loop invariant oj <= yu0;
  loop invariant 0 <= swn;
  loop assigns bi, mv6x, swn, izp, od, oj;
*/
while (oj<=yu0-1) {
      bi += 1;
      mv6x += 1;
      swn += 1;
      izp = izp + 3;
      od = od + bi;
      oj = yu0;
  }
}