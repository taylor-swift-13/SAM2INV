int main1(int f,int h){
  int pf, ywx;
  pf=0;
  ywx=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pf == 0;
  loop invariant f == \at(f, Pre);
  loop invariant h == \at(h, Pre);
  loop invariant 0 <= ywx;
  loop invariant ywx <= 0;
  loop assigns ywx, h, f;
*/
while (ywx!=ywx) {
      if (ywx>ywx) {
          ywx -= ywx;
          ywx += ywx;
      }
      else {
          ywx -= ywx;
          ywx += ywx;
      }
      h += ywx;
      f += pf;
  }
}