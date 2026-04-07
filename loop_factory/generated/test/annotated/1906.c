int main1(int x,int t){
  int t1, oo, stz, n, cp82, ml, f, yv, tgs;
  t1=x+6;
  oo=0;
  stz=oo;
  n=oo;
  cp82=oo;
  ml=oo;
  f=t;
  yv=4;
  tgs=x;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant oo >= 0;
  loop invariant f == \at(t, Pre) + 2*oo;
  loop invariant t == \at(t, Pre) + oo * t1;
  loop invariant n == oo / 2;
  loop invariant t1 == \at(x, Pre) + 6;
  loop assigns oo, stz, n, cp82, ml, x, f, t, yv, tgs;
*/
while (1) {
      if (!(oo < t1)) {
          break;
      }
      oo = oo + 1;
      if (!(!((oo % 2 == 0)))) {
          stz += x;
          n += 1;
      }
      else {
          cp82 += t;
          ml -= 1;
      }
      if (oo+2<=x+t1) {
          x = x + yv;
      }
      f = f + 1;
      t = t + t1;
      f = f + 1;
      yv += f;
      tgs += oo;
  }
}