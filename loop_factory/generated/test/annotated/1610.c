int main1(){
  int qc, w, y4, wew, dufv, f0, rl, c1pc;
  qc=50;
  w=qc+1;
  y4=0;
  wew=0;
  dufv=0;
  f0=(1%18)+5;
  rl=qc;
  c1pc=qc;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y4 == dufv;
  loop invariant y4 == wew;
  loop invariant w == qc + 1;
  loop invariant 0 <= f0;
  loop invariant f0 <= 6;
  loop invariant f0 + y4 == (1%18) + 5;
  loop invariant rl >= 0;
  loop invariant c1pc >= 0;
  loop invariant 0 <= y4 <= 6;
  loop invariant qc == 50;
  loop assigns y4, dufv, wew, f0, rl, c1pc;
*/
while (f0>0) {
      y4 = y4+1*1;
      dufv = dufv+1*1;
      wew = wew+1*1;
      f0--;
      if (w+5<=f0+qc) {
          c1pc = c1pc*rl;
      }
      if (rl+3<qc) {
          rl = rl%9;
      }
      rl = rl*4+5;
      c1pc = c1pc*rl+5;
      c1pc = rl*rl;
  }
}