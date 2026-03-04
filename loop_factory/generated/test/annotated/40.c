int main1(int t){
  int sh, xv, x5x, lic;
  sh=(t%21)+7;
  xv=sh;
  x5x=(t%20)+5;
  lic=xv;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == \at(t, Pre) + (((\at(t, Pre) % 20) + 5) - x5x) * ((\at(t, Pre) % 21) + 7);
  loop invariant t - \at(t,Pre) == ((\at(t,Pre) % 20) + 5 - x5x) * ((\at(t,Pre) % 21) + 7);
  loop invariant t == \at(t,Pre) + (((\at(t,Pre) % 20) + 5) - x5x) * xv;
  loop invariant xv == ((\at(t,Pre) % 21) + 7);
  loop assigns x5x, t, lic;
*/
while (1) {
      if (!(x5x>0)) {
          break;
      }
      x5x = x5x - 1;
      t += xv;
      lic += t;
  }
}