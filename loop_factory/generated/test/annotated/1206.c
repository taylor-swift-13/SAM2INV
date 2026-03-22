int main1(){
  int al, fg, v0t, prk, k3, t0, bwf;
  al=(1%35)+15;
  fg=(1%35)+15;
  v0t=1;
  prk=0;
  k3=0;
  t0=1;
  bwf=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= al <= 32;
  loop invariant 0 <= fg <= 32;
  loop invariant al + fg <= 32;
  loop invariant 5 <= bwf;
  loop invariant (al % 16 == 0);
  loop invariant (fg % 16 == 0);
  loop assigns al, fg, v0t, prk, k3, t0, bwf;
*/
while (al!=fg) {
      if (al>fg) {
          al = al - fg;
          v0t = v0t - prk;
          k3 -= t0;
      }
      else {
          fg = fg - al;
          prk -= v0t;
          t0 -= k3;
      }
      bwf = bwf + fg;
  }
}