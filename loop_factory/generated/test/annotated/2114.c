int main1(){
  int i3zr, u9, a2, ny, r0;
  i3zr=1;
  u9=i3zr;
  a2=3*i3zr;
  ny=2*i3zr;
  r0=i3zr;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (a2 + (u9 * (u9 - 1)) / 2) == 3;
  loop invariant (ny + r0 * u9) == (2 + r0);
  loop invariant u9 >= 0;
  loop invariant u9 <= i3zr;
  loop invariant a2 + (u9*(u9-1))/2 == 3*i3zr + (i3zr*(i3zr-1))/2;
  loop invariant ny + u9*r0 == 2*i3zr + i3zr*r0;
  loop invariant r0 == i3zr;
  loop invariant 2*a2 + u9*(u9-1) == 6*i3zr + i3zr*(i3zr-1);
  loop invariant 0 <= u9;
  loop invariant i3zr == 1;
  loop invariant (a2 + ny * r0 + (u9 * (u9 + 1)) / 2) == 6;
  loop assigns u9, ny, a2;
*/
while (u9 > 0) {
      u9--;
      ny += r0;
      a2 += u9;
  }
}