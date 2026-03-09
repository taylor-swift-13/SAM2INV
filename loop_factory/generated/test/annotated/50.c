int main1(){
  int kcj, r6x, vyh, e, w, byo9;
  kcj=(1%29)+5;
  r6x=1;
  vyh=0;
  e=0;
  w=7;
  byo9=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant byo9 == vyh * r6x;
  loop invariant e == 7*vyh - vyh*(vyh-1)/2;
  loop invariant (vyh + w) == 7;
  loop invariant 0 <= vyh;
  loop invariant vyh <= kcj;
  loop invariant 0 <= w;
  loop invariant byo9 == vyh;
  loop assigns e, vyh, w, byo9;
*/
while (vyh<kcj&&w>0) {
      e = e + w;
      vyh++;
      w = w - 1;
      byo9 += r6x;
  }
}