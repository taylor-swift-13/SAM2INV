int main1(int y,int l){
  int li3l, dh, w7ab, rh;
  li3l=41;
  dh=-4;
  w7ab=l+2;
  rh=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (dh == -4) ==> (l == \at(l,Pre));
  loop invariant (dh >= -3) ==> (l == w7ab + rh + y);
  loop invariant w7ab == \at(l,Pre) + 2;
  loop invariant li3l == 41;
  loop invariant rh == -3;
  loop invariant -4 <= dh <= li3l;
  loop assigns l, dh;
*/
while (dh<=li3l-1) {
      l = w7ab+rh+y;
      dh = dh + 1;
  }
}