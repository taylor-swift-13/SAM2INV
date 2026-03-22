int main1(){
  int w6, z9, eiw8, bd4a, vc, xd, u;
  w6=8;
  z9=w6;
  eiw8=5;
  bd4a=0;
  vc=w6;
  xd=-5;
  u=z9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 5 <= eiw8 <= w6 + 1;
  loop invariant bd4a >= 0;
  loop invariant xd >= -5;
  loop invariant vc >= 8;
  loop invariant u >= 8;
  loop invariant w6 == 8;
  loop invariant vc == 8 + ((eiw8 + 6) * (eiw8 - 5)) / 2;
  loop invariant bd4a == ((eiw8 - 1) * eiw8 * (2 * eiw8 - 1)) / 6 - 30;
  loop invariant eiw8 >= 5;
  loop assigns bd4a, eiw8, xd, vc, u;
*/
while (1) {
      if (!(eiw8<=w6)) {
          break;
      }
      bd4a = bd4a+eiw8*eiw8;
      eiw8 = eiw8 + 1;
      xd = xd + u;
      vc = vc + eiw8;
      u = u + vc;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= eiw8;
  loop invariant 0 <= w6;
  loop invariant 0 <= u;
  loop invariant 0 <= vc;
  loop invariant (eiw8 % 2) == 1;
  loop assigns w6, eiw8, bd4a, u;
*/
while (1) {
      if (!(u<vc)) {
          break;
      }
      w6 = w6 + u;
      eiw8 += 2;
      bd4a += xd;
      u = u + 1;
      bd4a += 1;
  }
}