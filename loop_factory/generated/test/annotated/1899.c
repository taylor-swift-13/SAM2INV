int main1(){
  int ywx, ev6d, v, c3n, f41, rh, hdv, em, nk, a3, q3;
  ywx=1;
  ev6d=0;
  v=0;
  c3n=5;
  f41=0;
  rh=ev6d;
  hdv=ev6d;
  em=ywx;
  nk=ywx;
  a3=0;
  q3=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ev6d;
  loop invariant ev6d <= ywx;
  loop invariant ((ev6d % 2 == 0) ==> (c3n == 5)) && ((ev6d % 2 != 0) ==> (c3n == -5));
  loop invariant em == 1 + ((ev6d + 4) / 5);
  loop invariant nk == 1 + ((ev6d + 3) / 5);
  loop invariant a3 == ((ev6d + 2) / 5);
  loop invariant f41 == ((ev6d + 1) / 5);
  loop invariant q3 == -6 + (ev6d / 5);
  loop assigns em, ev6d, nk, a3, f41, q3, rh, hdv, c3n;
*/
while (ev6d < ywx) {
      if ((ev6d % 5) == 0) {
          em = em + 1;
      }
      else {
      }
      if ((ev6d % 5) == 1) {
          nk++;
      }
      else {
      }
      if ((ev6d % 5) == 2) {
          a3++;
      }
      else {
      }
      if ((ev6d % 5) == 3) {
          f41 += 1;
      }
      else {
      }
      if ((ev6d % 5) == 4) {
          q3 += 1;
      }
      else {
      }
      ev6d++;
      rh += q3;
      c3n += rh;
      c3n = v-c3n;
      rh += v;
      hdv += c3n;
      c3n += rh;
  }
}