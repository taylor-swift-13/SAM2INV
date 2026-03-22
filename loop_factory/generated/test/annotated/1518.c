int main1(){
  int v, tz, ztb, ae7, ydm, t59, h27, ldk, yz;
  v=1;
  tz=0;
  ztb=v;
  ae7=3;
  ydm=v;
  t59=v;
  h27=tz;
  ldk=13;
  yz=tz;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant tz == 0;
  loop invariant ztb >= 1;
  loop invariant h27 >= 0;
  loop invariant ae7 >= 3;
  loop invariant t59 >= 1;
  loop invariant ydm >= 1;
  loop invariant 0 <= yz <= 1;
  loop invariant v <= tz + 3;
  loop invariant ldk == 13;
  loop invariant ((tz == 0 && v == 1) || (v == tz + 3));
  loop invariant (ae7 - 3) % 5 == 0;
  loop assigns ztb, v, ldk, h27, yz, ae7, ydm, t59;
*/
while (1) {
      if (!(tz+4<=v)) {
          break;
      }
      if (!(!(tz<v/2))) {
          ztb = ztb + 1;
      }
      else {
          ztb = ztb + ae7;
      }
      if (ldk+6<v) {
          ldk = h27-ldk;
      }
      h27 += ztb;
      yz = yz + 1;
      ae7 = ae7 + 5;
      ydm = ydm + ae7;
      t59 += ydm;
      t59 += tz;
      v = (tz+4)-1;
  }
}