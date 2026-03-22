int main1(){
  int e, r5, dn0h, yth, e3, cev;
  e=(1%31)+8;
  r5=0;
  dn0h=0;
  yth=0;
  e3=(1%18)+5;
  cev=e;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant cev - e * yth == 9;
  loop invariant r5 >= 0;
  loop invariant r5 == dn0h;
  loop invariant yth == r5;
  loop invariant cev == e * (r5 + 1);
  loop invariant e3 + r5 == 6;
  loop invariant r5 <= 6;
  loop assigns cev, dn0h, e3, r5, yth;
*/
while (e3>=1) {
      r5 = r5+1*1;
      dn0h = dn0h+1*1;
      e3 = e3 - 1;
      cev = cev + e;
      yth = yth+1*1;
  }
}