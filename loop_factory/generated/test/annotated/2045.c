int main1(){
  int z, jhb, v, afc, u6t3, j;
  z=1*2;
  jhb=0;
  v=1;
  afc=1;
  u6t3=1;
  j=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant jhb >= 0;
  loop invariant jhb <= z;
  loop invariant j == 1;
  loop invariant u6t3 == j * v;
  loop invariant v >= 1;
  loop invariant afc >= 1;
  loop invariant afc <= 1 + jhb;
  loop invariant z == 2;
  loop assigns v, jhb, u6t3, afc;
*/
while (1) {
      if (!(jhb < z)) {
          break;
      }
      v = (v + u6t3) * afc;
      jhb += 1;
      u6t3 = j * v;
      afc = afc+(u6t3%2);
  }
}