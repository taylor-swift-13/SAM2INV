int main1(int x){
  int e1, gn, ua, fu, z;
  e1=134;
  gn=e1+2;
  ua=6;
  fu=6;
  z=gn;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z - e1*gn == (1 - e1)*(e1 + 2);
  loop invariant fu == ua;
  loop invariant gn >= e1 + 2;
  loop invariant ua >= 6;
  loop invariant (fu - gn) == (4 - e1);
  loop invariant e1 == 134;
  loop assigns fu, ua, z, gn;
*/
while (1) {
      if (!(gn<e1)) {
          break;
      }
      fu = fu + 1;
      ua++;
      z += e1;
      gn = gn + 1;
  }
}