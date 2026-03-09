int main1(){
  int aik6, mk, gn, ke, v;
  aik6=1*3;
  mk=0;
  gn=0;
  ke=mk;
  v=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= gn;
  loop invariant gn <= aik6;
  loop invariant v == 8 + gn * aik6;
  loop invariant ((gn <= (aik6/2)) && ke == 0) || ((gn > (aik6/2)) && ke == 4 * (gn - (aik6/2)));
  loop assigns gn, ke, v;
*/
while (gn<aik6) {
      if (!(!(gn>=aik6/2))) {
          ke += 4;
      }
      gn = gn + 1;
      v = v + aik6;
  }
}