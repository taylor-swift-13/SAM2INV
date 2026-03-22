int main1(){
  int ua3, l3f, ukf, e4dn;
  ua3=1*3;
  l3f=(1%40)+2;
  ukf=0;
  e4dn=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (ukf == 0) ==> (l3f == 3);
  loop invariant ua3 == 3;
  loop invariant e4dn >= -6;
  loop invariant l3f != ukf;
  loop invariant 1 <= l3f <= 3;
  loop invariant 0 <= ukf <= 3;
  loop assigns e4dn, l3f, ukf;
*/
while (1) {
      if (!(l3f!=ukf)) {
          break;
      }
      ukf = l3f;
      l3f = (l3f+ua3/l3f)/2;
      e4dn = e4dn + l3f;
  }
}