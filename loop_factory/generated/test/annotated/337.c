int main1(){
  int rv, u0, qe;
  rv=121;
  u0=-1;
  qe=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rv == 121;
  loop invariant qe >= 0;
  loop invariant qe <= rv;
  loop invariant u0 >= -1;
  loop invariant (qe > 0) ==> (qe == 1);
  loop invariant (qe == 1) ==> (u0 >= 0);
  loop assigns qe, u0;
*/
while (qe>0&&qe<=rv) {
      if (qe>qe) {
          qe -= qe;
      }
      else {
          qe = 0;
      }
      qe++;
      u0 = u0 + 1;
  }
}