int main1(int q){
  int vqss, ynmp, fu, itd2, m6;
  vqss=76;
  ynmp=0;
  fu=0;
  itd2=0;
  m6=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (ynmp == 0) || (ynmp == vqss);
  loop invariant (ynmp != vqss) ==> (fu == 0 && itd2 == 0 && m6 == 0);
  loop invariant (ynmp == vqss) ==> (m6 == itd2);
  loop invariant (ynmp == 0 && fu == 0 && itd2 == 0 && m6 == 0)
                   || (ynmp == vqss && fu == q + 1 && itd2 == q && m6 == q);
  loop invariant ( (ynmp == 0 && fu == 0 && itd2 == 0 && m6 == 0)
                  || (ynmp == vqss && fu == q + 1 && itd2 == q && m6 == q) );
  loop invariant vqss == 76;
  loop assigns fu, itd2, m6, ynmp;
*/
while (1) {
      if (!(ynmp < vqss)) {
          break;
      }
      itd2 = itd2 + (fu += q, ynmp++, fu);
      fu = fu + 1;
      m6 = m6 + itd2;
      ynmp = vqss;
  }
}