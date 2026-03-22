int main1(int n){
  int is, wjqc, nda, ku6;
  is=n;
  wjqc=1;
  nda=8;
  ku6=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ku6 == 0 || ku6 == 8;
  loop invariant is == n || is == (wjqc*3) - 1;
  loop invariant 0 <= ku6 <= nda;
  loop invariant (is >= 3 ==> ku6 == 0);
  loop invariant ((is == n && ku6 == 0) || (is == 2 && ku6 == 8));
  loop invariant (is == n ==> ku6 == 0);
  loop assigns ku6, is;
*/
while (1) {
      if (!(wjqc*3<=is)) {
          break;
      }
      ku6 = ku6 + nda;
      is = (wjqc*3)-1;
  }
}