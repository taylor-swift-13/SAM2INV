int main1(int e,int l){
  int b, pe7, vo01;
  b=l-8;
  pe7=0;
  vo01=pe7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vo01 == pe7;
  loop invariant pe7 >= 0;
  loop invariant (b >= 0) ==> (pe7 <= b);
  loop invariant b == l - 8;
  loop assigns vo01, pe7;
*/
while (1) {
      vo01 += 1;
      pe7++;
      if (pe7>=b) {
          break;
      }
  }
}