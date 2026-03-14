int main1(int q){
  int ao, o, tj;
  ao=(q%20)+5;
  o=(q%20)+5;
  tj=(q%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ao == o;
  loop invariant o == tj;
  loop invariant q >= \at(q, Pre);
  loop assigns ao, o, tj, q;
*/
while (ao>0) {
      if (o>0) {
          if (tj>0) {
              ao -= 1;
              o--;
              tj--;
          }
      }
      q += tj;
  }
}