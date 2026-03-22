int main1(){
  int a, k, foy, ao1;
  a=(1%21)+13;
  k=a;
  foy=-2;
  ao1=k;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((k != 0) ==> (ao1 == k));
  loop invariant ((k == 0) ==> (foy == ao1*ao1));
  loop invariant k >= 0;
  loop invariant ao1 >= 14;
  loop invariant ao1 <= 15;
  loop invariant a == 14;
  loop invariant (k >= 1) ==> (ao1 == a);
  loop invariant (ao1 == a) ==> (foy == -2);
  loop invariant foy <= ao1 * ao1;
  loop assigns ao1, foy, k;
*/
while (k>=1) {
      ao1 += 1;
      foy = ao1*ao1;
      k = 0;
  }
}