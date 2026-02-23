int main1(int b){
  int a, k, o;

  a=54;
  k=a;
  o=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == 54;
  loop invariant b == \at(b, Pre);
  loop invariant k <= 54;
  loop invariant k >= 0;
  loop invariant k <= a;
  loop invariant 0 <= k;
  loop assigns k;
*/
while (k>=1) {
      k = k-1;
  }

}
