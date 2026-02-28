int main1(int a,int q){
  int n, v, j;

  n=q;
  v=0;
  j=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant n == \at(q, Pre);
  loop invariant v >= 0 && j >= q && ((n >= 7) ==> (j == q + v)) && ((n < 7) ==> (j == q));
  loop invariant n == q;
  loop invariant j >= q;
  loop invariant v >= 0;
  loop invariant (q >= 7) ==> (j == q + v);
  loop assigns j, v;
*/
while (1) {
      if (v+7<=v+n) {
          j = j+1;
      }
      v = v+1;
  }

}
