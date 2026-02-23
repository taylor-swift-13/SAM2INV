int main1(int k,int q){
  int m, a, v, j;

  m=k;
  a=0;
  v=k;
  j=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant 0 <= a;
  loop invariant m == k;
  loop invariant v == k;
  loop invariant q == \at(q, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant a >= 0;
  loop invariant (m < 0) || (a <= m);
  loop invariant (a == 0) ==> (j == q);
  loop assigns a, j;
*/
while (a<m) {
      j = j+j;
      j = j+v;
      a = a+1;
  }

}
