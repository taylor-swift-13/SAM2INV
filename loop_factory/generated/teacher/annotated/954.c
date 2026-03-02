int main1(int m,int q){
  int g, a, n;

  g=q;
  a=0;
  n=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == \at(q, Pre);
  loop invariant m == \at(m, Pre) && q == \at(q, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant g == q && q == \at(q, Pre);
  loop invariant g == q;

  loop invariant n <= 2147483647;

  loop assigns n;
*/
while (1) {
      n = n+3;
      if (n+7<g) {
          n = n%2;
      }
      else {
          n = n*n+n;
      }
  }

}
