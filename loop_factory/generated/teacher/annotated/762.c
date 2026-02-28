int main1(int k,int m,int n,int q){
  int l, o, v, i, r;

  l=80;
  o=0;
  v=n;
  i=m;
  r=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v >= n;
  loop invariant i == m + (v - n) * n + ((v - n) * (v - n + 1)) / 2;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant i == m + ((v - n) * (n + 1)) + (((v - n) * (v - n - 1)) / 2);
  loop invariant 2*(i - \at(m, Pre)) == (v - \at(n, Pre))*(v - \at(n, Pre)) + (2 * \at(n, Pre) + 1) * (v - \at(n, Pre));

  loop invariant i == m + n*(v - n) + ((v - n) * (v - n + 1)) / 2;
  loop assigns v, i;
*/
while (1) {
      v = v+1;
      i = i+v;
  }

}
