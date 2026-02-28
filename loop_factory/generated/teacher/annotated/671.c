int main1(int b,int k,int n,int q){
  int v, a, j, s, t, p, e, d;

  v=74;
  a=0;
  j=b;
  s=-8;
  t=0;
  p=5;
  e=q;
  d=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant v == 74;
  loop invariant s >= -8;
  loop invariant 4*j - ((s*s*s*s) + (2*(s*s*s)) + (s*s)) == 4*\at(b,Pre) - 3136;


  loop assigns s, j;
*/
while (1) {
      s = s+1;
      j = j+s*s*s;
  }

}
