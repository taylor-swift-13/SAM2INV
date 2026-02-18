int main1(int b,int m,int n,int p){
  int l, i, v, u;

  l=41;
  i=0;
  v=m;
  u=6;

/* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i <= l;
  loop invariant v == m + 3*i;
  loop invariant u == 6 + i;
  loop invariant i >= 0;
  loop invariant l == 41;
  loop invariant 0 <= i <= l;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant 0 <= i;
  loop assigns i, v, u;
  loop variant l - i;
*/
while (i<l) {
      v = v+3;
      u = u+1;
      i = i+1;
  }

}