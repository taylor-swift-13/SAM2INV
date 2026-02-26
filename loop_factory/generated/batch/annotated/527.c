int main1(int p,int q){
  int n, x, i, r;

  n=q+19;
  x=3;
  i=p;
  r=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (r == n) || (r == 2*i - 4);
  loop invariant (i >= p);
  loop invariant ((i - p) % 2) == 0;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant n == q + 19;
  loop invariant i >= p;
  loop invariant (i - p) % 2 == 0;
  loop invariant (i == p && r == n) || (i != p && r == 2*i - 4);
  loop invariant (i == p) || (r == 2*i - 4);
  loop invariant n == \at(q, Pre) + 19;
  loop invariant (i == p && r == n) || (r == 2*i - 4);
  loop assigns i, r;
*/
while (1) {
      r = i;
      i = i+2;
      r = r+r;
  }

}
