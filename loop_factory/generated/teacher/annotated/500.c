int main1(int n,int p){
  int y, k, i, o;

  y=p;
  k=0;
  i=n;
  o=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i >= \at(n, Pre);
  loop invariant (i - \at(n, Pre)) % 5 == 0;
  loop invariant o * 10 == (i - \at(n, Pre)) * (i + \at(n, Pre) + 7);
  loop invariant y == p;

  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant i >= n;
  loop invariant ((i - n) % 5) == 0;

  loop invariant ((i - \at(n, Pre)) % 5 == 0);

  loop assigns i, o;
*/
while (1) {
      i = i+4;
      i = i+1;
      o = o+i;
      o = o+1;
  }

}
