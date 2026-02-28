int main1(int p){
  int l, k, e, j;

  l=p-8;
  k=0;
  e=l;
  j=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == \at(p, Pre) - 8;
  loop invariant e == (\at(p, Pre) - 8) + k;
  loop invariant j == \at(p, Pre) + k*( (\at(p, Pre) - 8) ) + k*(k+1)/2;
  loop invariant 0 <= k;
  loop invariant k >= 0;

  loop invariant e == l + k;
  loop invariant j == p + k*l + k*(k+1)/2;
  loop invariant l == p - 8;
  loop invariant p == \at(p, Pre);
  loop invariant j == \at(p, Pre) + k*l + (k*(k+1))/2;

  loop invariant k >= 0 && (l < 0 || k <= l + 1);
  loop assigns e, j, k;
*/
while (k<=l-1) {
      e = e+1;
      j = j+e;
      k = k+1;
  }

}
