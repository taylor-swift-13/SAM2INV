int main1(int m,int p){
  int n, j, k, r, i, a;

  n=30;
  j=0;
  k=p;
  r=0;
  i=3;
  a=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j >= 0;
  loop invariant j <= n;
  loop invariant i == 3 + j * k;
  loop invariant r == 3 * j + k * j * (j - 1) / 2;
  loop invariant k == p;
  loop invariant n == 30;
  loop invariant k == \at(p, Pre);
  loop invariant 0 <= j;

  loop assigns r, i, j;
*/
while (j<n) {
      r = r+i;
      i = i+k;
      j = j+1;
  }

}
