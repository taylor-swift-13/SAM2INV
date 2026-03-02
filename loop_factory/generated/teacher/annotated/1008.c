int main1(int n,int p){
  int l, j, c;

  l=60;
  j=3;
  c=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == 3 && l == 60 && p == \at(p, Pre);
  loop invariant n == \at(n, Pre) && c >= \at(p, Pre);
  loop invariant j == 3;
  loop invariant l == 60;
  loop invariant p == \at(p, Pre) && n == \at(n, Pre);
  loop invariant c >= \at(p, Pre);
  loop invariant j == 3 && l == 60;
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant (c - \at(p, Pre)) % 4 == 0;
  loop invariant j == 3 && l == 60 && l >= 6;
  loop invariant c == \at(p, Pre) || c >= \at(p, Pre) + 3;
  loop invariant j == 3 && l == 60 && p == \at(p, Pre) && n == \at(n, Pre);

  loop invariant j == 3 && l == 60 && n == \at(n, Pre) && p == \at(p, Pre);
  loop invariant (c == \at(p, Pre) || c >= \at(p, Pre) + 3) && l >= 6 && c >= \at(p, Pre);
  loop invariant l >= 6 && c >= \at(p, Pre) && ((c - \at(p, Pre)) % 4) == 0;
  loop assigns c;
*/
while (1) {
      c = c+3;
      if (j+6<=j+l) {
          c = c+1;
      }
  }

}
