int main1(int n,int p){
  int l, j, c;

  l=60;
  j=3;
  c=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == 3 && l == 60 && p == \at(p, Pre) && n == \at(n, Pre);

  loop invariant j + 6 <= j + l;
  loop invariant l == 60;
  loop invariant j == 3;
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);

  loop invariant (p == -6) ==> (c == -6);

  loop invariant 6 <= l;

  loop invariant j+6 <= j + l;
  loop invariant l == 60 && j == 3 && j+6 <= j + l;
  loop invariant p == \at(p, Pre) && n == \at(n, Pre);
  loop assigns c;
*/
while (1) {
      c = c+3;
      if (j+6<=j+l) {
          c = c*2;
      }
  }

}
