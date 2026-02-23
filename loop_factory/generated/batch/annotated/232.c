int main1(int a,int m){
  int n, j, c;

  n=56;
  j=n;
  c=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant n == 56;
  loop invariant 0 <= j;
  loop invariant j <= 56;
  loop invariant j % 2 == 0 && ((c == a - n) || (c == -8 && j == 56));
  loop invariant j >= 0;
  loop invariant (j % 2) == 0 && (c == -8 || c == a - n);
  loop invariant j % 2 == 0;
  loop invariant (j < 56) ==> c == a - n;
  loop invariant (j % 2) == 0;
  loop invariant (c == -8) || (c == a - n);
  loop assigns c, j;
*/
while (j>=2) {
      c = a-n;
      j = j-2;
  }

}
