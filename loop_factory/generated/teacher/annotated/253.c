int main1(int a,int m){
  int x, j, i, b;

  x=35;
  j=x;
  i=5;
  b=3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant (i == x) || (((i - 5) % 6) == 0 && 5 <= i && i <= x);
  loop invariant 5 <= i;
  loop invariant i <= x;
  loop invariant j == 35;
  loop invariant x == 35;
  loop invariant i >= 5;
  loop invariant j >= 4;
  loop invariant (i == 5) || (i == 11) || (i == 17) || (i == 23) || (i == 29) || (i == 35);
  loop invariant 5 <= i && i <= x && ((i - 5) % 6 == 0 || i == x);
  loop invariant i % 6 == 5;
  loop assigns i;
*/
while (j-4>=0) {
      if (i+6<=x) {
          i = i+6;
      }
      else {
          i = x;
      }
  }

}
