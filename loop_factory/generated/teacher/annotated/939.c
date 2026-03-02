int main1(int a,int p){
  int m, j, x;

  m=p-7;
  j=0;
  x=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == 0 && m == p - 7;
  loop invariant a == \at(a, Pre) && p == \at(p, Pre) && (x == 4 || x == -8);
  loop invariant j == 0;
  loop invariant m == p - 7;
  loop invariant x == 4 || x == j - 8;
  loop invariant x <= 4;
  loop invariant x >= -8;
  loop invariant a == \at(a, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant m == \at(p, Pre) - 7;
  loop invariant (x == 4) || (x == j - 8);
  loop invariant j == 0 && a == \at(a, Pre);
  loop invariant p == \at(p, Pre) && m == \at(p, Pre) - 7 && (x == 4 || x == j - 8);
  loop invariant p == \at(p, Pre) && a == \at(a, Pre) && j == 0;
  loop invariant x >= j - 8;
  loop invariant j == 0 && m == \at(p, Pre) - 7 && p == \at(p, Pre) && a == \at(a, Pre) && (x == 4 || x == -8);
  loop invariant 0 <= j;
  loop invariant j == 0 && (x == 4 || x == -8) && m == p - 7;
  loop invariant p == \at(p, Pre) && a == \at(a, Pre);
  loop assigns x;
*/
while (1) {
      x = x+3;
      x = j-8;
  }

}
