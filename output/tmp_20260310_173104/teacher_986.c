int main1(int k,int n){
  int y, t, a;

  y=k-2;
  t=1;
  a=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre) && n == \at(n, Pre);
  loop invariant y == \at(k, Pre) - 2;
  loop invariant t == 1 || (t % 3 == 0 && t <= y);
  loop invariant 0 <= a && a <= 25;
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant t >= 1 && (t % 3 == 0 || t == 1);
  loop invariant a == 8 || a == 0 || a == 1 || a == 4 || a == 9 || a == 16 || a == 25;
  loop invariant a == 8 || a == 4 || a == 16;
  loop invariant t >= 1;
  loop invariant k == \at(k, Pre) && n == \at(n, Pre) && y == \at(k, Pre) - 2;
  loop invariant 0 <= a && a <= 25 && a % 2 == 0 && t >= 1 && (t == 1 || t % 3 == 0);
  loop invariant t >= 1 && (t == 1 || t % 3 == 0);
  loop invariant t == 1 || t % 3 == 0;
  loop invariant y == \at(k, Pre) - 2 && k == \at(k, Pre) && n == \at(n, Pre);
  loop invariant 0 <= a && a <= 25 && t >= 1;
  loop invariant a >= 0 && a % 2 == 0;
  loop invariant y == k - 2;
  loop invariant (y >= 0) ==> t <= y + 1;
  loop assigns a, t;
*/
while (t<=y/3) {
      a = a%6;
      a = a*a;
      t = t*3;
  }
/*@
  assert !(t<=y/3) &&
         (k == \at(k, Pre) && n == \at(n, Pre));
*/


}
