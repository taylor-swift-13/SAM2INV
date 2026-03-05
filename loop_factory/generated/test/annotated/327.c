int main1(int k){
  int ou, y;
  ou=70;
  y=(k%28)+10;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ou == 70;
  loop invariant ((k - \at(k, Pre)) % ou) == 0;
  loop invariant y == 1 || y == (\at(k, Pre) % 28) + 10;
  loop invariant k >= \at(k, Pre);
  loop invariant (k - \at(k, Pre)) <= ou;
  loop assigns y, k;
*/
while (y>y) {
      y = y - y;
      y++;
      k += ou;
  }
}