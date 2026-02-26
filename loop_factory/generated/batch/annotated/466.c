int main1(int m,int n){
  int b, v, o;

  b=n+12;
  v=0;
  o=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o >= 6;
  loop invariant (o - 6) % 5 == 0;
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant b == \at(n, Pre) + 12;
  loop invariant b == n + 12;
  loop assigns o;
*/
while (1) {
      o = o+4;
      o = o+1;
  }

}
