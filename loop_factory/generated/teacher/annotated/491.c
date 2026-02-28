int main1(int k,int n){
  int y, j, o, b;

  y=k;
  j=0;
  o=j;
  b=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o >= 0;
  loop invariant o % 5 == 0;
  loop invariant b % 2 == 0;
  loop invariant b >= 2;
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant y == k;
  loop invariant b >= 2 * o;
  loop assigns b, o;
*/
while (1) {
      o = o+4;
      o = o+1;
      b = b+o;
      b = b+b;
  }

}
