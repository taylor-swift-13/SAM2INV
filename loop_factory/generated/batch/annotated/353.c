int main1(int k,int n){
  int m, o, y;

  m=(k%12)+6;
  o=0;
  y=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y % 5 == 0;
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant m == ((\at(k, Pre)) % 12) + 6;
  loop invariant 0 <= y;
  loop invariant m == (\at(k, Pre) % 12) + 6;
  loop invariant y >= 0;
  loop invariant m == ((\at(k,Pre) % 12) + 6);
  loop invariant m == (\at(k, Pre) % 12 + 6);
  loop assigns y;
*/
while (1) {
      y = y+4;
      y = y+1;
  }

}
