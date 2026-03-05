int main1(int a){
  int ams0, k3l, b;
  ams0=51;
  k3l=ams0+5;
  b=k3l;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == k3l;
  loop invariant k3l == ams0 + 5;
  loop invariant a >= \at(a, Pre);
  loop invariant ams0 == 51;
  loop invariant (a - \at(a, Pre)) % b == 0;
  loop assigns a, b;
*/
while (k3l>=ams0+1) {
      b = b*3;
      b = b/3;
      a += b;
  }
}