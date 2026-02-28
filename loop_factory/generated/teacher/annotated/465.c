int main1(int k,int n){
  int v, e, a;

  v=k+8;
  e=0;
  a=e;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == k + 8;
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant a >= 0;
  loop invariant a % 8 == 0;
  loop assigns a;
*/
while (1) {
      a = a+4;
      a = a+a;
  }

}
