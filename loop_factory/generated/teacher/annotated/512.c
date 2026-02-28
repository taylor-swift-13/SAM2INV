int main1(int a,int k){
  int n, v, u;

  n=k;
  v=3;
  u=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == k;
  loop invariant (u == a) || (u == 0);
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(k, Pre);
  loop invariant u == \at(a, Pre) || u == 0;
  loop assigns u;
*/
while (1) {
      u = u+2;
      u = u-u;
  }

}
