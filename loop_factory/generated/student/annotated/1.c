int main1(int m,int n){
  int b, t, i;

  b=n-2;
  t=0;
  i=t;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i >= 0;
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);

  loop assigns i;
*/
while (1) {
      i = i+3;
  }

}
