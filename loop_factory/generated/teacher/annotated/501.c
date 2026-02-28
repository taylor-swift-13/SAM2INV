int main1(int b,int k){
  int i, t, n, v;

  i=b;
  t=0;
  n=b;
  v=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n - 4*t == b;
  loop invariant t >= 0;
  loop invariant n >= b;
  loop invariant i == b;

  loop invariant n == b + 4*t;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop assigns n, t;
*/
while (1) {
      if (t>=i) {
          break;
      }
      n = n+3;
      t = t+1;
      n = n+1;
  }

}
