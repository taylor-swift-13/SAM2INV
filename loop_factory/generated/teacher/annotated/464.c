int main1(int k,int n){
  int m, a, v, t;

  m=70;
  a=0;
  v=a;
  t=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 4*v == t*t + 11*t;
  loop invariant t >= 0;
  loop invariant t % 4 == 0;
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant m == 70;
  loop invariant 4*v == t*(t+11);
  loop invariant v >= 0;
  loop assigns v, t;
*/
while (1) {
      v = v+3;
      t = t+3;
      v = v+t+t;
      v = v+1;
      t = t+1;
      v = v+5;
  }

}
