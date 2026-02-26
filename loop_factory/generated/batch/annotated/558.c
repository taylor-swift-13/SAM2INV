int main1(int k,int m){
  int p, i, t;

  p=(k%22)+5;
  i=3;
  t=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k,Pre);
  loop invariant m == \at(m,Pre);
  loop invariant p == (k % 22) + 5;
  loop invariant t >= p;
  loop invariant p == (\at(k, Pre) % 22) + 5;

  loop assigns t;
*/
while (1) {
      t = t+3;
      t = t*t;
  }

}
