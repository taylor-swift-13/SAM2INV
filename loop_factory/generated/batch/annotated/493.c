int main1(int k,int q){
  int d, a, i, v;

  d=61;
  a=0;
  i=6;
  v=d;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d == 61;
  loop invariant i == 3*a + 6;
  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant a <= d;
  loop invariant a >= 0;
  loop invariant i <= 3*d + 6;
  loop invariant 0 <= a;
  loop assigns i, a;
*/
while (1) {
      if (a>=d) {
          break;
      }
      i = i+2;
      a = a+1;
      i = i+1;
  }

}
