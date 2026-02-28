int main1(int a,int b,int m,int q){
  int t, i, f;

  t=(q%13)+13;
  i=0;
  f=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == (\at(q, Pre) % 13) + 13;
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant f % 3 == 0;
  loop invariant i == 0;
  loop invariant f >= 0;

  loop invariant t <= 25;
  loop invariant t == (q % 13) + 13;

  loop assigns f;
*/
while (1) {
      f = f+3;
      if (m<t+5) {
          f = f-f;
      }
      f = f+i;
  }

}
