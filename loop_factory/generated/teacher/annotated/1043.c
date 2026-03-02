int main1(int a,int q){
  int n, t, e;

  n=44;
  t=0;
  e=3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant n == 44 && a == \at(a, Pre) && q == \at(q, Pre);
  loop invariant n == 44;
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant t >= 0;
  loop invariant e >= 1;

  loop invariant (t == 0 ==> e == 3);

  loop invariant e > 0;
  loop invariant e >= 3;

  loop invariant a == \at(a, Pre) && q == \at(q, Pre);
  loop assigns e, t;
*/
while (1) {
      e = e*e;
      t = t+1;
  }

}
