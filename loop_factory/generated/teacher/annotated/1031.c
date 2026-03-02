int main1(int p,int q){
  int r, a, t, e;

  r=q+9;
  a=0;
  t=p;
  e=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == a;
  loop invariant t == \at(p, Pre) + 5 * a;
  loop invariant a >= 0;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant r == \at(q, Pre) + 9;
  loop invariant t - 5*e == \at(p, Pre);
  loop invariant a == e;
  loop invariant e >= 0;
  loop invariant t == \at(p, Pre) + 5 * e;
  loop invariant t == \at(p, Pre) + 5*e;
  loop invariant p == \at(p, Pre) && q == \at(q, Pre);
  loop invariant p == \at(p, Pre) && q == \at(q, Pre) && r == \at(q, Pre) + 9;
  loop invariant a == e && t == \at(p, Pre) + 5*e && a >= 0 && e >= 0;
  loop assigns t, e, a;
*/
while (1) {
      t = t+5;
      e = e+1;
      a = a+1;
  }

}
