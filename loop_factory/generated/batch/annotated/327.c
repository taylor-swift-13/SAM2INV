int main1(int a,int p){
  int b, d, t;

  b=61;
  d=b;
  t=d;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant d % 3 == 1;

  loop invariant t == 0 || t == 61;
  loop invariant t <= d;
  loop invariant t == 0 || t == d;
  loop invariant d % 3 == b % 3;
  loop invariant 1 <= d;
  loop invariant d <= b;
  loop invariant b == 61;
  loop invariant (1 <= d);
  loop invariant (d <= 61);

  loop invariant d <= 61;
  loop assigns t, d;
*/
while (d>2) {
      t = t-t;
      d = d-3;
  }

}
