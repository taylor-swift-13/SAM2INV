int main1(int a,int p){
  int v, t, f;

  v=p;
  t=v;
  f=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == 0 && v == \at(p, Pre);
  loop invariant p == \at(p, Pre) && t <= \at(p, Pre);
  loop invariant f == 0;

  loop invariant v == \at(p, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant t <= v;
  loop invariant t <= \at(p, Pre);

  loop invariant v == \at(p, Pre) && p == \at(p, Pre) && a == \at(a, Pre);
  loop invariant f == 0 && t <= \at(p, Pre);
  loop invariant t <= \at(p, Pre) && (t >= 0 || t == \at(p, Pre)) && p == \at(p, Pre) && a == \at(a, Pre);
  loop invariant p == \at(p, Pre) && a == \at(a, Pre);
  loop assigns f, t;
*/
while (t>=1) {
      f = f+f;
      t = t-1;
  }

}
