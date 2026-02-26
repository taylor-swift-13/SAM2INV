int main1(int n,int p){
  int a, e, v;

  a=(p%12)+6;
  e=0;
  v=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == (\at(p,Pre) % 12) + 6;
  loop invariant e == 0;

  loop invariant v >= -4;
  loop invariant n == \at(n,Pre);
  loop invariant p == \at(p,Pre);

  loop invariant v <= v*v + 7*v + 12;
  loop assigns v;
*/
while (e+1<=a) {
      v = v+3;
      v = v*v+v;
  }

}
