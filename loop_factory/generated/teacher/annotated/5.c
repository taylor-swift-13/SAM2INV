int main1(int a,int p){
  int o, e, s;

  o=a;
  e=0;
  s=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant o == \at(a, Pre);
  loop invariant s == \at(p, Pre) + e*(e-1)/2;

  loop invariant p == \at(p, Pre);
  loop invariant s == \at(p, Pre) + (e*(e-1))/2;
  loop invariant e >= 0;
  loop invariant (o < 0) || e <= o;
  loop invariant a == \at(a,Pre);
  loop invariant 0 <= e;

  loop assigns s, e;
*/
while (e<o) {
      s = s+e;
      e = e+1;
  }

}
