int main1(int b,int p){
  int e, c, v, m;

  e=b+3;
  c=e;
  v=0;
  m=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == b + 3;
  loop invariant c == e;
  loop invariant p == \at(p, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant v >= 0;
  loop invariant v > 0 ==> m + v == e + 1;
  loop invariant m <= e;
  loop invariant m + v <= e + 1;
  loop invariant (v == 0 ==> m == b) && (v >= 1 ==> m == e - v + 1);

  loop assigns m, v;
*/
while (c-4>=0) {
      m = e-v;
      v = v+1;
  }

}
